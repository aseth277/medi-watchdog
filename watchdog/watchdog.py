"""Off-host watchdog: turns a healthchecks.io webhook into a GitHub issue.

Flow (Telemetry TT8, dev design 4.7): healthchecks.io notices a missed ping
(`medi-outage` or `medi-c5`) and POSTs a `repository_dispatch` to the
`medi-watchdog` repo. That repo's workflow runs this script, which opens,
comments on, or closes an issue in the TARGET repo (Medi's private repo).

Design rules this file keeps:
  * Standard library only (Python 3.10+). It runs in another repo's Actions
    runner with no `pip install`, so the backend's pydantic-settings and
    structlog rules do not apply; `main(argv, env)` takes the environment as a
    mapping and only the `__main__` guard touches `os.environ`. Logging is the
    stdlib `logging`, configured in `main` only.
  * The payload is read from the file named by `GITHUB_EVENT_PATH` and
    validated here. Nothing from the payload is ever used to build a command
    or a URL path; `kind` and `status` are checked against allow-lists.
  * The issues token (`WATCHDOG_ISSUES_TOKEN`) is never logged, never put in
    an exception message and never echoed, including on error paths.

Exit codes: 0 handled (a no-op `up` counts), 2 invalid payload/config (no HTTP
call made), 1 GitHub API failure, or the issue was filed but something the
owner configured did not take (an assignee invalid, dropped or refused, or
an assignee who is the issues token's owner and so is never notified), or the
new issue came back without its label. A non-zero
exit makes Actions email the actor that triggered the run, which is the
watchdog's own failure channel.
"""

from __future__ import annotations

import http.client
import json
import logging
import os
import re
import string
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Mapping, Sequence

log = logging.getLogger("watchdog")

# Principle 10: a fixed offset, no zoneinfo (the runner may lack tzdata).
IST = timezone(timedelta(hours=5, minutes=30))

_DAYS = ("Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun")
_MONTHS = (
    "Jan", "Feb", "Mar", "Apr", "May", "Jun",
    "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
)

RUNBOOKS_PATH = Path(__file__).with_name("runbooks.json")

VALID_STATUSES = ("down", "up")
DEFAULT_API_URL = "https://api.github.com"
DEFAULT_RUNBOOK_REF = "main"
HTTP_TIMEOUT_S = 10
# K6: GitHub hiccups (5xx, 429, a secondary-rate-limit 403, a network error)
# are retried a bounded number of times; healthchecks.io is assumed to send
# each webhook once, so a single blip must not lose the alert. One call's worst
# case is 3 attempts x 10 s timeout + at most 2 x 30 s of waiting = 90 s. A run
# chains several calls (GET /user, the open and closed listings, the create
# with its re-lists, one comment and close per issue), so a badly degraded
# GitHub can take longer than the job's 5-minute `timeout-minutes`. The job is
# then cancelled, which fails the run and emails the actor like any other
# failure; "Re-run failed jobs" replays it (README, Exit codes).
MAX_ATTEMPTS = 3
BACKOFF_S = (2.0, 5.0)
RETRY_AFTER_CAP_S = 30
_RETRYABLE_STATUSES = frozenset({429, 500, 502, 503, 504})
PAGE_SIZE = 100
MAX_PAGES = 10
RECENTLY_CLOSED_PAGE = 20  # K8: how many recently updated closed issues to check
# X2: a `down` counts as stale only if the watchdog closed an issue of its kind
# at most this long after the `down` was detected. A close much later than that
# may be a delayed `up` run closing an OLDER outage after a genuine new one.
STALE_DOWN_WINDOW = timedelta(minutes=10)
_REPO_RE = re.compile(r"^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$")
# A GitHub login: alphanumerics and single inner hyphens, at most 39 chars.
_LOGIN_RE = re.compile(r"^[A-Za-z0-9](?:[A-Za-z0-9]|-(?=[A-Za-z0-9])){0,38}$")

EXIT_OK = 0
EXIT_API_FAILURE = 1
EXIT_INVALID = 2


class InvalidPayload(ValueError):
    """The dispatch event or the environment is not something to act on."""


class GitHubError(RuntimeError):
    """A GitHub API call failed. The message never carries a header."""

    def __init__(
        self,
        message: str,
        status: int | None = None,
        *,
        retryable: bool = False,
        retry_after_s: float | None = None,
    ) -> None:
        super().__init__(message)
        self.status = status
        self.retryable = retryable
        self.retry_after_s = retry_after_s

    def delay_s(self, attempt: int) -> float:
        """How long to wait before attempt `attempt + 1` (1-based `attempt`)."""
        if self.retry_after_s is not None:
            return min(self.retry_after_s, float(RETRY_AFTER_CAP_S))
        return BACKOFF_S[min(attempt, len(BACKOFF_S)) - 1]


def _sleep(seconds: float) -> None:
    """Indirection so tests can record the back-off instead of waiting."""
    time.sleep(seconds)


def _retry_after(headers: Any) -> float | None:
    raw = headers.get("Retry-After") if headers is not None else None
    try:
        value = float(raw) if raw is not None else None
    except (TypeError, ValueError):
        return None  # an HTTP-date form falls back to the fixed back-off
    return value if value is not None and value >= 0 else None


def marker_for(kind: str) -> str:
    return f"<!-- watchdog:{kind} -->"


def format_ist(moment: datetime) -> str:
    """`Fri 19 Sep, 03:22 IST` (English names, no locale dependence)."""
    local = moment.astimezone(IST)
    return (
        f"{_DAYS[local.weekday()]} {local.day} {_MONTHS[local.month - 1]}, "
        f"{local:%H:%M} IST"
    )


def format_duration(span: timedelta) -> str:
    """`45 min`, `2 h 15 min`, `1 d 2 h` (whole minutes, rounded down)."""
    minutes = max(int(span.total_seconds() // 60), 0)
    days, rest = divmod(minutes, 24 * 60)
    hours, mins = divmod(rest, 60)
    if days:
        return f"{days} d {hours} h"
    if hours:
        return f"{hours} h {mins} min"
    return f"{mins} min"


def load_runbooks(path: Path = RUNBOOKS_PATH) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


# ---------------------------------------------------------------- dispatch

@dataclass(frozen=True)
class Dispatch:
    kind: str
    status: str
    now: datetime
    now_from_payload: bool


def _parse_now(raw: Any) -> datetime | None:
    if not isinstance(raw, str) or not raw.strip():
        return None
    text = raw.strip()
    if text.endswith(("Z", "z")):
        text = text[:-1] + "+00:00"
    try:
        parsed = datetime.fromisoformat(text)
    except ValueError:
        return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed


def parse_event(
    event: Any,
    runbooks: Mapping[str, Any] | None = None,
    run_time: datetime | None = None,
) -> Dispatch:
    """Validate a `repository_dispatch` event; raise `InvalidPayload`."""
    runbooks = runbooks if runbooks is not None else load_runbooks()
    if not isinstance(event, dict):
        raise InvalidPayload("event is not a JSON object")
    if event.get("action") != "watchdog":
        raise InvalidPayload("action is not 'watchdog'")
    payload = event.get("client_payload")
    if not isinstance(payload, dict):
        raise InvalidPayload("client_payload is missing")
    kind = payload.get("kind")
    if not isinstance(kind, str) or kind not in runbooks["alerts"]:
        raise InvalidPayload("client_payload.kind is not a known alert")
    status = payload.get("status")
    if status not in VALID_STATUSES:
        raise InvalidPayload("client_payload.status is not 'down' or 'up'")
    parsed = _parse_now(payload.get("now"))
    if parsed is not None:
        return Dispatch(kind, status, parsed, True)
    fallback = run_time if run_time is not None else datetime.now(timezone.utc)
    return Dispatch(kind, status, fallback, False)


# ---------------------------------------------------------------- config

@dataclass(frozen=True)
class Config:
    token: str = field(repr=False)
    repo: str
    api_url: str
    runbook_ref: str
    runbooks: Mapping[str, Any]
    # K2: who gets notified. GitHub never notifies the token owner of its own
    # activity, so these must be people other than the issues token's owner.
    assignees: tuple[str, ...] = ()
    invalid_assignees: tuple[str, ...] = ()

    def runbook_url(self, filename: str) -> str:
        return (
            f"https://github.com/{self.repo}/blob/{self.runbook_ref}/"
            f"{self.runbooks['runbook_dir']}/{filename}"
        )


def config_from_env(env: Mapping[str, str], runbooks: Mapping[str, Any]) -> Config:
    token = env.get("WATCHDOG_ISSUES_TOKEN", "").strip()
    if not token:
        raise InvalidPayload("WATCHDOG_ISSUES_TOKEN is not set")
    repo = env.get("WATCHDOG_TARGET_REPO", "").strip()
    if not repo:
        raise InvalidPayload("WATCHDOG_TARGET_REPO is not set")
    if not _REPO_RE.match(repo):
        raise InvalidPayload("WATCHDOG_TARGET_REPO is not 'owner/name'")
    logins = [part.strip() for part in env.get("WATCHDOG_ASSIGNEES", "").split(",")]
    logins = [login for login in logins if login]
    return Config(
        token=token,
        repo=repo,
        api_url=(env.get("GITHUB_API_URL", "").strip() or DEFAULT_API_URL).rstrip("/"),
        runbook_ref=env.get("WATCHDOG_RUNBOOK_REF", "").strip() or DEFAULT_RUNBOOK_REF,
        runbooks=runbooks,
        assignees=tuple(login for login in logins if _LOGIN_RE.match(login)),
        invalid_assignees=tuple(login for login in logins if not _LOGIN_RE.match(login)),
    )


# ---------------------------------------------------------------- rendering

_NOTE_RUN_TIME = " (time of the workflow run)"

# C1 - `medi-outage`. One text, SEV1.
_C1_TITLE = string.Template("Wello · backend not responding")
_C1_BODY = string.Template(
    """\
$marker
**SEV1 — the backend is not responding**

The `medi-outage` check stopped getting its ping. Reported at $when.

This check cannot tell the host, the gateway and `telemetry_worker` apart: it goes quiet if the host is off or asleep, if the gateway is not `ready`, or if `telemetry_worker` has stopped draining. The runbook starts by finding out which.

Runbook: $runbook_url

$see_also
Closes itself when the check recovers. A human-opened issue is never touched.
"""
)

# C5 - `medi-c5`. Its own text, SEV2.
_C5_TITLE = string.Template(
    "Wello · a worker, queue or traffic floor has gone quiet"
)
_C5_BODY = string.Template(
    """\
$marker
**SEV2 — a worker, queue or traffic floor has gone quiet**

The `medi-c5` check stopped getting its ping. Reported at $when.

`telemetry_worker` sends this ping only while the gateway answers `c5` as `ok`. So it goes quiet when one of the "quiet" signals below trips, and also when the host, the gateway or `telemetry_worker` itself is down.

**If a `medi-outage` issue is open too, this is an outage, not a quiet signal.** Work [backend not responding]($outage_runbook_url) first; this issue closes by itself once the backend recovers.

Otherwise the actual reason is in the token-gated detail body, under `c5.reasons` (the runbook has the command). Each reason code maps to a runbook:

| Reason code | Runbook |
|---|---|
$reason_rows

Runbook: $runbook_url

$see_also
Closes itself when the check recovers. A human-opened issue is never touched.
"""
)

TEMPLATES: dict[str, tuple[string.Template, string.Template]] = {
    "outage": (_C1_TITLE, _C1_BODY),
    "worker-stale": (_C5_TITLE, _C5_BODY),
}


def _label_for(filename: str) -> str:
    return filename.removesuffix(".md").replace("-", " ")


def _when(now: datetime, now_from_payload: bool) -> str:
    return format_ist(now) + ("" if now_from_payload else _NOTE_RUN_TIME)


def render_issue(
    kind: str,
    now: datetime,
    cfg: Config,
    now_from_payload: bool = True,
) -> tuple[str, str]:
    title_tpl, body_tpl = TEMPLATES[kind]
    alert = cfg.runbooks["alerts"][kind]
    see_also = "\n".join(
        f"- Also see: [{_label_for(name)}]({cfg.runbook_url(name)})"
        for name in alert["see_also"]
    )
    rows = "\n".join(
        f"| `{code}` | [{_label_for(name)}]({cfg.runbook_url(name)}) |"
        for code, name in cfg.runbooks["c5_reasons"].items()
    )
    values = {
        "marker": marker_for(kind),
        "when": _when(now, now_from_payload),
        "runbook_url": cfg.runbook_url(alert["runbook"]),
        "see_also": see_also + "\n" if see_also else "",
        "reason_rows": rows,
        "outage_runbook_url": cfg.runbook_url(cfg.runbooks["alerts"]["outage"]["runbook"]),
    }
    return title_tpl.substitute(values), body_tpl.substitute(values)


# ---------------------------------------------------------------- GitHub

class GitHubClient:
    def __init__(self, cfg: Config, timeout: float = HTTP_TIMEOUT_S) -> None:
        self._root = cfg.api_url
        self._base = f"{cfg.api_url}/repos/{cfg.repo}"
        self._token = cfg.token
        self._timeout = timeout

    def _request(
        self,
        method: str,
        path: str,
        query: Mapping[str, Any] | None = None,
        body: Mapping[str, Any] | None = None,
        *,
        retry: bool = True,
        root: bool = False,
    ) -> Any:
        """One API call, retried on a transient failure unless `retry=False`
        (the create path does its own retry — see `_create`). `path` is under
        the target repo, or under the API root when `root=True`."""
        attempts = MAX_ATTEMPTS if retry else 1
        for attempt in range(1, attempts + 1):
            try:
                return self._request_once(method, path, query, body, root)
            except GitHubError as exc:
                if not exc.retryable or attempt == attempts:
                    raise
                delay = exc.delay_s(attempt)
                log.warning(
                    "github_retry method=%s path=%s attempt=%d wait_s=%.0f", method, path, attempt, delay
                )
                _sleep(delay)
        raise AssertionError("unreachable")  # pragma: no cover

    def _request_once(
        self,
        method: str,
        path: str,
        query: Mapping[str, Any] | None,
        body: Mapping[str, Any] | None,
        root: bool = False,
    ) -> Any:
        url = (self._root if root else self._base) + path
        if query:
            url += "?" + urllib.parse.urlencode(query)
        data = json.dumps(body).encode("utf-8") if body is not None else None
        request = urllib.request.Request(url, data=data, method=method)
        request.add_header("Authorization", f"Bearer {self._token}")
        request.add_header("Accept", "application/vnd.github+json")
        request.add_header("X-GitHub-Api-Version", "2022-11-28")
        request.add_header("User-Agent", "medi-watchdog")
        if data is not None:
            request.add_header("Content-Type", "application/json")
        try:
            with urllib.request.urlopen(request, timeout=self._timeout) as response:
                raw = response.read()
        except urllib.error.HTTPError as exc:
            retry_after = _retry_after(exc.headers)
            retryable = exc.code in _RETRYABLE_STATUSES or (
                exc.code == 403 and retry_after is not None  # secondary rate limit
            )
            raise GitHubError(
                f"{method} {path} -> HTTP {exc.code}",
                exc.code,
                retryable=retryable,
                retry_after_s=retry_after,
            ) from None
        except (urllib.error.URLError, TimeoutError, OSError, http.client.HTTPException) as exc:
            # HTTPException covers a body cut short mid-read (IncompleteRead).
            raise GitHubError(
                f"{method} {path} failed: {type(exc).__name__}", retryable=True
            ) from None
        if not raw:
            return None
        try:
            return json.loads(raw)
        except ValueError:
            # Y1: a 2xx that is not JSON (a proxy or captive-portal HTML page)
            # must reach callers as a GitHubError like any other failure, so
            # their handling (retry, fail open, warn) applies; never the body.
            raise GitHubError(
                f"{method} {path} answered a body that is not JSON", retryable=True
            ) from None

    def list_open_issues(self, label: str) -> list[dict[str, Any]]:
        items: list[dict[str, Any]] = []
        for page in range(1, MAX_PAGES + 1):
            chunk = self._request(
                "GET",
                "/issues",
                query={
                    "state": "open",
                    "labels": label,
                    "per_page": PAGE_SIZE,
                    "page": page,
                },
            )
            chunk = chunk if isinstance(chunk, list) else []
            items.extend(chunk)
            if len(chunk) < PAGE_SIZE:
                break
        return items

    def token_owner(self) -> str | None:
        """The login the issues token belongs to (`GET /user`). One attempt
        only: it is advisory and runs after the alert (Y2)."""
        user = self._request("GET", "/user", root=True, retry=False)
        login = user.get("login") if isinstance(user, dict) else None
        return login if isinstance(login, str) else None

    def list_recently_closed(self, label: str) -> list[dict[str, Any]]:
        chunk = self._request(
            "GET",
            "/issues",
            query={
                "state": "closed",
                "labels": label,
                "sort": "updated",
                "direction": "desc",
                "per_page": RECENTLY_CLOSED_PAGE,
            },
        )
        return chunk if isinstance(chunk, list) else []

    def create_issue(
        self,
        title: str,
        body: str,
        labels: Sequence[str],
        assignees: Sequence[str] = (),
    ) -> Any:
        payload: dict[str, Any] = {"title": title, "body": body, "labels": list(labels)}
        if assignees:
            payload["assignees"] = list(assignees)
        return self._request("POST", "/issues", body=payload, retry=False)

    def comment(self, number: int, body: str) -> Any:
        return self._request("POST", f"/issues/{int(number)}/comments", body={"body": body})

    def close(self, number: int) -> Any:
        return self._request(
            "PATCH",
            f"/issues/{int(number)}",
            body={"state": "closed", "state_reason": "completed"},
        )


def _marker_issues(client: GitHubClient, kind: str) -> list[dict[str, Any]]:
    """Open issues labelled `kind` that carry the exact marker (D-M8-4).

    Pull requests are skipped; an issue whose label a human removed is no
    longer listed, so it has been taken over and is never touched.
    """
    marker = marker_for(kind)
    return [
        item
        for item in client.list_open_issues(kind)
        if "pull_request" not in item and marker in (item.get("body") or "")
    ]


def _names(items: Any, key: str) -> set[str]:
    if not isinstance(items, list):
        return set()
    return {i.get(key) for i in items if isinstance(i, dict)}


def _check_label(created: Any, kind: str, problems: list[str]) -> None:
    """K7: every later run finds the issue by its label, so a new issue
    without it can never be de-duplicated or closed by the watchdog."""
    labels = _names(created.get("labels") if isinstance(created, dict) else None, "name")
    if kind not in labels:
        number = created.get("number") if isinstance(created, dict) else None
        log.error("label_not_applied kind=%s issue=%s (add the label by hand)", kind, number)
        problems.append("label_not_applied")


_LANDED = object()  # sentinel: a failed create had in fact created the issue


def _create(
    client: GitHubClient, kind: str, title: str, body: str, assignees: Sequence[str]
) -> Any:
    """Create, retrying a transient failure while avoiding a duplicate.

    A POST that timed out or answered 5xx may still have created the issue, so
    before each retry the open marker issues are listed again; if one now
    exists, the earlier attempt landed and nothing more is sent. This narrows
    the window but cannot close it: a create that GitHub commits only after
    the re-list has read can still end up filed twice. Later runs then
    comment on (or close) both, since both carry the marker.
    """
    for attempt in range(1, MAX_ATTEMPTS + 1):
        try:
            return client.create_issue(title, body, [kind], assignees)
        except GitHubError as exc:
            if not exc.retryable or attempt == MAX_ATTEMPTS:
                raise
            delay = exc.delay_s(attempt)
            log.warning("github_retry method=POST path=/issues attempt=%d wait_s=%.0f", attempt, delay)
            _sleep(delay)
            if _marker_issues(client, kind):
                log.warning("create_landed_despite_error kind=%s", kind)
                return _LANDED
    raise AssertionError("unreachable")  # pragma: no cover


def _open_issue(
    client: GitHubClient, cfg: Config, kind: str, title: str, body: str, problems: list[str]
) -> Any:
    """Create the issue; never let an assignee problem stop it being filed."""
    try:
        created = _create(client, kind, title, body, cfg.assignees)
    except GitHubError as exc:
        if exc.status != 422 or not cfg.assignees:
            raise
        log.error("issue_opened_without_assignees kind=%s status=422", kind)
        problems.append("assignees_rejected")
        created = _create(client, kind, title, body, ())
        if created is not _LANDED:
            _check_label(created, kind, problems)
        return created
    if created is _LANDED:
        return created  # found again by its label, so the label is there
    _check_label(created, kind, problems)
    applied = _names(created.get("assignees") if isinstance(created, dict) else None, "login")
    for login in cfg.assignees:
        if login not in applied:
            log.error("assignee_not_applied kind=%s login=%s", kind, login)
            problems.append("assignee_not_applied")
    return created


def _within_stale_window(closed_at: datetime, moment: datetime) -> bool:
    """0 < closed_at - moment <= STALE_DOWN_WINDOW."""
    return timedelta(0) < closed_at - moment <= STALE_DOWN_WINDOW


def _stale_because_of(client: GitHubClient, kind: str, moment: datetime) -> int | None:
    """K8/X2: the number of a watchdog issue of `kind` whose close makes this
    `down` (detected at `moment`) a late delivery, or None.

    healthchecks.io sends `down` and `up` as separate webhooks, and a `down`
    can reach GitHub after the `up` that followed it; the `up` run then closes
    the issue shortly after the `down` was detected. Only a close inside
    STALE_DOWN_WINDOW counts. A later close is logged and ignored, because a
    delayed `up` run can close an older outage after a genuine new `down` was
    sent, and suppressing that would lose a real alert.

    C4: fails open. If the closed issues cannot be listed, the `down` is acted
    on — a false alarm is cheaper than a lost one.
    """
    marker = marker_for(kind)
    try:
        items = client.list_recently_closed(kind)
    except GitHubError as exc:
        log.warning("stale_check_unavailable kind=%s: %s (acting on the down)", kind, exc)
        return None
    for item in items:
        if "pull_request" in item or marker not in (item.get("body") or ""):
            continue
        closed_at = _parse_now(item.get("closed_at"))
        if closed_at is None or closed_at <= moment:
            continue
        if _within_stale_window(closed_at, moment):
            return item.get("number")
        log.warning(
            "stale_down_window_exceeded kind=%s closed_issue=%s closed_after_s=%.0f (acting on the down)",
            kind, item.get("number"), (closed_at - moment).total_seconds(),
        )
    return None


def _check_notification_path(cfg: Config, client: GitHubClient, problems: list[str]) -> None:
    """C2: GitHub never notifies an account of its own activity, so an issue
    reaches a person only through an assignee who is NOT the issues token's
    owner. Never blocks the issue: a failed lookup only warns."""
    if not cfg.assignees:
        log.warning(
            "no_assignees: WATCHDOG_ASSIGNEES is empty; nobody is assigned, and the "
            "issues token's owner is not notified of issues it opens"
        )
        return
    try:
        owner = client.token_owner()
    except GitHubError as exc:
        log.warning("token_owner_unknown: %s (assignees not checked)", exc)
        return
    if owner is None:
        log.warning("token_owner_unknown: GET /user returned no login (assignees not checked)")
        return
    for login in cfg.assignees:
        if login.lower() == owner.lower():
            log.error(
                "assignee_is_token_owner login=%s: GitHub does not notify an account of "
                "its own activity; assign someone else or use a machine-user token",
                login,
            )
            problems.append("assignee_is_token_owner")


def _still_down_comment(item: Mapping[str, Any], dispatch: Dispatch, when: str) -> str:
    """C3: say how long the issue has been open, so an issue left open by a
    lost `up` (see README, Known limits) is visibly old."""
    text = f"Still not recovered: the check reported another failure at {when}."
    opened = _parse_now(item.get("created_at"))
    if opened is not None and opened <= dispatch.now:
        text += (
            f" This issue has been open for {format_duration(dispatch.now - opened)}"
            f" (since {format_ist(opened)})."
        )
    return text


def handle(dispatch: Dispatch, cfg: Config, client: GitHubClient) -> list[str]:
    """Act on one dispatch. Returns problems that did not stop the issue.

    Y2: the primary action (open, comment or close) runs first; the
    notification-path check (`GET /user`) runs only after it, so a slow or
    failing lookup can never delay or block the alert.
    """
    problems: list[str] = []
    for login in cfg.invalid_assignees:
        log.error("invalid_assignee login=%r (not a GitHub login; skipped)", login)
        problems.append("invalid_assignee")
    _act(dispatch, cfg, client, problems)
    _check_notification_path(cfg, client, problems)
    return problems


def _act(dispatch: Dispatch, cfg: Config, client: GitHubClient, problems: list[str]) -> None:
    kind = dispatch.kind
    when = _when(dispatch.now, dispatch.now_from_payload)
    existing = _marker_issues(client, kind)
    if dispatch.status == "down":
        if existing:
            for item in existing:
                client.comment(item["number"], _still_down_comment(item, dispatch, when))
            log.info("commented_on_open_issue kind=%s", kind)
            return
        if dispatch.now_from_payload:
            newer = _stale_because_of(client, kind, dispatch.now)
            if newer is not None:
                log.info("stale_down_ignored kind=%s closed_issue=%s", kind, newer)
                return
        title, body = render_issue(kind, dispatch.now, cfg, dispatch.now_from_payload)
        _open_issue(client, cfg, kind, title, body, problems)
        log.info("opened_issue kind=%s", kind)
        return
    for item in existing:
        client.comment(
            item["number"],
            f"Recovered at {when}: the check is passing again. Closing this issue.",
        )
        client.close(item["number"])
    log.info("closed_issues kind=%s count=%d", kind, len(existing))


# ---------------------------------------------------------------- entrypoint

def main(argv: Sequence[str] | None = None, env: Mapping[str, str] | None = None) -> int:
    del argv  # no CLI arguments; everything arrives through the environment
    env = env if env is not None else {}
    logging.basicConfig(
        level=logging.INFO, stream=sys.stderr, format="%(levelname)s %(name)s %(message)s"
    )
    try:
        runbooks = load_runbooks()
        cfg = config_from_env(env, runbooks)
        event_path = env.get("GITHUB_EVENT_PATH", "").strip()
        if not event_path:
            raise InvalidPayload("GITHUB_EVENT_PATH is not set")
        try:
            event = json.loads(Path(event_path).read_text(encoding="utf-8"))
        except (OSError, ValueError):
            raise InvalidPayload("event file is unreadable or not JSON") from None
        dispatch = parse_event(event, runbooks)
    except InvalidPayload as exc:
        log.error("invalid_input: %s", exc)
        return EXIT_INVALID
    try:
        problems = handle(dispatch, cfg, GitHubClient(cfg))
    except GitHubError as exc:
        log.error("github_api_failure: %s", exc)
        return EXIT_API_FAILURE
    return EXIT_API_FAILURE if problems else EXIT_OK


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:], os.environ))
