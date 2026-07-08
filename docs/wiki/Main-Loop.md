Project profile:

```text
skills/project-profile/references/rh-lol.md
```

Suggested scheduled prompt:

```text
Use $project-main-loop.
Read project profile: skills/project-profile/references/rh-lol.md.
Run exactly one coordination loop.
```

Issue selection:

- Adopt open PRs before selecting new work.
- Prefer `status:ready`.
- Prefer `priority:p0`, then `priority:p1`, then `priority:p2`.
- Keep each issue PR-sized with testable acceptance criteria.

Validation:

- `scripts/lint_text`
- `scripts/ci_local`
- GitHub Actions CI

Issue links:

- [Open ready issues](https://github.com/alexlopashev/rh-lol/issues?q=is%3Aissue%20is%3Aopen%20label%3Astatus%3Aready)
- [Open PRs](https://github.com/alexlopashev/rh-lol/pulls)
- [Repository roadmap](https://github.com/alexlopashev/rh-lol/blob/main/docs/ROADMAP.md)
