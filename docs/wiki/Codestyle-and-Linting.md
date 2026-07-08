Hard rules:

- No `sorry`.
- No `admit`.
- No `axiom`.
- No `unsafe`.
- No broad imports left behind after exploration.

Local checks:

```bash
scripts/lint_text
scripts/ci_local
```

Lean style:

- Keep `autoImplicit = false`.
- Use Mathlib's RH and zeta names directly.
- Put hard analysis behind named hypotheses or theorems.
- Prefer small lemmas to large proof blocks.
- Shrink imports before finishing a change.

Repository reference:

- [docs/CODESTYLE.md](https://github.com/alexlopashev/rh-lol/blob/main/docs/CODESTYLE.md)
