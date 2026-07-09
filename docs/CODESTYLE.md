# Codestyle And Linting

## Hard Rules

- No `sorry`.
- No `admit`.
- No `axiom`.
- No `unsafe`.
- No new RH-like proposition without a theorem relating it to Mathlib's `RiemannHypothesis`.
- No broad imports left behind after exploration.

## Lean Conventions

- Use two-space indentation.
- Keep `autoImplicit = false`.
- Prefer short definitions and named lemmas.
- Use `noncomputable section` for analytic files.
- Keep theorem statements mathematically precise even when their proof is postponed through a named hypothesis.
- Use Mathlib names directly for zeta and RH objects.

## Naming

- Predicate names should read as mathematical facts: `AllZerosReal`, `OnCriticalLine`.
- Bridge theorem names should expose direction: `RH_of_Xi_real_zeros`.
- Placeholder theorem or hypothesis names should name the missing bridge exactly, such as `LaguerrePolyaZerosRealTheorem`.

## Imports

Start with the narrowest import that likely works. Temporary `import Mathlib` is acceptable while discovering names, but shrink it before the change is done.

## Required Checks

```bash
scripts/lint_text
scripts/ci_local
```

`scripts/lint_text` is intentionally dependency-light and should run even before Lean is installed. `scripts/ci_local` requires `lake`.
