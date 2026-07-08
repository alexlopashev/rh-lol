# Agent Instructions

This repository formalizes a Riemann hypothesis strategy scaffold in Lean 4 and Mathlib. The near-term goal is a verified dependency graph, not a claimed RH proof.

## Project Invariant

Every mathematically hard step must be isolated behind a named theorem, definition, or hypothesis. Do not hide missing analysis in notation, broad rewrites, opaque automation, or informal prose.

The initial spine is:

```text
Laguerre-Polya certificate for Xi
  -> all zeros of Xi are real
  -> all nontrivial zeta zeros lie on the critical line
  -> Mathlib.RiemannHypothesis
```

## Required Local Check

Run this before opening a PR:

```bash
scripts/ci_local
```

If Lean is not installed locally, record that explicitly in the PR or handoff and rely on GitHub Actions as the verification gate.

## Lean Style

- Use Lean 4 with Mathlib through `lakefile.toml`.
- Keep `autoImplicit = false`.
- Keep imports specific. Use `import Mathlib` only while investigating a missing declaration, then shrink imports before finishing.
- No `sorry`, `admit`, `axiom`, or `unsafe` in committed Lean source.
- Prefer small named lemmas over large tactic blocks.
- Place analytic gaps behind explicit `Prop` hypotheses or theorem statements.
- Do not define a parallel RH statement unless the file also proves how it relates to Mathlib's `RiemannHypothesis`.

## Repository Structure

- `RHLean/ZetaXi.lean`: `xi`, `Xi`, and completed-zeta definitions.
- `RHLean/CriticalLine.lean`: zero predicates, critical-line predicates, coordinate algebra.
- `RHLean/RHBridge.lean`: bridge from `AllZerosReal Xi` to `RiemannHypothesis`.
- `RHLean/LaguerrePolya/`: certificate interface and later Laguerre-Polya class work.
- `docs/`: roadmap, codestyle, and wiki source pages.
- `scripts/`: local CI and publication helpers.

## Main Loop Expectations

Use the project profile at:

```text
/Users/sasha/Documents/agentic-skills/skills/project-profile/references/rh-lol.md
```

For automation runs, prefer GitHub issues labeled `status:ready`, then highest priority. Keep issues PR-sized and state acceptance criteria that can be checked by Lean, CI, or a precise documentation diff.
