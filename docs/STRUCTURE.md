# Codebase Structure

The repository is intentionally small at the start. Avoid creating a broad formalization tree before the bridge compiles.

```text
RHLean/
  ZetaXi.lean
  CriticalLine.lean
  RHBridge.lean
  Jensen/
    Polynomial.lean
  LaguerrePolya/
    Certificate.lean
docs/
  CODESTYLE.md
  ROADMAP.md
  STRUCTURE.md
  wiki/
scripts/
  ci_local
  lint_text
  publish_wiki
```

## Near-Term Lean Modules

`RHLean/ZetaXi.lean` owns definitions of `xi` and `Xi`.

`RHLean/CriticalLine.lean` owns coordinate and zero-location predicates.

`RHLean/RHBridge.lean` owns the theorem turning real zeros of `Xi` into Mathlib's `RiemannHypothesis`.

`RHLean/Jensen/Polynomial.lean` owns the minimal Jensen polynomial route: xi coefficient sequences, Jensen polynomials, real hyperbolicity, and the named bridge to a Laguerre-Polya certificate for `Xi`.

`RHLean/LaguerrePolya/Certificate.lean` owns the Laguerre-Polya class interface and the named theorem boundary from class membership to real zeros.

## Later Modules

Add these only when the relevant milestone starts:

```text
RHLean/LaguerrePolya/
  Basic.lean
  RealZeros.lean

RHLean/TotalPositivity/
  PFSequence.lean
  ToeplitzMinors.lean
  KernelTotalPositivity.lean
```

Each later directory should come with one small compiling bridge before adding many definitions.
