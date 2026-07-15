# Codebase Structure

The repository is intentionally small at the start. Avoid creating a broad formalization tree before the bridge compiles.

```text
RHLean/
  ZetaXi.lean
  CriticalLine.lean
  RHBridge.lean
  XiCoefficients.lean
  Jensen/
    Polynomial.lean
  LaguerrePolya/
    Certificate.lean
  TotalPositivity/
    PFSequence.lean
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

`RHLean/XiCoefficients.lean` owns both coefficient conventions: the raw
exponential-generating Taylor sequence for `Xi`, the sign-correct centered-even
sequence for `xi`, their proved series identities, and the exact reconstruction
map between them.

`RHLean/Jensen/Polynomial.lean` owns the Jensen polynomial route: Jensen polynomials, real hyperbolicity, the explicit normalized approximants, their locally uniform convergence proof, and the theorem from Jensen hyperbolicity to Laguerre-Polya membership for `Xi`.

`RHLean/LaguerrePolya/Certificate.lean` owns the Laguerre-Polya class interface, the named pointwise/off-real locally-uniform zero-preservation boundaries, the public compatibility boundary that feeds the theorem from nonzero class membership to real zeros, and the proved `Xi_nonzero` fact used by the public RH wrappers.

`RHLean/TotalPositivity/PFSequence.lean` owns the minimal total-positivity route:
PF-infinity conditions and Toeplitz minor determinants for the sign-correct
centered-even sequence, plus the named finite boundary connecting those minors
to Jensen hyperbolicity for the reconstructed raw `Xi` sequence.

## Later Modules

Add these only when the relevant milestone starts:

```text
RHLean/LaguerrePolya/
  Basic.lean
  RealZeros.lean

RHLean/TotalPositivity/
  ToeplitzMinors.lean
  KernelTotalPositivity.lean
```

Each later directory should come with one small compiling bridge before adding many definitions.
