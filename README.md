# rh-lol

Lean 4 and Mathlib scaffold for formalizing a dependency graph around the Riemann hypothesis.

The project is not claiming a proof of RH. The immediate goal is narrower and more useful: make the proof architecture explicit enough that Lean checks every easy bridge and every hard bridge has a name.

```text
Xi has only real zeros
  -> all nontrivial zeta zeros lie on the critical line
  -> Mathlib.RiemannHypothesis
```

The longer route is:

```text
existence of Xi coefficients with PF-infinity
  -> Jensen hyperbolicity for Xi coefficients
  -> Laguerre-Polya membership for Xi
  -> proved nonzero Xi plus the named Laguerre-Polya zero theorem
  -> Xi has only real zeros
  -> Mathlib.RiemannHypothesis
```

## Status

Initial formal spine:

- `RHLean.ZetaXi`: defines `xi` and `Xi`.
- `RHLean.CriticalLine`: defines zeta-zero predicates and the critical-line coordinate lemma.
- `RHLean.RHBridge`: proves the zeta-to-`Xi` transfer from completed zeta definitions, then proves `RH_of_Xi_real_zeros` from the real-zero hypothesis.
- `RHLean.XiCoefficients`: defines the shared `Xi` coefficient sequence interface.
- `RHLean.Jensen.Polynomial`: defines the minimal Jensen polynomial route, including its existential coefficient boundary and named bridge to Laguerre-Polya membership for `Xi`.
- `RHLean.LaguerrePolya.Certificate`: defines the Laguerre-Polya class interface, the nonzero-target predicate, proves `Xi_nonzero`, and records the named locally-uniform zero-preservation boundary used to turn nonzero membership into real zeros.
- `RHLean.TotalPositivity.PFSequence`: defines the minimal PF-infinity / Toeplitz-minor route, including its existential coefficient boundary and named bridge to Jensen hyperbolicity.

## Setup

Install Lean through `elan`, then run:

```bash
lake exe cache get
scripts/ci_local
```

The project follows Mathlib's current downstream setup: `lakefile.toml` requires `mathlib`, and `lean-toolchain` is pinned to Mathlib's current toolchain.

## Roadmap

See [docs/ROADMAP.md](docs/ROADMAP.md).

## Codestyle

See [docs/CODESTYLE.md](docs/CODESTYLE.md). The short version: no `sorry`, no `admit`, no `axiom`, no `unsafe`, strict imports, and named hypotheses for unfinished mathematical bridges.
