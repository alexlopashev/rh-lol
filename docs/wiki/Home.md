`rh-lol` is a Lean 4 and Mathlib project for formalizing a dependency graph around a possible Riemann hypothesis strategy.

The project goal is not to announce a proof. The goal is to make each bridge precise:

```text
Xi has only real zeros
  -> all nontrivial zeta zeros lie on the critical line
  -> Mathlib.RiemannHypothesis
```

Useful pages:

- [Roadmap](Roadmap)
- [Formalization Spine](Formalization-Spine)
- [Codestyle And Linting](Codestyle-and-Linting)
- [Main Loop](Main-Loop)

Repository docs:

- [README](https://github.com/alexlopashev/rh-lol/blob/main/README.md)
- [Roadmap](https://github.com/alexlopashev/rh-lol/blob/main/docs/ROADMAP.md)
- [Codebase Structure](https://github.com/alexlopashev/rh-lol/blob/main/docs/STRUCTURE.md)
- [Codestyle](https://github.com/alexlopashev/rh-lol/blob/main/docs/CODESTYLE.md)

Core Lean source:

- `RHLean/ZetaXi.lean`
- `RHLean/CriticalLine.lean`
- `RHLean/RHBridge.lean`
- `RHLean/LaguerrePolya/Certificate.lean`
