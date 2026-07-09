## Milestone 0: Repository Operating System

Lean/Lake project, Mathlib dependency, CI, codestyle, main-loop profile, labels, issues, and wiki seed.

Status: done through [#1](https://github.com/alexlopashev/rh-lol/issues/1) and repository docs.

## Milestone 1: Compile The RH Bridge

Formal target:

```lean
theorem RH_of_Xi_real_zeros
    (hXi : AllZerosReal Xi) :
    RiemannHypothesis
```

Status: updated through [#20](https://github.com/alexlopashev/rh-lol/issues/20). The theorem targets Mathlib's `RiemannHypothesis` and no longer takes the completed-zeta transfer as an external argument.

## Milestone 2: Xi Functional Equation

Prove `xi (1 - s) = xi s` from Mathlib's completed zeta functional equation.

Status: done in [#3](https://github.com/alexlopashev/rh-lol/issues/3).

## Milestone 3: Zeta-Zero-To-Xi Transfer

Keep the transfer explicit and checked. The scaffold now proves `completedZetaZerosTransferToXi`, then uses it inside `ZetaZerosTransferToXi` so public RH bridge callers do not provide a completed-zeta transfer hypothesis.

Status: completed through [#19](https://github.com/alexlopashev/rh-lol/issues/19) and [#20](https://github.com/alexlopashev/rh-lol/issues/20). This discharges the completed-zeta-to-`Xi` transfer; it does not claim RH, because the route to `AllZerosReal Xi` is still represented by named Laguerre-Polya, Jensen, and total-positivity theorem boundaries.

## Milestone 4: Real Laguerre-Polya Certificate

Replace the temporary certificate wrapper with real definitions and a theorem proving real zeros.

Tracking issue: [#5](https://github.com/alexlopashev/rh-lol/issues/5).

## Milestone 5: Jensen Polynomial Route

Define Jensen polynomials and hyperbolicity for xi coefficients.

Tracking issue: [#6](https://github.com/alexlopashev/rh-lol/issues/6).

## Milestone 6: Total Positivity Route

Define PF-infinity sequences, Toeplitz minors, and total positivity bridges.

Status: started in [#7](https://github.com/alexlopashev/rh-lol/issues/7) with a minimal `RHLean.TotalPositivity.PFSequence` module and the named bridge `TotalPositivityToLaguerrePolyaXi`.

Repository references:

- [Full roadmap](https://github.com/alexlopashev/rh-lol/blob/main/docs/ROADMAP.md)
- [Codebase structure](https://github.com/alexlopashev/rh-lol/blob/main/docs/STRUCTURE.md)
- [Open ready issues](https://github.com/alexlopashev/rh-lol/issues?q=is%3Aissue%20is%3Aopen%20label%3Astatus%3Aready)
