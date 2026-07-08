## Milestone 0: Repository Operating System

Lean/Lake project, Mathlib dependency, CI, codestyle, main-loop profile, labels, issues, and wiki seed.

Status: done through [#1](https://github.com/alexlopashev/rh-lol/issues/1) and repository docs.

## Milestone 1: Compile The RH Bridge

Formal target:

```lean
theorem RH_of_Xi_real_zeros
    (hcompleted : CompletedZetaZerosTransferToXi)
    (hXi : AllZerosReal Xi) :
    RiemannHypothesis
```

Status: done in [#2](https://github.com/alexlopashev/rh-lol/issues/2). The theorem targets Mathlib's `RiemannHypothesis`.

## Milestone 2: Xi Functional Equation

Prove `xi (1 - s) = xi s` from Mathlib's completed zeta functional equation.

Status: done in [#3](https://github.com/alexlopashev/rh-lol/issues/3).

## Milestone 3: Zeta-Zero-To-Xi Transfer

Keep the transfer explicit. The current scaffold proves `ZetaZerosTransferToXi` from the remaining named hypothesis `CompletedZetaZerosTransferToXi`.

Status: refined in [#4](https://github.com/alexlopashev/rh-lol/issues/4). The completed-zeta-to-`Xi` analytic bridge is still intentionally named, not hidden.

## Milestone 4: Real Laguerre-Polya Certificate

Replace the temporary certificate wrapper with real definitions and a theorem proving real zeros.

Tracking issue: [#5](https://github.com/alexlopashev/rh-lol/issues/5).

## Milestone 5: Jensen Polynomial Route

Define Jensen polynomials and hyperbolicity for xi coefficients.

Tracking issue: [#6](https://github.com/alexlopashev/rh-lol/issues/6).

## Milestone 6: Total Positivity Route

Define PF-infinity sequences, Toeplitz minors, and total positivity bridges.

Tracking issue: [#7](https://github.com/alexlopashev/rh-lol/issues/7).

Repository references:

- [Full roadmap](https://github.com/alexlopashev/rh-lol/blob/main/docs/ROADMAP.md)
- [Codebase structure](https://github.com/alexlopashev/rh-lol/blob/main/docs/STRUCTURE.md)
- [Open ready issues](https://github.com/alexlopashev/rh-lol/issues?q=is%3Aissue%20is%3Aopen%20label%3Astatus%3Aready)
