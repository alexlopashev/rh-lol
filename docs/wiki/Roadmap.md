# Roadmap

## Milestone 0: Repository Operating System

Lean/Lake project, Mathlib dependency, CI, codestyle, main-loop profile, labels, issues, and wiki seed.

## Milestone 1: Compile The RH Bridge

Formal target:

```lean
theorem RH_of_Xi_real_zeros
    (htransfer : ZetaZerosTransferToXi)
    (hXi : AllZerosReal Xi) :
    RiemannHypothesis
```

## Milestone 2: Xi Functional Equation

Prove `xi (1 - s) = xi s` from Mathlib's completed zeta functional equation.

## Milestone 3: Zeta-Zero-To-Xi Transfer

Replace the `ZetaZerosTransferToXi` hypothesis with a theorem.

## Milestone 4: Real Laguerre-Polya Certificate

Replace the temporary certificate wrapper with real definitions and a theorem proving real zeros.

## Milestone 5: Jensen Polynomial Route

Define Jensen polynomials and hyperbolicity for xi coefficients.

## Milestone 6: Total Positivity Route

Define PF-infinity sequences, Toeplitz minors, and total positivity bridges.
