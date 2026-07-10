# Roadmap

This roadmap is organized around a verified formal spine first, then progressively replacing named theorem boundaries with real Mathlib-backed mathematics.

## Milestone 0: Repository Operating System

Deliverables:

- Lean/Lake project with Mathlib dependency.
- Local and GitHub CI.
- Codestyle and agent instructions.
- Main-loop profile, labels, issues, and wiki seed.

Acceptance:

- `scripts/lint_text` passes.
- `scripts/ci_local` runs wherever `lake` is installed.
- GitHub Actions runs build and lint on pushes and PRs.

## Milestone 1: Compile the RH Bridge

Deliverables:

- `theorem RH_of_Xi_real_zeros`
- `theorem RH_from_LaguerrePolya_Xi`
- No `sorry`, `admit`, or hidden axioms.

Acceptance:

- `lake build` succeeds.
- `lake lint RHLean` succeeds.
- The bridge targets Mathlib's `RiemannHypothesis`; later milestones keep hard steps named and discharge the zeta-to-`Xi` transfer.

## Milestone 2: Xi Functional Equation

Deliverables:

- Prove `xi (1 - s) = xi s` from Mathlib's `completedRiemannZeta₀_one_sub`.
- Document the exact relation between this `xi` definition and Mathlib's completed zeta definitions.

Acceptance:

- The theorem compiles without new assumptions.
- Any algebraic cancellation is isolated in short lemmas.

## Milestone 3: Zeta-Zero-to-Xi Transfer

Deliverables:

- Replace `ZetaZerosTransferToXi` as a bare hypothesis with a theorem proved from Mathlib definitions.
- Carefully handle exclusions at `s = 0`, `s = 1`, and trivial negative even zeros.

Acceptance:

- Nontrivial zeta zeros transfer to zeros of `Xi (-I * (s - 1 / 2))`.
- The bridge theorem no longer assumes the transfer as a project-level hypothesis.

Status: completed in [#20](https://github.com/alexlopashev/rh-lol/issues/20) after the completed-zeta transfer was discharged in [#19](https://github.com/alexlopashev/rh-lol/issues/19). `RH_of_Xi_real_zeros` now depends only on `AllZerosReal Xi`; the remaining unproved RH route work stays behind named Laguerre-Polya, Jensen, and total-positivity theorem boundaries.

## Milestone 4: Real Laguerre-Polya Boundary

Deliverables:

- Define the Laguerre-Polya class or a conservative Mathlib-compatible interface for it.
- Prove membership plus an explicit nonzero-target hypothesis implies all zeros are real.
- Keep `LaguerrePolyaZerosRealTheorem`, `LaguerrePolyaClass Xi`, and
  the proved `Xi_nonzero` fact visible at the `RH_from_LaguerrePolya_Xi`
  boundary until the real theorem is formalized.

Acceptance:

- The public RH wrapper derives `AllZerosReal Xi` from membership, the proved
  nonzero-`Xi` fact, and the named zero theorem rather than a packaged certificate.
- Any unformalized classical theorem is a single named theorem with a precise statement.
- The general zero-function exclusion remains visible in the named Laguerre-Polya
  theorem, while the `Xi` instance is supplied by `Xi_nonzero`.

## Milestone 5: Jensen Polynomial Route

Deliverables:

- Define Jensen polynomials for xi coefficients.
- Define polynomial hyperbolicity over the reals.
- State or prove the bridge from all Jensen hyperbolicity to Laguerre-Polya membership.

Acceptance:

- Definitions compile independently of the hardest analytic theorem.
- The dependency graph makes the missing research theorem visible.

Status: started in [#6](https://github.com/alexlopashev/rh-lol/issues/6) with a minimal `RHLean.Jensen.Polynomial` module and the named bridge `JensenHyperbolicityToLaguerrePolyaXi`.
[#31](https://github.com/alexlopashev/rh-lol/issues/31) adds the explicit
existential coefficient boundary `ExistsXiCoefficientSequenceWithJensenHyperbolicity`
and the RH wrapper theorem through that bridge.
The Jensen bridge supplies only `Nonempty (LaguerrePolyaClass Xi)`; the RH
wrappers still require the named `LaguerrePolyaZerosRealTheorem`, while
nonzero-`Xi` is supplied internally by `Xi_nonzero`.

## Milestone 6: Total Positivity Route

Deliverables:

- Define PF-infinity sequences and Toeplitz minors.
- Connect total positivity to Jensen hyperbolicity.
- Relate the formal route to xi coefficient objects.

Acceptance:

- The route is available as an explicit dependency edge into the Jensen branch.
- It does not duplicate Jensen definitions unless the math demands it.

Status: started in [#7](https://github.com/alexlopashev/rh-lol/issues/7) with a minimal `RHLean.TotalPositivity.PFSequence` module.
[#31](https://github.com/alexlopashev/rh-lol/issues/31) adds the explicit
existential coefficient boundary `ExistsXiCoefficientSequenceWithPFInfinity`.
[#37](https://github.com/alexlopashev/rh-lol/issues/37) adds the named
boundary `PFInfinityToJensenHyperbolicity`, making the PF-infinity to Jensen
hyperbolicity edge explicit.
[#39](https://github.com/alexlopashev/rh-lol/issues/39) routes the public
PF-infinity RH wrapper through that Jensen edge and the existing
Jensen-to-Laguerre-Polya membership bridge, with the Laguerre-Polya zero theorem
still explicit and nonzero-`Xi` supplied internally.

## Milestone 7: Completed-Zeta Transfer Cleanup

Goal:

- Discharge `CompletedZetaZerosTransferToXi` from Mathlib completed-zeta
  definitions and the local `Xi` normalization.
- Remove the completed-zeta transfer from public RH bridge signatures, so
  callers of `RH_of_Xi_real_zeros` provide only `AllZerosReal Xi`.

Implementation sequence:

- [#17](https://github.com/alexlopashev/rh-lol/issues/17): prove the inverse
  `Xi` critical-transform identity used to move between `s` and the real-line
  parameter.
- [#18](https://github.com/alexlopashev/rh-lol/issues/18): prove the local
  `xi` normalization by Mathlib's completed zeta away from the pole exclusions.
- [#19](https://github.com/alexlopashev/rh-lol/issues/19): prove
  `CompletedZetaZerosTransferToXi` from those algebraic and normalization
  facts.
- [#20](https://github.com/alexlopashev/rh-lol/issues/20): remove the
  completed-transfer hypothesis from public RH bridge APIs.

Boundary:

- This milestone removes an algebraic transfer hypothesis from the RH bridge.
- It does not prove RH, prove `AllZerosReal Xi`, or discharge the remaining
  Laguerre-Polya, Jensen-polynomial, or total-positivity research boundaries.

Status: completed through [#17](https://github.com/alexlopashev/rh-lol/issues/17), [#18](https://github.com/alexlopashev/rh-lol/issues/18), [#19](https://github.com/alexlopashev/rh-lol/issues/19), and [#20](https://github.com/alexlopashev/rh-lol/issues/20).
