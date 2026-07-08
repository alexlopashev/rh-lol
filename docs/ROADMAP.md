# Roadmap

This roadmap is organized around a verified formal spine first, then progressively replacing thin certificates with real Mathlib-backed mathematics.

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
- The only remaining RH assumptions are named hypotheses such as `ZetaZerosTransferToXi`.

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

## Milestone 4: Real Laguerre-Polya Certificate

Deliverables:

- Define the Laguerre-Polya class or a conservative Mathlib-compatible interface for it.
- Prove membership implies all zeros are real.
- Replace the temporary `LaguerrePolyaCertificate.zeros_real` field.

Acceptance:

- The certificate is no longer just a wrapper around `AllZerosReal`.
- Any unformalized classical theorem is a single named theorem with a precise statement.

## Milestone 5: Jensen Polynomial Route

Deliverables:

- Define Jensen polynomials for xi coefficients.
- Define polynomial hyperbolicity over the reals.
- State or prove the bridge from all Jensen hyperbolicity to Laguerre-Polya membership.

Acceptance:

- Definitions compile independently of the hardest analytic theorem.
- The dependency graph makes the missing research theorem visible.

Status: started in [#6](https://github.com/alexlopashev/rh-lol/issues/6) with a minimal `RHLean.Jensen.Polynomial` module and the named bridge `JensenHyperbolicityToLaguerrePolyaXi`.

## Milestone 6: Total Positivity Route

Deliverables:

- Define PF-infinity sequences and Toeplitz minors.
- Connect total positivity to a Laguerre-Polya certificate.
- Relate the formal route to xi coefficient objects.

Acceptance:

- The route is available as an alternative dependency branch.
- It does not duplicate Jensen definitions unless the math demands it.

Status: started in [#7](https://github.com/alexlopashev/rh-lol/issues/7) with a minimal `RHLean.TotalPositivity.PFSequence` module and the named bridge `TotalPositivityToLaguerrePolyaXi`.
