/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import RHLean.ZetaXi
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Xi coefficient sequences

This file records the shared coefficient-sequence interface used by the Jensen
polynomial and total-positivity branches.
-/

noncomputable section

namespace RHLean

open scoped BigOperators

/-- A candidate coefficient sequence for the power-series expansion of `Xi`. -/
abbrev XiCoefficientSequence :=
  Nat → Complex

/-- The Jensen polynomial formula attached to a coefficient sequence.

This definition lives with the coefficient interface so the coefficient
certificate can state local-uniform convergence of the same approximants used by
the Jensen route without creating an import cycle.
-/
def XiCoefficientJensenPolynomial (γ : XiCoefficientSequence) (n d : Nat) : Polynomial Complex :=
  Finset.sum (Finset.range (d + 1)) fun j =>
    Polynomial.C (((Nat.choose d j : Nat) : Complex) * γ (n + j)) * Polynomial.X ^ j

/--
The sequence `γ` is a usable Xi coefficient sequence for the Jensen route.

Besides the pointwise power-series identity, the certificate records the exact
analytic data needed to turn hyperbolic Jensen approximants into
Laguerre-Polya membership for `Xi`.  The concrete construction of such a
certificate remains separate from the generic Jensen-to-Laguerre-Polya bridge.
-/
structure IsXiCoefficientSequence (γ : XiCoefficientSequence) : Prop where
  /-- `γ` is a power-series coefficient sequence for `Xi` at `0`. -/
  hasSum_xi : ∀ z : Complex, HasSum (fun n : Nat => γ n * z ^ n) (Xi z)
  /-- `Xi` is entire in the coefficient certificate used by the Jensen route. -/
  xi_entire : AnalyticOnNhd Complex Xi Set.univ
  /-- `Xi` takes real values on real inputs. -/
  xi_real_on_real : ∀ x : Real, (Xi (x : Complex)).im = 0
  /--
  The degree-`d` Jensen approximants based at `0` converge locally uniformly to
  `Xi`.  This is the analytic normalization used by the Laguerre-Polya
  certificate.
  -/
  jensen_locally_uniform_limit :
    TendstoLocallyUniformlyOn
      (fun (d : Nat) (z : Complex) => (XiCoefficientJensenPolynomial γ 0 d).eval z)
      Xi Filter.atTop Set.univ

/-- The canonical Taylor coefficient sequence for `Xi` at `0`. -/
def XiTaylorCoefficientSequence : XiCoefficientSequence :=
  fun n : Nat => ((n.factorial : Complex)⁻¹) * iteratedDeriv n Xi 0

/-- The canonical Taylor coefficients sum to `Xi` on the whole complex plane. -/
theorem hasSum_XiTaylorCoefficientSequence :
    ∀ z : Complex,
      HasSum (fun n : Nat => XiTaylorCoefficientSequence n * z ^ n) (Xi z) := by
  intro z
  simpa [XiTaylorCoefficientSequence, sub_zero, smul_eq_mul,
    mul_assoc, mul_left_comm, mul_comm] using
    (Complex.hasSum_taylorSeries_of_entire (f := Xi) differentiable_Xi 0 z)

end RHLean
