/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import RHLean.ZetaXi
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Xi coefficient sequences

This file records the shared coefficient-sequence interface used by the Jensen
polynomial and total-positivity branches.
-/

noncomputable section

namespace RHLean

/-- A candidate exponential-generating coefficient sequence for `Xi`. -/
abbrev XiCoefficientSequence :=
  Nat → Complex

/--
The sequence `γ` is an exponential-generating coefficient sequence for `Xi` at
`0`.  This is the normalization used by Jensen polynomials: `γ n` is divided by
`n!` in the power series.
-/
def IsXiCoefficientSequence (γ : XiCoefficientSequence) : Prop :=
  ∀ z : Complex,
    HasSum (fun n : Nat => ((n.factorial : Complex)⁻¹ * γ n) * z ^ n) (Xi z)

/-- The canonical Jensen/Taylor coefficient sequence for `Xi` at `0`. -/
def XiTaylorCoefficientSequence : XiCoefficientSequence :=
  fun n : Nat => iteratedDeriv n Xi 0

/-- The canonical exponential-generating Taylor coefficients sum to `Xi`. -/
theorem isXiCoefficientSequence_XiTaylorCoefficientSequence :
    IsXiCoefficientSequence XiTaylorCoefficientSequence := by
  intro z
  simpa [XiTaylorCoefficientSequence, sub_zero, smul_eq_mul,
    mul_assoc, mul_left_comm, mul_comm] using
    (Complex.hasSum_taylorSeries_of_entire (f := Xi) differentiable_Xi 0 z)

end RHLean
