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

/-- A candidate coefficient sequence for the power-series expansion of `Xi`. -/
abbrev XiCoefficientSequence :=
  Nat → Complex

/-- The sequence `γ` is a power-series coefficient sequence for `Xi` at `0`. -/
def IsXiCoefficientSequence (γ : XiCoefficientSequence) : Prop :=
  ∀ z : Complex, HasSum (fun n : Nat => γ n * z ^ n) (Xi z)

/-- The canonical Taylor coefficient sequence for `Xi` at `0`. -/
def XiTaylorCoefficientSequence : XiCoefficientSequence :=
  fun n : Nat => ((n.factorial : Complex)⁻¹) * iteratedDeriv n Xi 0

/-- The canonical Taylor coefficients sum to `Xi` on the whole complex plane. -/
theorem isXiCoefficientSequence_XiTaylorCoefficientSequence :
    IsXiCoefficientSequence XiTaylorCoefficientSequence := by
  intro z
  simpa [XiTaylorCoefficientSequence, sub_zero, smul_eq_mul,
    mul_assoc, mul_left_comm, mul_comm] using
    (Complex.hasSum_taylorSeries_of_entire (f := Xi) differentiable_Xi 0 z)

end RHLean
