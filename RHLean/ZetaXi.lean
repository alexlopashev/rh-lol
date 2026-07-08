/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Ring

/-!
# The completed zeta and critical-line transform

This file defines the Riemann xi function through Mathlib's
`completedRiemannZeta₀`, and the critical-line transform
`Xi z = xi (1 / 2 + I * z)`.
-/

noncomputable section

namespace RHLean

open Complex

/-- The Riemann xi function, expressed using Mathlib's entire `completedRiemannZeta₀`.

Mathlib has `completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)`.
Multiplying by `s * (s - 1)` cancels the polar correction terms and yields the usual
normalization `1 / 2 * (s * (s - 1) * completedRiemannZeta₀ s + 1)`.
-/
def xi (s : Complex) : Complex :=
  (1 / 2 : Complex) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

/-- The real-line model of xi on the critical line.

Zeros of `Xi` with real input correspond to zeros of `xi` on `re s = 1 / 2`.
-/
def Xi (z : Complex) : Complex :=
  xi ((1 / 2 : Complex) + Complex.I * z)

/-- The polynomial factor in `xi` is invariant under `s ↦ 1 - s`. -/
lemma xi_prefactor_one_sub (s : Complex) :
    (1 - s) * ((1 - s) - 1) = s * (s - 1) := by
  ring

/-- The Riemann xi function satisfies the functional equation `xi (1 - s) = xi s`. -/
theorem xi_one_sub (s : Complex) :
    xi (1 - s) = xi s := by
  rw [xi, xi, completedRiemannZeta₀_one_sub, xi_prefactor_one_sub]

end RHLean
