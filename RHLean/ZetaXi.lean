/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.FieldSimp
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

/-- The repo's `xi` normalization is an entire complex function. -/
theorem differentiable_xi : Differentiable Complex xi := by
  have h_id : Differentiable Complex (fun s : Complex => s) := differentiable_id
  have h_const_one : Differentiable Complex (fun _s : Complex => (1 : Complex)) :=
    differentiable_const (c := (1 : Complex))
  have h_const_half : Differentiable Complex (fun _s : Complex => (1 / 2 : Complex)) :=
    differentiable_const (c := (1 / 2 : Complex))
  have h_sub_one : Differentiable Complex (fun s : Complex => s - 1) :=
    h_id.sub h_const_one
  have h_prefactor : Differentiable Complex (fun s : Complex => s * (s - 1)) :=
    h_id.mul h_sub_one
  have h_product :
      Differentiable Complex (fun s : Complex => s * (s - 1) * completedRiemannZeta₀ s) :=
    h_prefactor.mul differentiable_completedZeta₀
  have h_sum :
      Differentiable Complex (fun s : Complex => s * (s - 1) * completedRiemannZeta₀ s + 1) :=
    h_product.add h_const_one
  change Differentiable Complex
    (fun s : Complex => (1 / 2 : Complex) * (s * (s - 1) * completedRiemannZeta₀ s + 1))
  simpa [one_div] using h_sum.const_mul (1 / 2 : Complex)

/-- Multiplying by `s * (s - 1)` cancels the two pole-correction terms in
Mathlib's `completedRiemannZeta_eq` formula. -/
lemma completedRiemannZeta_pole_correction_factor
    {s : Complex} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s * (s - 1) * (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s))
      = s * (s - 1) * completedRiemannZeta₀ s + 1 := by
  have h1s : (1 : Complex) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp [hs0, h1s]
  ring

/-- Away from `s = 0, 1`, this repo's `xi` is the standard polynomial
normalization of Mathlib's completed Riemann zeta function. -/
theorem xi_eq_half_mul_completedRiemannZeta
    {s : Complex} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi s = (1 / 2 : Complex) * (s * (s - 1) * completedRiemannZeta s) := by
  rw [xi, completedRiemannZeta_eq,
    completedRiemannZeta_pole_correction_factor hs0 hs1]

/-- A completed-zeta zero away from `s = 0, 1` is a zero of `xi`. -/
theorem xi_eq_zero_of_completedRiemannZeta_eq_zero
    {s : Complex} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzero : completedRiemannZeta s = 0) :
    xi s = 0 := by
  rw [xi_eq_half_mul_completedRiemannZeta hs0 hs1, hzero]
  ring

/-- The real-line model of xi on the critical line.

Zeros of `Xi` with real input correspond to zeros of `xi` on `re s = 1 / 2`.
-/
def Xi (z : Complex) : Complex :=
  xi ((1 / 2 : Complex) + Complex.I * z)

/-- The critical-line transform `Xi` is an entire complex function. -/
theorem differentiable_Xi : Differentiable Complex Xi := by
  have h_const_half : Differentiable Complex (fun _z : Complex => (1 / 2 : Complex)) :=
    differentiable_const (c := (1 / 2 : Complex))
  have h_I_mul : Differentiable Complex (fun z : Complex => Complex.I * z) :=
    differentiable_id.const_mul Complex.I
  have h_line :
      Differentiable Complex (fun z : Complex => (1 / 2 : Complex) + Complex.I * z) :=
    h_const_half.add h_I_mul
  change Differentiable Complex (fun z : Complex => xi ((1 / 2 : Complex) + Complex.I * z))
  simpa [one_div] using differentiable_xi.fun_comp h_line

/-- The inverse critical-line transform recovers the original xi input. -/
theorem Xi_neg_I_mul_sub_half (s : Complex) :
    Xi (-Complex.I * (s - (1 / 2 : Complex))) = xi s := by
  rw [Xi]
  congr 1
  calc
    (1 / 2 : Complex) + Complex.I * (-Complex.I * (s - (1 / 2 : Complex)))
        = (1 / 2 : Complex) + (s - (1 / 2 : Complex)) := by
      rw [← mul_assoc]
      simp [Complex.I_mul_I]
    _ = s := by
      ring

/-- The polynomial factor in `xi` is invariant under `s ↦ 1 - s`. -/
lemma xi_prefactor_one_sub (s : Complex) :
    (1 - s) * ((1 - s) - 1) = s * (s - 1) := by
  ring

/-- The Riemann xi function satisfies the functional equation `xi (1 - s) = xi s`. -/
theorem xi_one_sub (s : Complex) :
    xi (1 - s) = xi s := by
  rw [xi, xi, completedRiemannZeta₀_one_sub, xi_prefactor_one_sub]

end RHLean
