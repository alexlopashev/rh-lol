/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import RHLean.ZetaXi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Critical-line predicates and coordinate algebra

This file contains the elementary coordinate calculation that converts a real
zero of `Xi` back into a zeta zero on the critical line.
-/

noncomputable section

namespace RHLean

open Complex

/-- The negative even integers, i.e. the trivial zeros of `riemannZeta`. -/
def IsTrivialZero (s : Complex) : Prop :=
  ∃ n : Nat, s = -2 * (n + 1)

/-- A zeta zero with the pole and trivial zeros excluded. -/
def NontrivialZetaZero (s : Complex) : Prop :=
  riemannZeta s = 0 ∧ ¬ IsTrivialZero s ∧ s ≠ 1

/-- The critical line `re s = 1 / 2`. -/
def OnCriticalLine (s : Complex) : Prop :=
  s.re = (1 : Real) / 2

/-- Every zero of a complex-valued function occurs at a real argument. -/
def AllZerosReal (F : Complex → Complex) : Prop :=
  ∀ z : Complex, F z = 0 → z.im = 0

/-- Imaginary coordinate of the inverse critical-line transform. -/
lemma criticalTransform_im (s : Complex) :
    (-Complex.I * (s - (1 / 2 : Complex))).im = (1 : Real) / 2 - s.re := by
  simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

/-- If the `Xi` coordinate of `s` is real, then `s` lies on the critical line. -/
lemma onCriticalLine_of_aux_real {s : Complex}
    (h : (-Complex.I * (s - (1 / 2 : Complex))).im = 0) :
    OnCriticalLine s := by
  rw [criticalTransform_im] at h
  dsimp [OnCriticalLine]
  linarith

end RHLean
