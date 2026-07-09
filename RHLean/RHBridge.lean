/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import RHLean.CriticalLine
import Mathlib.Tactic.NormNum

/-!
# Bridge from real zeros of Xi to Mathlib's Riemann hypothesis

The zeta-to-Xi transfer is split into elementary exclusions and the discharged
named completed-zeta transfer theorem.  Real-rootedness of `Xi` then implies
Mathlib's `RiemannHypothesis`.
-/

noncomputable section

namespace RHLean

open Complex

/-- Remaining analytic/algebraic transfer from completed zeta zeros to `Xi` zeros.

The hypotheses expose the exceptional points of the completed zeta expression:
`s = 0`, `s = 1`, and the Gamma-factor zeros, which are exactly the negative
even trivial-zero candidates handled below.
-/
def CompletedZetaZerosTransferToXi : Prop :=
  ∀ s : Complex,
    s ≠ 0 →
      s ≠ 1 →
        Gammaℝ s ≠ 0 →
          completedRiemannZeta s = 0 →
            Xi (-Complex.I * (s - (1 / 2 : Complex))) = 0

/-- Completed-zeta zeros away from the exposed exceptional factors transfer to `Xi` zeros. -/
theorem completedZetaZerosTransferToXi : CompletedZetaZerosTransferToXi := by
  intro s hs0 hs1 _hGamma hzero
  calc
    Xi (-Complex.I * (s - (1 / 2 : Complex))) = xi s := Xi_neg_I_mul_sub_half s
    _ = 0 := xi_eq_zero_of_completedRiemannZeta_eq_zero hs0 hs1 hzero

/-- A zeta zero cannot occur at `s = 0`, since Mathlib proves `ζ 0 = -1 / 2`. -/
lemma zeta_zero_ne_zero {s : Complex} (hz : riemannZeta s = 0) : s ≠ 0 := by
  intro hs
  have hzero : riemannZeta (0 : Complex) = 0 := by
    simpa [hs] using hz
  have hnonzero : (-1 / 2 : Complex) ≠ 0 := by norm_num
  rw [riemannZeta_zero] at hzero
  exact hnonzero hzero

/-- Excluding `s = 0` and the negative even trivial zeros makes the Gamma factor nonzero. -/
lemma GammaR_ne_zero_of_ne_zero_of_not_trivial {s : Complex}
    (hs0 : s ≠ 0) (htriv : ¬ IsTrivialZero s) :
    Gammaℝ s ≠ 0 := by
  intro hGamma
  rw [Gammaℝ_eq_zero_iff] at hGamma
  rcases hGamma with ⟨n, hn⟩
  cases n with
  | zero =>
      exact hs0 (by simpa using hn)
  | succ n =>
      apply htriv
      refine ⟨n, ?_⟩
      rw [hn, Nat.cast_succ]
      ring

/-- A zeta zero away from the Gamma-factor exceptions is a completed-zeta zero. -/
lemma completedRiemannZeta_eq_zero_of_zeta_eq_zero {s : Complex}
    (hz : riemannZeta s = 0) (hs0 : s ≠ 0) (hGamma : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = 0 := by
  have hdef := riemannZeta_def_of_ne_zero hs0
  have hquot : completedRiemannZeta s / Gammaℝ s = 0 := by
    simpa [hz] using hdef.symm
  exact (div_eq_zero_iff.mp hquot).resolve_right hGamma

/-- Nontrivial zeta zeros transfer to `Xi` zeros. -/
theorem ZetaZerosTransferToXi :
    ∀ s : Complex,
      NontrivialZetaZero s →
      Xi (-Complex.I * (s - (1 / 2 : Complex))) = 0 := by
  intro s hs
  rcases hs with ⟨hz, hnottriv, hs1⟩
  have hs0 : s ≠ 0 := zeta_zero_ne_zero hz
  have hGamma : Gammaℝ s ≠ 0 := GammaR_ne_zero_of_ne_zero_of_not_trivial hs0 hnottriv
  exact completedZetaZerosTransferToXi s hs0 hs1 hGamma
    (completedRiemannZeta_eq_zero_of_zeta_eq_zero hz hs0 hGamma)

/-- Mathlib's RH statement follows from locating every nontrivial zeta zero on the critical line. -/
theorem RH_of_nontrivial_zero_location
    (h : ∀ s : Complex, NontrivialZetaZero s → OnCriticalLine s) :
    RiemannHypothesis := by
  intro s hz hnottriv hs1
  exact h s ⟨hz, by simpa [IsTrivialZero] using hnottriv, hs1⟩

/-- If every `Xi` zero is real, then RH follows from the zeta-to-Xi transfer theorem. -/
theorem RH_of_Xi_real_zeros
    (hXi : AllZerosReal Xi) :
    RiemannHypothesis := by
  apply RH_of_nontrivial_zero_location
  intro s hs
  apply onCriticalLine_of_aux_real
  exact hXi _ (ZetaZerosTransferToXi s hs)

end RHLean
