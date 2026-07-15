/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import RHLean.ZetaXi
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Xi coefficient sequences

This file distinguishes two coefficient normalizations:

* `XiCoefficientSequence` is the raw exponential-generating sequence for `Xi`;
  its canonical witness consists of all Taylor derivatives of `Xi` at `0`.
* `XiEvenCoefficientSequence` is the sign-correct sequence in the centered-even
  expansion of `xi`; its canonical witness has normalization
  `n! / (2n)! * xi^(2n)(1 / 2)`.

The total-positivity branch uses only the second normalization.  The explicit
map `xiCoefficientSequenceOfEven` reconstructs the first normalization, with
zero odd entries and alternating even entries, for the existing Jensen and
Laguerre-Polya route.
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

/-- A sign-correct coefficient sequence for the centered even expansion of `xi`. -/
def XiEvenCoefficientSequence :=
  Nat → Complex

/--
The sequence `γ` represents the centered even expansion
`xi (1 / 2 + z) = ∑ γ n / n! * z^(2n)`.
-/
def IsXiEvenCoefficientSequence (γ : XiEvenCoefficientSequence) : Prop :=
  ∀ z : Complex,
    HasSum
      (fun n : Nat => ((n.factorial : Complex)⁻¹ * γ n) * z ^ (2 * n))
      (xi ((1 / 2 : Complex) + z))

/--
The canonical sign-correct even coefficients of `xi` at `1 / 2`, normalized so
that the `n`th coefficient is divided by `n!` in the centered even series.
-/
def XiEvenTaylorCoefficientSequence : XiEvenCoefficientSequence :=
  fun n : Nat =>
    ((n.factorial : Complex) * (((2 * n).factorial : Complex)⁻¹)) *
      iteratedDeriv (2 * n) xi (1 / 2 : Complex)

/-- The canonical even coefficient has the standard `n! / (2n)!` normalization. -/
theorem XiEvenTaylorCoefficientSequence_apply (n : Nat) :
    XiEvenTaylorCoefficientSequence n =
      ((n.factorial : Complex) / ((2 * n).factorial : Complex)) *
        iteratedDeriv (2 * n) xi (1 / 2 : Complex) := by
  simp [XiEvenTaylorCoefficientSequence, div_eq_mul_inv]

/--
Reconstruct a raw exponential-generating `Xi` sequence from sign-correct even
coefficients.  Even entries acquire the factor
`(-1)^n * (2n)! / n!`; odd entries are zero.
-/
def xiCoefficientSequenceOfEven
    (γ : XiEvenCoefficientSequence) : XiCoefficientSequence :=
  fun m : Nat =>
    if Even m then
      (((-1 : Complex) ^ (m / 2) * (m.factorial : Complex)) *
        (((m / 2).factorial : Complex)⁻¹)) * γ (m / 2)
    else
      0

/-- The reconstructed raw sequence has the required alternating even entries. -/
@[simp]
theorem xiCoefficientSequenceOfEven_even
    (γ : XiEvenCoefficientSequence) (n : Nat) :
    xiCoefficientSequenceOfEven γ (2 * n) =
      (((-1 : Complex) ^ n * (((2 * n).factorial : Complex))) *
        ((n.factorial : Complex)⁻¹) * γ n) := by
  simp [xiCoefficientSequenceOfEven]

/-- The reconstructed raw sequence has zero odd entries. -/
@[simp]
theorem xiCoefficientSequenceOfEven_odd
    (γ : XiEvenCoefficientSequence) (n : Nat) :
    xiCoefficientSequenceOfEven γ (2 * n + 1) = 0 := by
  simp [xiCoefficientSequenceOfEven]

/-- The functional equation makes `xi` even around `1 / 2`. -/
theorem xi_half_sub_eq_half_add (z : Complex) :
    xi ((1 / 2 : Complex) - z) = xi ((1 / 2 : Complex) + z) := by
  calc
    xi ((1 / 2 : Complex) - z) = xi (1 - ((1 / 2 : Complex) + z)) := by
      congr 1
      ring
    _ = xi ((1 / 2 : Complex) + z) := xi_one_sub _

/-- Every odd Taylor derivative of `xi` at `1 / 2` vanishes. -/
theorem iteratedDeriv_xi_half_odd (n : Nat) :
    iteratedDeriv (2 * n + 1) xi (1 / 2 : Complex) = 0 := by
  have hfunctions :
      (fun z : Complex => xi ((1 / 2 : Complex) - z)) =
        fun z : Complex => xi ((1 / 2 : Complex) + z) := by
    funext z
    exact xi_half_sub_eq_half_add z
  have hderiv := congrArg
    (fun f : Complex → Complex => iteratedDeriv (2 * n + 1) f 0)
    hfunctions
  have hneg :
      -iteratedDeriv (2 * n + 1) xi (1 / 2 : Complex) =
        iteratedDeriv (2 * n + 1) xi (1 / 2 : Complex) := by
    simpa [iteratedDeriv_comp_const_sub, iteratedDeriv_comp_const_add,
      pow_add, pow_mul] using hderiv
  exact CharZero.neg_eq_self_iff.mp hneg

/-- Iterated derivatives of `Xi` are the centered derivatives of `xi`, scaled by `I^n`. -/
theorem XiTaylorCoefficientSequence_eq_I_pow_mul_xi_deriv (n : Nat) :
    XiTaylorCoefficientSequence n =
      Complex.I ^ n * iteratedDeriv n xi (1 / 2 : Complex) := by
  have hcentered : Differentiable Complex
      (fun z : Complex => xi ((1 / 2 : Complex) + z)) := by
    have hline : Differentiable Complex
        (fun z : Complex => (1 / 2 : Complex) + z) :=
      (differentiable_const (c := (1 / 2 : Complex))).add differentiable_id
    exact differentiable_xi.fun_comp hline
  have hcomp := congrFun
    (iteratedDeriv_comp_const_mul (n := n) hcentered.contDiff Complex.I)
    0
  rw [XiTaylorCoefficientSequence]
  change iteratedDeriv n
      (fun z : Complex => xi ((1 / 2 : Complex) + Complex.I * z)) 0 = _
  simpa [iteratedDeriv_comp_const_add] using hcomp

/-- Odd entries of the raw canonical `Xi` Taylor sequence vanish. -/
theorem XiTaylorCoefficientSequence_odd (n : Nat) :
    XiTaylorCoefficientSequence (2 * n + 1) = 0 := by
  rw [XiTaylorCoefficientSequence_eq_I_pow_mul_xi_deriv]
  rw [iteratedDeriv_xi_half_odd]
  simp

/--
Even raw `Xi` Taylor entries are the sign-alternating, factorial-rescaled
canonical centered-even coefficients.
-/
theorem XiTaylorCoefficientSequence_even (n : Nat) :
    XiTaylorCoefficientSequence (2 * n) =
      (((-1 : Complex) ^ n * (((2 * n).factorial : Complex))) *
        ((n.factorial : Complex)⁻¹) * XiEvenTaylorCoefficientSequence n) := by
  rw [XiTaylorCoefficientSequence_eq_I_pow_mul_xi_deriv]
  simp only [pow_mul, Complex.I_sq]
  rw [XiEvenTaylorCoefficientSequence_apply]
  have hn : (n.factorial : Complex) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have htwo_n : ((2 * n).factorial : Complex) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * n))
  field_simp [hn, htwo_n]

/-- The canonical centered-even sequence reconstructs the canonical raw `Xi` sequence. -/
theorem xiCoefficientSequenceOfEven_XiEvenTaylorCoefficientSequence :
    xiCoefficientSequenceOfEven XiEvenTaylorCoefficientSequence =
      XiTaylorCoefficientSequence := by
  funext m
  rcases Nat.even_or_odd' m with ⟨n, rfl | rfl⟩
  · simpa only [xiCoefficientSequenceOfEven_even] using
      (XiTaylorCoefficientSequence_even n).symm
  · simp [XiTaylorCoefficientSequence_odd]

/-- The canonical sign-correct even coefficients give the centered even Taylor series of `xi`. -/
theorem isXiEvenCoefficientSequence_XiEvenTaylorCoefficientSequence :
    IsXiEvenCoefficientSequence XiEvenTaylorCoefficientSequence := by
  intro z
  let term : Nat → Complex := fun m : Nat =>
    ((m.factorial : Complex)⁻¹ * z ^ m) *
      iteratedDeriv m xi (1 / 2 : Complex)
  have hTaylor :
      HasSum term (xi ((1 / 2 : Complex) + z)) := by
    simpa [term, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      (Complex.hasSum_taylorSeries_of_entire
        (f := xi) differentiable_xi (1 / 2 : Complex) ((1 / 2 : Complex) + z))
  have hEvenSummable : Summable fun n : Nat => term (2 * n) :=
    hTaylor.summable.comp_injective
      (mul_right_injective₀ (two_ne_zero' Nat))
  have hOdd : HasSum (fun n : Nat => term (2 * n + 1)) 0 := by
    refine HasSum.congr_fun
      (hasSum_zero : HasSum (fun _ : Nat => (0 : Complex)) 0) ?_
    intro n
    dsimp [term]
    rw [iteratedDeriv_xi_half_odd]
    simp
  have hSplit := HasSum.even_add_odd hEvenSummable.hasSum hOdd
  have hEvenTsum :
      ∑' n : Nat, term (2 * n) = xi ((1 / 2 : Complex) + z) := by
    simpa using hSplit.unique hTaylor
  have hEven : HasSum (fun n : Nat => term (2 * n))
      (xi ((1 / 2 : Complex) + z)) := by
    rw [← hEvenTsum]
    exact hEvenSummable.hasSum
  refine HasSum.congr_fun hEven ?_
  intro n
  dsimp [term]
  rw [XiEvenTaylorCoefficientSequence_apply]
  have hn : (n.factorial : Complex) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have htwo_n : ((2 * n).factorial : Complex) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * n))
  field_simp [hn, htwo_n]

/-- Any centered-even coefficient identity gives the corresponding sign-alternating `Xi` series. -/
theorem IsXiEvenCoefficientSequence.hasSum_Xi
    {γ : XiEvenCoefficientSequence}
    (hγ : IsXiEvenCoefficientSequence γ)
    (z : Complex) :
    HasSum
      (fun n : Nat =>
        (((n.factorial : Complex)⁻¹ * γ n) * (-1 : Complex) ^ n) *
          z ^ (2 * n))
      (Xi z) := by
  have hIpow (n : Nat) :
      (Complex.I * z) ^ (2 * n) = (-1 : Complex) ^ n * z ^ (2 * n) := by
    calc
      (Complex.I * z) ^ (2 * n) =
          Complex.I ^ (2 * n) * z ^ (2 * n) := by rw [mul_pow]
      _ = (Complex.I ^ 2) ^ n * z ^ (2 * n) := by rw [pow_mul]
      _ = (-1 : Complex) ^ n * z ^ (2 * n) := by rw [Complex.I_sq]
  simpa only [Xi] using HasSum.congr_fun (hγ (Complex.I * z)) (fun n => by
    rw [hIpow]
    ring)

/-- The canonical centered-even coefficients give the sign-alternating series for `Xi`. -/
theorem hasSum_Xi_XiEvenTaylorCoefficientSequence (z : Complex) :
    HasSum
      (fun n : Nat =>
        (((n.factorial : Complex)⁻¹ * XiEvenTaylorCoefficientSequence n) *
          (-1 : Complex) ^ n) * z ^ (2 * n))
      (Xi z) :=
  isXiEvenCoefficientSequence_XiEvenTaylorCoefficientSequence.hasSum_Xi z

/--
The explicit zero/interlacing reconstruction turns a centered-even coefficient
identity into the existing raw exponential-generating coefficient identity for
`Xi`.
-/
theorem isXiCoefficientSequence_xiCoefficientSequenceOfEven
    {γ : XiEvenCoefficientSequence}
    (hγ : IsXiEvenCoefficientSequence γ) :
    IsXiCoefficientSequence (xiCoefficientSequenceOfEven γ) := by
  intro z
  let rawTerm : Nat → Complex := fun m : Nat =>
    ((m.factorial : Complex)⁻¹ * xiCoefficientSequenceOfEven γ m) * z ^ m
  have hEven :
      HasSum (fun n : Nat => rawTerm (2 * n)) (Xi z) := by
    refine HasSum.congr_fun (hγ.hasSum_Xi z) ?_
    intro n
    dsimp [rawTerm]
    rw [xiCoefficientSequenceOfEven_even]
    have hn : (n.factorial : Complex) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have htwo_n : ((2 * n).factorial : Complex) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * n))
    field_simp [hn, htwo_n]
  have hOdd :
      HasSum (fun n : Nat => rawTerm (2 * n + 1)) 0 := by
    refine HasSum.congr_fun
      (hasSum_zero : HasSum (fun _ : Nat => (0 : Complex)) 0) ?_
    intro n
    dsimp [rawTerm]
    rw [xiCoefficientSequenceOfEven_odd]
    simp
  change HasSum rawTerm (Xi z)
  simpa only [add_zero] using HasSum.even_add_odd hEven hOdd

end RHLean
