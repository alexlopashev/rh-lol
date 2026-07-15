/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import RHLean.Jensen.Polynomial
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Monotone.Defs

/-!
# Total positivity route for sign-correct even xi coefficients

This file records a minimal Polya-frequency / total-positivity branch of the
dependency graph.  Toeplitz minors are attached only to the sign-correct even
coefficient sequence.  The explicit `xiCoefficientSequenceOfEven` map then
connects that sequence to the existing raw `Xi` Jensen-polynomial route instead
of asserting PF-infinity for the alternating raw Taylor sequence.
-/

noncomputable section

namespace RHLean

/-- A complex number regarded as a nonnegative real value. -/
def IsNonnegativeRealComplex (z : Complex) : Prop :=
  z.im = 0 ∧ 0 ≤ z.re

/-- A strictly increasing finite selection of natural-number indices. -/
def IsIncreasingNatSelection {k : Nat} (indices : Fin k → Nat) : Prop :=
  StrictMono indices

/-- Entry of the one-sided Toeplitz matrix attached to a coefficient sequence. -/
def toeplitzEntry (γ : XiEvenCoefficientSequence) (row col : Nat) : Complex :=
  if col ≤ row then γ (row - col) else 0

/-- A finite Toeplitz submatrix selected by row and column index maps.

The determinant of this matrix is the Mathlib matrix determinant used for
Toeplitz minors in the PF-infinity interface below.
-/
def toeplitzMinorMatrix
    (γ : XiEvenCoefficientSequence) {k : Nat} (rows cols : Fin k → Nat) :
    Matrix (Fin k) (Fin k) Complex :=
  fun i j => toeplitzEntry γ (rows i) (cols j)

/-- The determinant of a finite Toeplitz submatrix. -/
def toeplitzMinor
    (γ : XiEvenCoefficientSequence) {k : Nat} (rows cols : Fin k → Nat) : Complex :=
  (toeplitzMinorMatrix γ rows cols).det

/-- Conservative PF-infinity interface for a coefficient sequence.

This placeholder asks every finite Toeplitz minor selected by strictly
increasing row and column index maps to be a nonnegative real complex number.
-/
def PFInfinitySequence (γ : XiEvenCoefficientSequence) : Prop :=
  ∀ k : Nat, ∀ rows cols : Fin k → Nat,
    IsIncreasingNatSelection rows →
      IsIncreasingNatSelection cols →
        IsNonnegativeRealComplex (toeplitzMinor γ rows cols)

/-- There exists a sign-correct centered-even xi sequence satisfying PF-infinity. -/
def ExistsXiEvenCoefficientSequenceWithPFInfinity : Prop :=
  ∃ γ : XiEvenCoefficientSequence, IsXiEvenCoefficientSequence γ ∧ PFInfinitySequence γ

/--
The ordinary Jensen polynomial of the sign-correct even sequence.  This is the
object whose coefficients are directly controlled by singleton Toeplitz
minors; it is kept distinct from the raw `Xi` Jensen polynomial below.
-/
def SignCorrectedEvenJensenPolynomial
    (γ : XiEvenCoefficientSequence) (n d : Nat) : Polynomial Complex :=
  JensenPolynomial (fun m : Nat => γ m) n d

/--
The existing raw `Xi` Jensen polynomial reconstructed from sign-correct even
coefficients.  This is the exact object consumed by the discharged
Jensen-to-Laguerre-Polya theorem.
-/
def XiJensenPolynomialOfEven
    (γ : XiEvenCoefficientSequence) (n d : Nat) : Polynomial Complex :=
  JensenPolynomial (xiCoefficientSequenceOfEven γ) n d

/-- The hard boundary from PF-infinity Xi coefficients to Jensen hyperbolicity. -/
def PFInfinityToJensenHyperbolicity : Prop :=
  ∀ γ : XiEvenCoefficientSequence,
    IsXiEvenCoefficientSequence γ →
      PFInfinitySequence γ →
        AllJensenPolynomialsHyperbolic (xiCoefficientSequenceOfEven γ)

/--
Finite Polya-frequency zero-location theorem needed after the real-coefficient
bookkeeping is discharged below.

This is narrower than `PFInfinityToJensenHyperbolicity`: it no longer mentions
the centered `xi` series identity or the real-coefficient part of
hyperbolicity.  It is the remaining ASW/PF theorem for the current one-sided
Toeplitz-minor normalization and the exact raw `Xi` Jensen polynomials obtained
through `xiCoefficientSequenceOfEven`.  Thus the nontrivial compatibility with
the existing Jensen route is visible here rather than hidden in notation.
-/
def PFInfinityJensenZerosRealTheorem : Prop :=
  ∀ γ : XiEvenCoefficientSequence,
    PFInfinitySequence γ →
      ∀ n d : Nat, PolynomialZerosReal (XiJensenPolynomialOfEven γ n d)

/-- Apply a PF-infinity hypothesis to one increasing Toeplitz minor selection. -/
theorem PFInfinitySequence.toeplitzMinor_nonnegative
    {γ : XiEvenCoefficientSequence}
    (hPF : PFInfinitySequence γ)
    {k : Nat} {rows cols : Fin k → Nat}
    (hrows : IsIncreasingNatSelection rows)
    (hcols : IsIncreasingNatSelection cols) :
    IsNonnegativeRealComplex (toeplitzMinor γ rows cols) :=
  hPF k rows cols hrows hcols

/-- Every map out of `Fin 1` is strictly increasing. -/
private theorem strictMono_fin_one_nat (indices : Fin 1 → Nat) :
    StrictMono indices := by
  intro i j hij
  have hsub : i = j := Subsingleton.elim i j
  subst j
  exact False.elim ((lt_irrefl i) hij)

/-- The `1 × 1` Toeplitz minor with row `n` and column `0` is the coefficient `γ n`. -/
theorem toeplitzMinor_singleton_coeff
    (γ : XiEvenCoefficientSequence) (n : Nat) :
    toeplitzMinor γ (fun _ : Fin 1 => n) (fun _ : Fin 1 => 0) = γ n := by
  simp [toeplitzMinor, toeplitzMinorMatrix, toeplitzEntry]

/--
The `j`th Jensen coefficient is the binomial weight times the singleton
Toeplitz minor selecting the shifted coefficient `γ (n + j)`.
-/
theorem coeff_JensenPolynomial_eq_choose_mul_toeplitzMinor_singleton
    (γ : XiEvenCoefficientSequence) (n d j : Nat) (hj : j ≤ d) :
    (SignCorrectedEvenJensenPolynomial γ n d).coeff j =
      ((Nat.choose d j : Nat) : Complex) *
        toeplitzMinor γ (fun _ : Fin 1 => n + j) (fun _ : Fin 1 => 0) := by
  rw [SignCorrectedEvenJensenPolynomial,
    coeff_JensenPolynomial_of_le (fun m : Nat => γ m) n d j hj]
  rw [toeplitzMinor_singleton_coeff]

/-- A PF-infinity coefficient sequence has nonnegative-real coefficients. -/
theorem PFInfinitySequence.coeff_nonnegative
    {γ : XiEvenCoefficientSequence}
    (hPF : PFInfinitySequence γ)
    (n : Nat) :
    IsNonnegativeRealComplex (γ n) := by
  simpa [toeplitzMinor_singleton_coeff] using
    hPF.toeplitzMinor_nonnegative
      (k := 1)
      (rows := fun _ : Fin 1 => n)
      (cols := fun _ : Fin 1 => 0)
      (strictMono_fin_one_nat _)
      (strictMono_fin_one_nat _)

/-- A PF-infinity coefficient has zero imaginary part. -/
theorem PFInfinitySequence.coeff_im_eq_zero
    {γ : XiEvenCoefficientSequence}
    (hPF : PFInfinitySequence γ)
    (n : Nat) :
    (γ n).im = 0 :=
  (hPF.coeff_nonnegative n).1

/-- The real part of a PF-infinity coefficient is nonnegative. -/
theorem PFInfinitySequence.coeff_re_nonnegative
    {γ : XiEvenCoefficientSequence}
    (hPF : PFInfinitySequence γ)
    (n : Nat) :
    0 ≤ (γ n).re :=
  (hPF.coeff_nonnegative n).2

/--
PF-infinity supplies the real-coefficient part of the reconstructed raw `Xi`
Jensen hyperbolicity.

The only remaining finite theorem is zero-location for the binomially weighted
Jensen polynomial; see `PFInfinityJensenZerosRealTheorem`.
-/
theorem hasRealCoefficients_JensenPolynomial_of_pfInfinity
    {γ : XiEvenCoefficientSequence}
    (hPF : PFInfinitySequence γ)
    (n d : Nat) :
    HasRealCoefficients (XiJensenPolynomialOfEven γ n d) := by
  have hraw (m : Nat) : (xiCoefficientSequenceOfEven γ m).im = 0 := by
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · have hsign : (((-1 : Complex) ^ k).im) = 0 := by
        induction k with
        | zero => simp
        | succ k ih => simp [pow_succ, ih]
      simp [Complex.mul_im, Complex.inv_im, hPF.coeff_im_eq_zero, hsign]
    · simp
  intro j
  by_cases hj : j ≤ d
  · rw [XiJensenPolynomialOfEven,
      coeff_JensenPolynomial_of_le (xiCoefficientSequenceOfEven γ) n d j hj]
    simp [Complex.mul_im, hraw (n + j)]
  · rw [XiJensenPolynomialOfEven,
      coeff_JensenPolynomial_eq_zero_of_gt
        (xiCoefficientSequenceOfEven γ) n d j (Nat.lt_of_not_ge hj)]
    simp

/--
The finite PF zero-location theorem discharges the public
`PFInfinityToJensenHyperbolicity` bridge.
-/
theorem pfInfinityToJensenHyperbolicity_of_jensenZerosReal
    (hzeros : PFInfinityJensenZerosRealTheorem) :
    PFInfinityToJensenHyperbolicity := by
  intro γ _hγ hPF n d
  exact
    { real_coefficients := hasRealCoefficients_JensenPolynomial_of_pfInfinity hPF n d
      zeros_real := hzeros γ hPF n d }

/-- Apply the named PF-infinity to Jensen hyperbolicity boundary. -/
theorem allJensenPolynomialsHyperbolic_of_pfInfinity
    (hbridge : PFInfinityToJensenHyperbolicity)
    {γ : XiEvenCoefficientSequence}
    (hγ : IsXiEvenCoefficientSequence γ)
    (hPF : PFInfinitySequence γ) :
    AllJensenPolynomialsHyperbolic (xiCoefficientSequenceOfEven γ) :=
  hbridge γ hγ hPF

/--
The PF-infinity route gives RH through the Jensen boundary, the Jensen-to-
Laguerre-Polya membership bridge, and the explicit Laguerre-Polya zero theorem.
-/
theorem RH_from_PFInfinity_via_Jensen_Xi
    (hPFToJensen : PFInfinityToJensenHyperbolicity)
    (hzeros : LaguerrePolyaZerosRealTheorem)
    {γ : XiEvenCoefficientSequence}
    (hγ : IsXiEvenCoefficientSequence γ)
    (hPF : PFInfinitySequence γ) :
    RiemannHypothesis :=
  RH_from_JensenHyperbolicity_Xi
    hzeros
    (isXiCoefficientSequence_xiCoefficientSequenceOfEven hγ)
    (allJensenPolynomialsHyperbolic_of_pfInfinity hPFToJensen hγ hPF)

/-- The existential PF-infinity route factors through Jensen hyperbolicity. -/
theorem RH_from_exists_XiEvenCoefficientSequenceWithPFInfinity_via_Jensen
    (hPFToJensen : PFInfinityToJensenHyperbolicity)
    (hzeros : LaguerrePolyaZerosRealTheorem)
    (hcoeffs : ExistsXiEvenCoefficientSequenceWithPFInfinity) :
    RiemannHypothesis :=
  match hcoeffs with
  | ⟨_, hγ, hPF⟩ =>
      RH_from_PFInfinity_via_Jensen_Xi hPFToJensen hzeros hγ hPF

end RHLean
