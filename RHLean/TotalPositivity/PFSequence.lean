/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import RHLean.Jensen.Polynomial
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Monotone.Defs

/-!
# Total positivity route for Xi coefficients

This file records a minimal Polya-frequency / total-positivity branch of the
dependency graph.  The interface deliberately reuses the existing `Xi`
coefficient sequence and Jensen-polynomial route instead of creating a parallel
RH route.
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
def toeplitzEntry (γ : XiCoefficientSequence) (row col : Nat) : Complex :=
  if col ≤ row then γ (row - col) else 0

/-- A finite Toeplitz submatrix selected by row and column index maps.

The determinant of this matrix is the Mathlib matrix determinant used for
Toeplitz minors in the PF-infinity interface below.
-/
def toeplitzMinorMatrix
    (γ : XiCoefficientSequence) {k : Nat} (rows cols : Fin k → Nat) :
    Matrix (Fin k) (Fin k) Complex :=
  fun i j => toeplitzEntry γ (rows i) (cols j)

/-- The determinant of a finite Toeplitz submatrix. -/
def toeplitzMinor
    (γ : XiCoefficientSequence) {k : Nat} (rows cols : Fin k → Nat) : Complex :=
  (toeplitzMinorMatrix γ rows cols).det

/-- Conservative PF-infinity interface for a coefficient sequence.

This placeholder asks every finite Toeplitz minor selected by strictly
increasing row and column index maps to be a nonnegative real complex number.
-/
def PFInfinitySequence (γ : XiCoefficientSequence) : Prop :=
  ∀ k : Nat, ∀ rows cols : Fin k → Nat,
    IsIncreasingNatSelection rows →
      IsIncreasingNatSelection cols →
        IsNonnegativeRealComplex (toeplitzMinor γ rows cols)

/-- There exists an `Xi` coefficient sequence satisfying the PF-infinity condition. -/
def ExistsXiCoefficientSequenceWithPFInfinity : Prop :=
  ∃ γ : XiCoefficientSequence, IsXiCoefficientSequence γ ∧ PFInfinitySequence γ

/-- The hard boundary from PF-infinity Xi coefficients to Jensen hyperbolicity. -/
def PFInfinityToJensenHyperbolicity : Prop :=
  ∀ γ : XiCoefficientSequence,
    IsXiCoefficientSequence γ →
      PFInfinitySequence γ →
        AllJensenPolynomialsHyperbolic γ

/--
Finite Polya-frequency zero-location theorem needed after the real-coefficient
bookkeeping is discharged below.

This is narrower than `PFInfinityToJensenHyperbolicity`: it no longer mentions
`Xi`, `IsXiCoefficientSequence`, or the real-coefficient part of hyperbolicity.
It is the remaining ASW/PF theorem for the current one-sided Toeplitz-minor
normalization and the binomially weighted Jensen polynomials.
-/
def PFInfinityJensenZerosRealTheorem : Prop :=
  ∀ γ : XiCoefficientSequence,
    PFInfinitySequence γ →
      ∀ n d : Nat, PolynomialZerosReal (JensenPolynomial γ n d)

/-- Apply a PF-infinity hypothesis to one increasing Toeplitz minor selection. -/
theorem PFInfinitySequence.toeplitzMinor_nonnegative
    {γ : XiCoefficientSequence}
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
    (γ : XiCoefficientSequence) (n : Nat) :
    toeplitzMinor γ (fun _ : Fin 1 => n) (fun _ : Fin 1 => 0) = γ n := by
  simp [toeplitzMinor, toeplitzMinorMatrix, toeplitzEntry]

/--
The `j`th Jensen coefficient is the binomial weight times the singleton
Toeplitz minor selecting the shifted coefficient `γ (n + j)`.
-/
theorem coeff_JensenPolynomial_eq_choose_mul_toeplitzMinor_singleton
    (γ : XiCoefficientSequence) (n d j : Nat) (hj : j ≤ d) :
    (JensenPolynomial γ n d).coeff j =
      ((Nat.choose d j : Nat) : Complex) *
        toeplitzMinor γ (fun _ : Fin 1 => n + j) (fun _ : Fin 1 => 0) := by
  rw [coeff_JensenPolynomial_of_le γ n d j hj]
  rw [toeplitzMinor_singleton_coeff]

/-- A PF-infinity coefficient sequence has nonnegative-real coefficients. -/
theorem PFInfinitySequence.coeff_nonnegative
    {γ : XiCoefficientSequence}
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
    {γ : XiCoefficientSequence}
    (hPF : PFInfinitySequence γ)
    (n : Nat) :
    (γ n).im = 0 :=
  (hPF.coeff_nonnegative n).1

/-- The real part of a PF-infinity coefficient is nonnegative. -/
theorem PFInfinitySequence.coeff_re_nonnegative
    {γ : XiCoefficientSequence}
    (hPF : PFInfinitySequence γ)
    (n : Nat) :
    0 ≤ (γ n).re :=
  (hPF.coeff_nonnegative n).2

/--
PF-infinity supplies the real-coefficient part of Jensen hyperbolicity.

The only remaining finite theorem is zero-location for the binomially weighted
Jensen polynomial; see `PFInfinityJensenZerosRealTheorem`.
-/
theorem hasRealCoefficients_JensenPolynomial_of_pfInfinity
    {γ : XiCoefficientSequence}
    (hPF : PFInfinitySequence γ)
    (n d : Nat) :
    HasRealCoefficients (JensenPolynomial γ n d) := by
  intro j
  by_cases hj : j ≤ d
  · rw [coeff_JensenPolynomial_of_le γ n d j hj]
    simp [Complex.mul_im, hPF.coeff_im_eq_zero (n + j)]
  · rw [coeff_JensenPolynomial_eq_zero_of_gt γ n d j (Nat.lt_of_not_ge hj)]
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
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ)
    (hPF : PFInfinitySequence γ) :
    AllJensenPolynomialsHyperbolic γ :=
  hbridge γ hγ hPF

/--
The PF-infinity route gives RH through the Jensen boundary, the Jensen-to-
Laguerre-Polya membership bridge, and the explicit Laguerre-Polya zero theorem.
-/
theorem RH_from_PFInfinity_via_Jensen_Xi
    (hPFToJensen : PFInfinityToJensenHyperbolicity)
    (hJensenBridge : JensenHyperbolicityToLaguerrePolyaXi)
    (hzeros : LaguerrePolyaZerosRealTheorem)
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ)
    (hPF : PFInfinitySequence γ) :
    RiemannHypothesis :=
  RH_from_JensenHyperbolicity_Xi
    hJensenBridge
    hzeros
    hγ
    (allJensenPolynomialsHyperbolic_of_pfInfinity hPFToJensen hγ hPF)

/-- The existential PF-infinity route factors through Jensen hyperbolicity. -/
theorem RH_from_exists_XiCoefficientSequenceWithPFInfinity_via_Jensen
    (hPFToJensen : PFInfinityToJensenHyperbolicity)
    (hJensenBridge : JensenHyperbolicityToLaguerrePolyaXi)
    (hzeros : LaguerrePolyaZerosRealTheorem)
    (hcoeffs : ExistsXiCoefficientSequenceWithPFInfinity) :
    RiemannHypothesis :=
  match hcoeffs with
  | ⟨_, hγ, hPF⟩ =>
      RH_from_PFInfinity_via_Jensen_Xi hPFToJensen hJensenBridge hzeros hγ hPF

end RHLean
