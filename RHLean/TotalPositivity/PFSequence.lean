/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import RHLean.LaguerrePolya.Certificate
import RHLean.XiCoefficients
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Monotone.Defs

/-!
# Total positivity route for Xi coefficients

This file records a minimal Polya-frequency / total-positivity branch of the
dependency graph.  The interface deliberately reuses the existing `Xi`
coefficient sequence and Laguerre-Polya certificate objects instead of creating
a parallel RH route.
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

/-- The remaining hard total-positivity theorem needed by the Laguerre-Polya route. -/
def TotalPositivityToLaguerrePolyaXi : Prop :=
  ∀ γ : XiCoefficientSequence,
    IsXiCoefficientSequence γ →
      PFInfinitySequence γ →
        Nonempty (LaguerrePolyaCertificate Xi)

/-- The explicit theorem boundary from PF-infinity coefficients to certificates for `Xi`. -/
theorem exists_laguerrePolyaCertificate_Xi_of_totalPositivity
    (hbridge : TotalPositivityToLaguerrePolyaXi)
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ)
    (hPF : PFInfinitySequence γ) :
    Nonempty (LaguerrePolyaCertificate Xi) :=
  hbridge γ hγ hPF

/-- A noncomputable certificate extracted from the named total-positivity theorem boundary. -/
def laguerrePolyaCertificateXiOfTotalPositivity
    (hbridge : TotalPositivityToLaguerrePolyaXi)
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ)
    (hPF : PFInfinitySequence γ) :
    LaguerrePolyaCertificate Xi :=
  Classical.choice
    (exists_laguerrePolyaCertificate_Xi_of_totalPositivity hbridge hγ hPF)

/-- The total-positivity route gives RH once its named bridge supplies a Laguerre-Polya certificate. -/
theorem RH_from_totalPositivity_Xi
    (hbridge : TotalPositivityToLaguerrePolyaXi)
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ)
    (hPF : PFInfinitySequence γ) :
    RiemannHypothesis :=
  RH_from_LaguerrePolya_Xi
    (laguerrePolyaCertificateXiOfTotalPositivity hbridge hγ hPF)

/-- The existential PF-infinity coefficient route gives RH through total positivity. -/
theorem RH_from_exists_XiCoefficientSequenceWithPFInfinity
    (hbridge : TotalPositivityToLaguerrePolyaXi)
    (hcoeffs : ExistsXiCoefficientSequenceWithPFInfinity) :
    RiemannHypothesis :=
  match hcoeffs with
  | ⟨_, hγ, hPF⟩ =>
      RH_from_totalPositivity_Xi hbridge hγ hPF

end RHLean
