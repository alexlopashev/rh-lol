/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import RHLean.LaguerrePolya.Certificate
import RHLean.XiCoefficients
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Jensen polynomial route for Xi coefficients

This file records the minimal Jensen-polynomial branch of the dependency graph.
The hard theorem turning hyperbolicity of all Jensen polynomials into a
Laguerre-Polya certificate for `Xi` remains a named proposition.
-/

noncomputable section

namespace RHLean

open scoped BigOperators

/-- The Jensen polynomial `J_{γ,n,d}` attached to a coefficient sequence. -/
def JensenPolynomial (γ : XiCoefficientSequence) (n d : Nat) : Polynomial Complex :=
  Finset.sum (Finset.range (d + 1)) fun j =>
    Polynomial.C (((Nat.choose d j : Nat) : Complex) * γ (n + j)) * Polynomial.X ^ j

/-- In-range coefficients of the Jensen polynomial are the expected binomial-weighted entries. -/
theorem coeff_JensenPolynomial_of_le
    (γ : XiCoefficientSequence) (n d j : Nat) (hj : j ≤ d) :
    (JensenPolynomial γ n d).coeff j =
      ((Nat.choose d j : Nat) : Complex) * γ (n + j) := by
  rw [JensenPolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro k _ hk
    rw [Polynomial.coeff_C_mul_X_pow, if_neg hk.symm]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).elim

/-- Coefficients above the Jensen polynomial's defining range vanish. -/
theorem coeff_JensenPolynomial_eq_zero_of_gt
    (γ : XiCoefficientSequence) (n d j : Nat) (hj : d < j) :
    (JensenPolynomial γ n d).coeff j = 0 := by
  rw [JensenPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hkj : j ≠ k := (lt_of_le_of_lt hk_le hj).ne'
  rw [Polynomial.coeff_C_mul_X_pow, if_neg hkj]

/-- The Jensen polynomial has no support outside the range used in its finite-sum definition. -/
theorem support_JensenPolynomial_subset_range
    (γ : XiCoefficientSequence) (n d : Nat) :
    (JensenPolynomial γ n d).support ⊆ Finset.range (d + 1) := by
  intro j hj
  rw [Finset.mem_range]
  rw [Polynomial.mem_support_iff] at hj
  by_contra hnot
  have hdj : d < j := Nat.lt_of_not_ge fun hjd => hnot (Nat.lt_succ_of_le hjd)
  exact hj (coeff_JensenPolynomial_eq_zero_of_gt γ n d j hdj)

/-- The Jensen polynomial has degree at most `d`. -/
theorem natDegree_JensenPolynomial_le
    (γ : XiCoefficientSequence) (n d : Nat) :
    (JensenPolynomial γ n d).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  exact coeff_JensenPolynomial_eq_zero_of_gt γ n d j hj

/-- Hyperbolicity over the reals, expressed through the existing real-rooted interface. -/
def PolynomialHyperbolicOverReal (p : Polynomial Complex) : Prop :=
  RealRootedPolynomial p

/-- All Jensen polynomials attached to `γ` are hyperbolic over the reals. -/
def AllJensenPolynomialsHyperbolic (γ : XiCoefficientSequence) : Prop :=
  ∀ n d : Nat, PolynomialHyperbolicOverReal (JensenPolynomial γ n d)

/-- There exists an `Xi` coefficient sequence whose Jensen polynomials are all hyperbolic. -/
def ExistsXiCoefficientSequenceWithJensenHyperbolicity : Prop :=
  ∃ γ : XiCoefficientSequence, IsXiCoefficientSequence γ ∧ AllJensenPolynomialsHyperbolic γ

/-- The remaining hard Jensen-polynomial theorem needed by the Laguerre-Polya route. -/
def JensenHyperbolicityToLaguerrePolyaXi : Prop :=
  ∀ γ : XiCoefficientSequence,
    IsXiCoefficientSequence γ →
      AllJensenPolynomialsHyperbolic γ →
        Nonempty (LaguerrePolyaCertificate Xi)

/-- The explicit theorem boundary from Jensen hyperbolicity to certificates for `Xi`. -/
theorem exists_laguerrePolyaCertificate_Xi_of_jensenHyperbolicity
    (hbridge : JensenHyperbolicityToLaguerrePolyaXi)
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ)
    (hJensen : AllJensenPolynomialsHyperbolic γ) :
    Nonempty (LaguerrePolyaCertificate Xi) :=
  hbridge γ hγ hJensen

/-- A noncomputable certificate extracted from the named Jensen theorem boundary. -/
def laguerrePolyaCertificateXiOfJensenHyperbolicity
    (hbridge : JensenHyperbolicityToLaguerrePolyaXi)
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ)
    (hJensen : AllJensenPolynomialsHyperbolic γ) :
    LaguerrePolyaCertificate Xi :=
  Classical.choice
    (exists_laguerrePolyaCertificate_Xi_of_jensenHyperbolicity hbridge hγ hJensen)

/-- The Jensen route gives RH once its named bridge supplies a Laguerre-Polya certificate. -/
theorem RH_from_JensenHyperbolicity_Xi
    (hbridge : JensenHyperbolicityToLaguerrePolyaXi)
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ)
    (hJensen : AllJensenPolynomialsHyperbolic γ) :
    RiemannHypothesis :=
  RH_from_LaguerrePolya_Xi
    (laguerrePolyaCertificateXiOfJensenHyperbolicity hbridge hγ hJensen)

/-- The existential Jensen-coefficient route gives RH through the named Jensen bridge. -/
theorem RH_from_exists_XiCoefficientSequenceWithJensenHyperbolicity
    (hbridge : JensenHyperbolicityToLaguerrePolyaXi)
    (hcoeffs : ExistsXiCoefficientSequenceWithJensenHyperbolicity) :
    RiemannHypothesis :=
  match hcoeffs with
  | ⟨_, hγ, hJensen⟩ =>
      RH_from_JensenHyperbolicity_Xi hbridge hγ hJensen

end RHLean
