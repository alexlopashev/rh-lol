/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import RHLean.LaguerrePolya.Certificate
import RHLean.XiCoefficients

/-!
# Jensen polynomial route for Xi coefficients

This file records the minimal Jensen-polynomial branch of the dependency graph.
The theorem turning hyperbolicity of all Jensen polynomials into a
Laguerre-Polya membership statement for `Xi` is discharged from the analytic
data now carried by `IsXiCoefficientSequence`.
-/

noncomputable section

namespace RHLean

open scoped BigOperators

/-- The Jensen polynomial `J_{γ,n,d}` attached to a coefficient sequence. -/
def JensenPolynomial (γ : XiCoefficientSequence) (n d : Nat) : Polynomial Complex :=
  XiCoefficientJensenPolynomial γ n d

/-- In-range coefficients of the Jensen polynomial are the expected binomial-weighted entries. -/
theorem coeff_JensenPolynomial_of_le
    (γ : XiCoefficientSequence) (n d j : Nat) (hj : j ≤ d) :
    (JensenPolynomial γ n d).coeff j =
      ((Nat.choose d j : Nat) : Complex) * γ (n + j) := by
  rw [JensenPolynomial, XiCoefficientJensenPolynomial, Polynomial.finsetSum_coeff]
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
  rw [JensenPolynomial, XiCoefficientJensenPolynomial, Polynomial.finsetSum_coeff]
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

/-- The Jensen-polynomial theorem needed by the Laguerre-Polya route. -/
def JensenHyperbolicityToLaguerrePolyaXi : Prop :=
  ∀ γ : XiCoefficientSequence,
    IsXiCoefficientSequence γ →
      AllJensenPolynomialsHyperbolic γ →
        Nonempty (LaguerrePolyaClass Xi)

/--
The Jensen hyperbolicity bridge is discharged by using the degree-`d`
Jensen polynomials based at `0` as the Laguerre-Polya approximants.
-/
theorem jensenHyperbolicityToLaguerrePolyaXi :
    JensenHyperbolicityToLaguerrePolyaXi := by
  intro γ hγ hJensen
  exact
    ⟨{ entire := hγ.xi_entire
       real_on_real := hγ.xi_real_on_real
       approximants := fun d => JensenPolynomial γ 0 d
       approximants_real_rooted := fun d => hJensen 0 d
       locally_uniform_limit := by
        simpa [JensenPolynomial] using hγ.jensen_locally_uniform_limit }⟩

/-- The explicit theorem from Jensen hyperbolicity to Laguerre-Polya membership for `Xi`. -/
theorem exists_laguerrePolyaClass_Xi_of_jensenHyperbolicity
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ)
    (hJensen : AllJensenPolynomialsHyperbolic γ) :
    Nonempty (LaguerrePolyaClass Xi) :=
  jensenHyperbolicityToLaguerrePolyaXi γ hγ hJensen

/-- Extract only Laguerre-Polya membership from Jensen hyperbolicity. -/
def laguerrePolyaClassXiOfJensenHyperbolicity
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ)
    (hJensen : AllJensenPolynomialsHyperbolic γ) :
    LaguerrePolyaClass Xi :=
  Classical.choice
    (exists_laguerrePolyaClass_Xi_of_jensenHyperbolicity hγ hJensen)

/--
The Jensen route gives RH after the separate Laguerre-Polya zero theorem is
supplied; nonzero-`Xi` is proved once in the Laguerre-Polya bridge.
-/
theorem RH_from_JensenHyperbolicity_Xi
    (hzeros : LaguerrePolyaZerosRealTheorem)
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ)
    (hJensen : AllJensenPolynomialsHyperbolic γ) :
    RiemannHypothesis :=
  RH_from_LaguerrePolya_Xi
    hzeros
    (laguerrePolyaClassXiOfJensenHyperbolicity hγ hJensen)

/-- The existential Jensen-coefficient route gives RH through the discharged Jensen bridge. -/
theorem RH_from_exists_XiCoefficientSequenceWithJensenHyperbolicity
    (hzeros : LaguerrePolyaZerosRealTheorem)
    (hcoeffs : ExistsXiCoefficientSequenceWithJensenHyperbolicity) :
    RiemannHypothesis :=
  match hcoeffs with
  | ⟨_, hγ, hJensen⟩ =>
      RH_from_JensenHyperbolicity_Xi hzeros hγ hJensen

end RHLean
