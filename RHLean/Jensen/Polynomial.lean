/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import RHLean.LaguerrePolya.Certificate
import RHLean.XiCoefficients
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.Prod
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm

/-!
# Jensen polynomial route for Xi coefficients

This file records the minimal Jensen-polynomial branch of the dependency graph.
The theorem turning hyperbolicity of all Jensen polynomials into a
Laguerre-Polya membership statement for `Xi` is discharged using explicitly
normalized Jensen polynomials and the coefficient-series hypothesis.
-/

noncomputable section

namespace RHLean

open Filter Topology

open scoped BigOperators
open scoped Topology

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

/-- The scalar multiplying the `j`th coefficient after evaluating a degree-`d`
Jensen polynomial at `z / (d + 1)`. -/
def jensenScale (d j : Nat) : Real :=
  (Nat.choose d j : Real) * ((d + 1 : Nat) : Real)⁻¹ ^ j

/-- The normalized Jensen coefficient multiplier is nonnegative. -/
theorem jensenScale_nonneg (d j : Nat) : 0 ≤ jensenScale d j := by
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _)

/-- The normalized Jensen coefficient multiplier is dominated by `1 / j!`. -/
theorem jensenScale_le_inv_factorial (d j : Nat) :
    jensenScale d j ≤ ((j.factorial : Nat) : Real)⁻¹ := by
  rw [jensenScale, inv_pow]
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  norm_cast
  simp only [one_mul]
  rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
  exact (Nat.descFactorial_le_pow d j).trans
    (Nat.pow_le_pow_left (Nat.le_succ d) j)

/-- The normalized Jensen coefficient multiplier tends to `1 / j!`. -/
theorem tendsto_jensenScale (j : Nat) :
    Filter.Tendsto (fun d : Nat => jensenScale d j) Filter.atTop
      (nhds ((j.factorial : Real)⁻¹)) := by
  have hratio :
      Filter.Tendsto (fun d : Nat => (d : Real) * ((d + 1 : Nat) : Real)⁻¹)
        Filter.atTop (nhds 1) := by
    simpa [div_eq_mul_inv] using
      (tendsto_natCast_div_add_atTop (1 : Real))
  simpa [jensenScale] using
    (ProbabilityTheory.tendsto_choose_mul_pow_atTop j hratio)

/-- The degree-`d` Jensen polynomial normalized by `z ↦ z / (d + 1)`. -/
def NormalizedJensenPolynomial
    (γ : XiCoefficientSequence) (d : Nat) : Polynomial Complex :=
  (JensenPolynomial γ 0 d).comp
    (Polynomial.C ((((d + 1 : Nat) : Complex)⁻¹)) * Polynomial.X)

/-- Evaluation of the normalized Jensen polynomial is evaluation of the
original polynomial at `z / (d + 1)`. -/
theorem eval_NormalizedJensenPolynomial
    (γ : XiCoefficientSequence) (d : Nat) (z : Complex) :
    (NormalizedJensenPolynomial γ d).eval z =
      (JensenPolynomial γ 0 d).eval ((((d + 1 : Nat) : Complex)⁻¹) * z) := by
  simp [NormalizedJensenPolynomial, Polynomial.eval_comp]

/-- Hyperbolicity over the reals, expressed through the existing real-rooted interface. -/
def PolynomialHyperbolicOverReal (p : Polynomial Complex) : Prop :=
  RealRootedPolynomial p

/-- All Jensen polynomials attached to `γ` are hyperbolic over the reals. -/
def AllJensenPolynomialsHyperbolic (γ : XiCoefficientSequence) : Prop :=
  ∀ n d : Nat, PolynomialHyperbolicOverReal (JensenPolynomial γ n d)

/-- Hyperbolicity of the degree-zero Jensen polynomials makes every coefficient real. -/
theorem coefficient_im_eq_zero_of_jensenHyperbolicity
    {γ : XiCoefficientSequence}
    (hJensen : AllJensenPolynomialsHyperbolic γ) (n : Nat) :
    (γ n).im = 0 := by
  have hreal := (hJensen n 0).real_coefficients 0
  simpa [coeff_JensenPolynomial_of_le γ n 0 0 (Nat.zero_le 0)] using hreal

/-- A real coefficient sequence makes its represented function real on real inputs. -/
theorem xi_real_on_real_of_jensenHyperbolicity
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ)
    (hJensen : AllJensenPolynomialsHyperbolic γ)
    (x : Real) :
    (Xi (x : Complex)).im = 0 := by
  have him := Complex.hasSum_im (hγ (x : Complex))
  have hterms :
      (fun n : Nat =>
        (((n.factorial : Complex)⁻¹ * γ n) * (x : Complex) ^ n).im) = 0 := by
    funext n
    have hxpow : ((x : Complex) ^ n).im = 0 := by
      induction n with
      | zero => simp
      | succ n ih => simp [pow_succ, Complex.mul_im, ih]
    simp [Complex.mul_im, Complex.inv_im,
      coefficient_im_eq_zero_of_jensenHyperbolicity hJensen n, hxpow]
  rw [hterms] at him
  simpa using him.unique hasSum_zero

/-- Positive real rescaling of the variable preserves the real-rooted interface. -/
theorem RealRootedPolynomial.comp_positive_real_mul_X
    {p : Polynomial Complex} (hp : RealRootedPolynomial p)
    {c : Real} (hc : 0 < c) :
    RealRootedPolynomial
      (p.comp (Polynomial.C (c : Complex) * Polynomial.X)) := by
  constructor
  · intro n
    rw [Polynomial.comp_C_mul_X_coeff]
    have hcpow : (((c : Complex) ^ n).im) = 0 := by
      induction n with
      | zero => simp
      | succ n ih => simp [pow_succ, Complex.mul_im, ih]
    simp [Complex.mul_im, hp.real_coefficients n, hcpow]
  · rcases hp.zeros_real with hpzero | hzeros
    · left
      simp [hpzero]
    · right
      intro z hz
      have hroot : p.eval ((c : Complex) * z) = 0 := by
        simpa [Polynomial.eval_comp] using hz
      have him := hzeros ((c : Complex) * z) hroot
      simp only [Complex.mul_im, Complex.ofReal_im, zero_mul, Complex.ofReal_re,
        add_zero] at him
      exact (mul_eq_zero.mp him).resolve_left hc.ne'

/-- The explicit normalized Jensen approximants remain real-rooted. -/
theorem realRootedPolynomial_normalizedJensenPolynomial
    {γ : XiCoefficientSequence}
    (hJensen : AllJensenPolynomialsHyperbolic γ) (d : Nat) :
    RealRootedPolynomial (NormalizedJensenPolynomial γ d) := by
  simpa [NormalizedJensenPolynomial, Nat.cast_add, Nat.cast_one] using
    (hJensen 0 d).comp_positive_real_mul_X
      (c := (((d + 1 : Nat) : Real)⁻¹)) (by positivity)

/-- The `j`th term in the evaluation of a normalized Jensen polynomial. -/
def normalizedJensenTerm
    (γ : XiCoefficientSequence) (d : Nat) (z : Complex) (j : Nat) : Complex :=
  (jensenScale d j : Complex) * γ j * z ^ j

/-- A normalized Jensen polynomial is the finite sum of its normalized terms. -/
theorem tsum_normalizedJensenTerm_eq_eval
    (γ : XiCoefficientSequence) (d : Nat) (z : Complex) :
    ∑' j : Nat, normalizedJensenTerm γ d z j =
      (NormalizedJensenPolynomial γ d).eval z := by
  rw [tsum_eq_sum (s := Finset.range (d + 1))]
  · rw [NormalizedJensenPolynomial, Polynomial.eval_comp]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [JensenPolynomial, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [normalizedJensenTerm, jensenScale, zero_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    push_cast
    rw [mul_pow]
    ring
  · intro j hj
    have hdj : d < j := by
      simpa [Finset.mem_range] using hj
    simp [normalizedJensenTerm, jensenScale, Nat.choose_eq_zero_of_lt hdj]

/-- The Xi coefficient series is absolutely summable on every fixed real radius. -/
theorem summable_norm_xiCoefficient_mul_pow
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ)
    {R : Real} (hR : 0 < R) :
    Summable fun j : Nat =>
      ‖((j.factorial : Complex)⁻¹ * γ j) * (R : Complex) ^ j‖ := by
  have hseries := hγ (((2 * R : Real) : Complex))
  have hnorm : ‖(R : Complex)‖ < ‖((2 * R : Real) : Complex)‖ := by
    simp [abs_of_pos hR]
    linarith
  exact (summable_powerSeries_of_norm_lt hseries.tendsto_sum_nat.cauchySeq hnorm).norm

/-- Joint convergence of the normalized Jensen series as the degree tends to
infinity and the evaluation point tends to a fixed point. -/
theorem tendsto_tsum_normalizedJensenTerm
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ) (x : Complex) :
    Filter.Tendsto
      (fun q : Nat × Complex => ∑' j : Nat, normalizedJensenTerm γ q.1 q.2 j)
      (Filter.atTop ×ˢ 𝓝 x) (𝓝 (Xi x)) := by
  let R : Real := ‖x‖ + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hsum : Summable fun j : Nat =>
      ‖((j.factorial : Complex)⁻¹ * γ j) * (R : Complex) ^ j‖ :=
    summable_norm_xiCoefficient_mul_pow hγ hR
  have hterm (j : Nat) :
      Filter.Tendsto
        (fun q : Nat × Complex => normalizedJensenTerm γ q.1 q.2 j)
        (Filter.atTop ×ˢ 𝓝 x)
        (𝓝 (((j.factorial : Complex)⁻¹ * γ j) * x ^ j)) := by
    have hscaleReal := tendsto_jensenScale j
    have hscaleComplex :
        Filter.Tendsto (fun d : Nat => (jensenScale d j : Complex)) Filter.atTop
          (𝓝 (((j.factorial : Real)⁻¹ : Real) : Complex)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hscaleReal
    have hscaleProduct := hscaleComplex.comp
      (tendsto_fst (f := Filter.atTop) (g := 𝓝 x))
    have hpowProduct :
        Filter.Tendsto (fun q : Nat × Complex => q.2 ^ j)
          (Filter.atTop ×ˢ 𝓝 x) (𝓝 (x ^ j)) :=
      (continuousAt_id.pow j).tendsto.comp
        (tendsto_snd (f := Filter.atTop) (g := 𝓝 x))
    simpa [normalizedJensenTerm] using
      (hscaleProduct.mul_const (γ j)).mul hpowProduct
  have hbound :
      ∀ᶠ q : Nat × Complex in Filter.atTop ×ˢ 𝓝 x,
        ∀ j : Nat,
          ‖normalizedJensenTerm γ q.1 q.2 j‖ ≤
            ‖((j.factorial : Complex)⁻¹ * γ j) * (R : Complex) ^ j‖ := by
    have hxR : x ∈ Metric.ball (0 : Complex) R := by
      simp [Metric.mem_ball, R]
    have hball : Metric.ball (0 : Complex) R ∈ 𝓝 x :=
      Metric.isOpen_ball.mem_nhds hxR
    filter_upwards [
      (tendsto_snd (f := Filter.atTop) (g := 𝓝 x)).eventually hball] with q hq
    intro j
    have hzR : ‖q.2‖ ≤ R := by
      exact le_of_lt (by simpa [Metric.mem_ball] using hq)
    calc
      ‖normalizedJensenTerm γ q.1 q.2 j‖ =
          jensenScale q.1 j * ‖γ j‖ * ‖q.2‖ ^ j := by
            simp [normalizedJensenTerm, norm_pow,
              abs_of_nonneg (jensenScale_nonneg q.1 j)]
      _ ≤ ((j.factorial : Nat) : Real)⁻¹ * ‖γ j‖ * R ^ j := by
            gcongr
            · exact jensenScale_le_inv_factorial q.1 j
      _ = ‖((j.factorial : Complex)⁻¹ * γ j) * (R : Complex) ^ j‖ := by
            simp [abs_of_pos hR]
  have htannery := tendsto_tsum_of_dominated_convergence hsum hterm hbound
  simpa [(hγ x).tsum_eq] using htannery

/-- The explicitly normalized Jensen polynomials converge locally uniformly to
`Xi`; this is derived from the coefficient series rather than stored in its
certificate. -/
theorem tendstoLocallyUniformlyOn_normalizedJensenPolynomial
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ) :
    TendstoLocallyUniformlyOn
      (fun (d : Nat) (z : Complex) => (NormalizedJensenPolynomial γ d).eval z)
      Xi Filter.atTop Set.univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro x _hx
  simp only [nhdsWithin_univ]
  have hEval :
      Filter.Tendsto
        (fun q : Nat × Complex => (NormalizedJensenPolynomial γ q.1).eval q.2)
        (Filter.atTop ×ˢ 𝓝 x) (𝓝 (Xi x)) := by
    simpa only [tsum_normalizedJensenTerm_eq_eval] using
      tendsto_tsum_normalizedJensenTerm hγ x
  have hXi :
      Filter.Tendsto (fun q : Nat × Complex => Xi q.2)
        (Filter.atTop ×ˢ 𝓝 x) (𝓝 (Xi x)) :=
    differentiable_Xi.continuous.continuousAt.tendsto.comp
      (tendsto_snd (f := Filter.atTop) (g := 𝓝 x))
  exact (hXi.prodMk hEval).mono_right
    (nhds_prod_eq.symm.trans_le (nhds_le_uniformity (Xi x)))

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
The Jensen hyperbolicity bridge is discharged by using the degree-`d` Jensen
polynomials based at `0`, normalized by `z ↦ z / (d + 1)`, as the
Laguerre-Polya approximants.
-/
theorem jensenHyperbolicityToLaguerrePolyaXi :
    JensenHyperbolicityToLaguerrePolyaXi := by
  intro γ hγ hJensen
  exact
    ⟨{ entire := Complex.analyticOnNhd_univ_iff_differentiable.mpr differentiable_Xi
       real_on_real := xi_real_on_real_of_jensenHyperbolicity hγ hJensen
       approximants := NormalizedJensenPolynomial γ
       approximants_real_rooted := realRootedPolynomial_normalizedJensenPolynomial hJensen
       locally_uniform_limit := tendstoLocallyUniformlyOn_normalizedJensenPolynomial hγ }⟩

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
