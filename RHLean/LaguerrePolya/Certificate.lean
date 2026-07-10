/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import RHLean.RHBridge
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Laguerre-Polya class interface

This file records a conservative Mathlib-compatible interface for the
Laguerre-Polya class.  The hard classical theorem that nonzero locally uniform
limits of real-rooted polynomials have only real zeros is still isolated as a
named statement, and the broader membership-to-real-zeros theorem is derived
from that boundary.
-/

noncomputable section

namespace RHLean

open Complex

/-- A complex polynomial has real coefficients when every coefficient is real. -/
def HasRealCoefficients (p : Polynomial Complex) : Prop :=
  ∀ n : Nat, (p.coeff n).im = 0

/-- A complex polynomial is real-rooted when all of its complex zeros lie on the real axis. -/
def PolynomialZerosReal (p : Polynomial Complex) : Prop :=
  ∀ z : Complex, p.eval z = 0 → z.im = 0

/-- Polynomial approximants allowed in the Laguerre-Polya closure definition. -/
structure RealRootedPolynomial (p : Polynomial Complex) : Prop where
  real_coefficients : HasRealCoefficients p
  zeros_real : PolynomialZerosReal p

/-- A conservative analytic interface for the real Laguerre-Polya class.

The data says that `F` is an entire complex function, real-valued on the real
axis, and locally uniformly approximated by complex polynomials whose
coefficients and zeros are real.  This does not include the hard closure theorem
that zeros of the limit remain real; that theorem is named separately below.
-/
structure LaguerrePolyaClass (F : Complex → Complex) where
  /-- The target function is entire. -/
  entire : AnalyticOnNhd Complex F Set.univ
  /-- The target function takes real values on real inputs. -/
  real_on_real : ∀ x : Real, (F (x : Complex)).im = 0
  /-- Real-rooted polynomial approximants converging to the target function. -/
  approximants : Nat → Polynomial Complex
  /-- Each approximating polynomial has real coefficients and only real zeros. -/
  approximants_real_rooted : ∀ n : Nat, RealRootedPolynomial (approximants n)
  /-- The approximating polynomials converge locally uniformly on the complex plane. -/
  locally_uniform_limit :
    TendstoLocallyUniformlyOn
      (fun (n : Nat) (z : Complex) => (approximants n).eval z) F Filter.atTop Set.univ

/-- A target function is not identically zero. -/
def NonzeroFunction (F : Complex → Complex) : Prop :=
  ∃ z : Complex, F z ≠ 0

/-- The approximation data from the Laguerre-Polya interface that matters for zeros. -/
def LocallyUniformRealRootedApproximation
    (F : Complex → Complex) (p : Nat → Polynomial Complex) : Prop :=
  (∀ n : Nat, RealRootedPolynomial (p n)) ∧
    TendstoLocallyUniformlyOn
      (fun (n : Nat) (z : Complex) => (p n).eval z) F Filter.atTop Set.univ

/-- Laguerre-Polya membership supplies the real-rooted locally uniform approximation data. -/
theorem locallyUniformRealRootedApproximation_of_laguerrePolya
    {F : Complex → Complex} (hLP : LaguerrePolyaClass F) :
    LocallyUniformRealRootedApproximation F hLP.approximants :=
  ⟨hLP.approximants_real_rooted, hLP.locally_uniform_limit⟩

/-- The current `xi` normalization is nonzero at `s = 1`. -/
theorem xi_one_ne_zero : xi (1 : Complex) ≠ 0 := by
  rw [xi]
  norm_num

/-- The critical-line transform `Xi` is not identically zero. -/
theorem Xi_nonzero : NonzeroFunction Xi := by
  refine ⟨-Complex.I * ((1 : Complex) - (1 / 2 : Complex)), ?_⟩
  rw [Xi_neg_I_mul_sub_half]
  exact xi_one_ne_zero

/-- The hard zero-preservation theorem for locally uniform real-rooted limits.

This is the analytic boundary where Hurwitz-style zero preservation and the
locally uniform limit argument belong.  The nonzero-target hypothesis is
explicit because the zero function can be a locally uniform limit of real-rooted
polynomials but does not satisfy `AllZerosReal`.
-/
def LocallyUniformRealRootedLimitZerosRealTheorem : Prop :=
  ∀ {F : Complex → Complex} {p : Nat → Polynomial Complex},
    LocallyUniformRealRootedApproximation F p → NonzeroFunction F → AllZerosReal F

/-- The remaining hard Laguerre-Polya theorem needed by the RH spine. -/
def LaguerrePolyaZerosRealTheorem : Prop :=
  ∀ {F : Complex → Complex}, LaguerrePolyaClass F → NonzeroFunction F → AllZerosReal F

/--
The broad Laguerre-Polya zero theorem follows from the local-uniform-limit
zero-preservation boundary plus the approximation fields of `LaguerrePolyaClass`.
-/
theorem laguerrePolyaZerosRealTheorem_of_locallyUniformRealRootedLimit
    (hlimit : LocallyUniformRealRootedLimitZerosRealTheorem) :
    LaguerrePolyaZerosRealTheorem := by
  intro F hLP hnonzero
  exact hlimit
    (locallyUniformRealRootedApproximation_of_laguerrePolya hLP)
    hnonzero

/-- The explicit dependency from Laguerre-Polya membership to real zeros. -/
theorem allZerosReal_of_laguerrePolya
    (hzeros : LaguerrePolyaZerosRealTheorem)
    {F : Complex → Complex} (hLP : LaguerrePolyaClass F) (hnonzero : NonzeroFunction F) :
    AllZerosReal F :=
  hzeros hLP hnonzero

/--
Laguerre-Polya membership for `Xi` and the named real-zero theorem give RH
through the discharged zeta-to-`Xi` transfer and the proved nonzero-`Xi` fact.
-/
theorem RH_from_LaguerrePolya_Xi
    (hzeros : LaguerrePolyaZerosRealTheorem)
    (hLP : LaguerrePolyaClass Xi) :
    RiemannHypothesis :=
  RH_of_Xi_real_zeros
    (allZerosReal_of_laguerrePolya hzeros hLP Xi_nonzero)

end RHLean
