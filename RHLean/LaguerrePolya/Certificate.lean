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
Laguerre-Polya class.  The hard classical theorem that nonzero membership
forces real zeros is still isolated as a named statement.
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

/-- The remaining hard Laguerre-Polya theorem needed by the RH spine.

The nonzero-target hypothesis is explicit because the zero function belongs to
closure-style Laguerre-Polya interfaces but does not satisfy `AllZerosReal`.
-/
def LaguerrePolyaZerosRealTheorem : Prop :=
  ∀ {F : Complex → Complex}, LaguerrePolyaClass F → NonzeroFunction F → AllZerosReal F

/-- The explicit dependency from Laguerre-Polya membership to real zeros. -/
theorem allZerosReal_of_laguerrePolya
    (hzeros : LaguerrePolyaZerosRealTheorem)
    {F : Complex → Complex} (hLP : LaguerrePolyaClass F) (hnonzero : NonzeroFunction F) :
    AllZerosReal F :=
  hzeros hLP hnonzero

/--
Laguerre-Polya membership for `Xi`, nonzero-`Xi`, and the named real-zero
theorem give RH through the discharged zeta-to-`Xi` transfer.
-/
theorem RH_from_LaguerrePolya_Xi
    (hzeros : LaguerrePolyaZerosRealTheorem)
    (hLP : LaguerrePolyaClass Xi)
    (hnonzero : NonzeroFunction Xi) :
    RiemannHypothesis :=
  RH_of_Xi_real_zeros
    (allZerosReal_of_laguerrePolya hzeros hLP hnonzero)

end RHLean
