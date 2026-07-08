/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import RHLean.LaguerrePolya.Certificate
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Jensen polynomial route for Xi coefficients

This file records the minimal Jensen-polynomial branch of the dependency graph.
The hard theorem turning hyperbolicity of all Jensen polynomials into a
Laguerre-Polya certificate for `Xi` remains a named proposition.
-/

noncomputable section

namespace RHLean

open scoped BigOperators

/-- A candidate coefficient sequence for the power-series expansion of `Xi`. -/
abbrev XiCoefficientSequence :=
  Nat → Complex

/-- The sequence `γ` is a power-series coefficient sequence for `Xi` at `0`. -/
def IsXiCoefficientSequence (γ : XiCoefficientSequence) : Prop :=
  ∀ z : Complex, HasSum (fun n : Nat => γ n * z ^ n) (Xi z)

/-- The Jensen polynomial `J_{γ,n,d}` attached to a coefficient sequence. -/
def JensenPolynomial (γ : XiCoefficientSequence) (n d : Nat) : Polynomial Complex :=
  Finset.sum (Finset.range (d + 1)) fun j =>
    Polynomial.C (((Nat.choose d j : Nat) : Complex) * γ (n + j)) * Polynomial.X ^ j

/-- Hyperbolicity over the reals, expressed through the existing real-rooted interface. -/
def PolynomialHyperbolicOverReal (p : Polynomial Complex) : Prop :=
  RealRootedPolynomial p

/-- All Jensen polynomials attached to `γ` are hyperbolic over the reals. -/
def AllJensenPolynomialsHyperbolic (γ : XiCoefficientSequence) : Prop :=
  ∀ n d : Nat, PolynomialHyperbolicOverReal (JensenPolynomial γ n d)

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

/-- The Jensen route gives RH once its named bridge and the zeta-to-`Xi` transfer are known. -/
theorem RH_from_JensenHyperbolicity_Xi
    (hcompleted : CompletedZetaZerosTransferToXi)
    (hbridge : JensenHyperbolicityToLaguerrePolyaXi)
    {γ : XiCoefficientSequence}
    (hγ : IsXiCoefficientSequence γ)
    (hJensen : AllJensenPolynomialsHyperbolic γ) :
    RiemannHypothesis :=
  RH_from_LaguerrePolya_Xi hcompleted
    (laguerrePolyaCertificateXiOfJensenHyperbolicity hbridge hγ hJensen)

end RHLean
