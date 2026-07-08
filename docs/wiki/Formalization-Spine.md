The core dependency spine is:

```text
Laguerre-Polya certificate for Xi
  -> all zeros of Xi are real
  -> all nontrivial zeta zeros lie on the critical line
  -> Mathlib.RiemannHypothesis
```

Current core objects:

- `xi : Complex -> Complex`
- `Xi : Complex -> Complex`
- `AllZerosReal : (Complex -> Complex) -> Prop`
- `CompletedZetaZerosTransferToXi : Prop`
- `ZetaZerosTransferToXi : CompletedZetaZerosTransferToXi -> ...`
- `LaguerrePolyaClass : (Complex -> Complex) -> Type`
- `LaguerrePolyaZerosRealTheorem : Prop`
- `LaguerrePolyaCertificate : (Complex -> Complex) -> Type`
- `JensenPolynomial : XiCoefficientSequence -> Nat -> Nat -> Polynomial Complex`
- `JensenHyperbolicityToLaguerrePolyaXi : Prop`
- `PFInfinitySequence : XiCoefficientSequence -> Prop`
- `toeplitzMinor : XiCoefficientSequence -> (Fin k -> Nat) -> (Fin k -> Nat) -> Complex`
- `TotalPositivityToLaguerrePolyaXi : Prop`

Current bridge theorem:

```lean
theorem RH_of_Xi_real_zeros
    (hcompleted : CompletedZetaZerosTransferToXi)
    (hXi : AllZerosReal Xi) :
    RiemannHypothesis
```

`CompletedZetaZerosTransferToXi` is the remaining named analytic transfer from completed zeta zeros to `Xi` zeros. It is a visible scaffold hypothesis, not a proof of RH.

The Laguerre-Polya interface is an analytic closure statement:

```lean
structure LaguerrePolyaClass (F : Complex -> Complex) where
  entire : AnalyticOnNhd Complex F Set.univ
  real_on_real : forall x : Real, (F (x : Complex)).im = 0
  approximants : Nat -> Polynomial Complex
  approximants_real_rooted : forall n : Nat, RealRootedPolynomial (approximants n)
  locally_uniform_limit :
    TendstoLocallyUniformlyOn
      (fun (n : Nat) (z : Complex) => (approximants n).eval z) F Filter.atTop Set.univ
```

The hard closure theorem is still explicit:

```lean
def LaguerrePolyaZerosRealTheorem : Prop :=
  forall {F : Complex -> Complex}, LaguerrePolyaClass F -> AllZerosReal F
```

`LaguerrePolyaCertificate` packages membership in this class with that named theorem. It is not a direct wrapper around `AllZerosReal`.

The Jensen branch is now represented as a separate route:

```lean
def JensenHyperbolicityToLaguerrePolyaXi : Prop :=
  forall gamma : XiCoefficientSequence,
    IsXiCoefficientSequence gamma ->
      AllJensenPolynomialsHyperbolic gamma ->
        Nonempty (LaguerrePolyaCertificate Xi)
```

This is a named research theorem boundary. It does not use the total-positivity route, and it does not claim a proof of RH.

The total-positivity branch is represented as another separate route over the same xi coefficient object:

```lean
def TotalPositivityToLaguerrePolyaXi : Prop :=
  forall gamma : XiCoefficientSequence,
    IsXiCoefficientSequence gamma ->
      PFInfinitySequence gamma ->
        Nonempty (LaguerrePolyaCertificate Xi)
```

This is also a named research theorem boundary. The PF-infinity interface records Toeplitz minor determinants explicitly and does not duplicate Jensen polynomial definitions.
