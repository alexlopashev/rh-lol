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
- `completedZetaZerosTransferToXi : CompletedZetaZerosTransferToXi`
- `ZetaZerosTransferToXi : ...`
- `LaguerrePolyaClass : (Complex -> Complex) -> Type`
- `LaguerrePolyaZerosRealTheorem : Prop`
- `LaguerrePolyaCertificate : (Complex -> Complex) -> Type`
- `XiCoefficientSequence : Type`
- `IsXiCoefficientSequence : XiCoefficientSequence -> Prop`
- `JensenPolynomial : XiCoefficientSequence -> Nat -> Nat -> Polynomial Complex`
- `JensenHyperbolicityToLaguerrePolyaXi : Prop`
- `IsIncreasingNatSelection : (Fin k -> Nat) -> Prop`
- `PFInfinitySequence : XiCoefficientSequence -> Prop`
- `toeplitzMinor : XiCoefficientSequence -> (Fin k -> Nat) -> (Fin k -> Nat) -> Complex`
- `TotalPositivityToLaguerrePolyaXi : Prop`
- `PFInfinityToJensenHyperbolicity : Prop`

Current bridge theorem:

```lean
theorem RH_of_Xi_real_zeros
    (hXi : AllZerosReal Xi) :
    RiemannHypothesis
```

`CompletedZetaZerosTransferToXi` remains as a named transfer proposition, and `completedZetaZerosTransferToXi` proves it from the current completed zeta definitions. It is no longer an external hypothesis of the public RH bridge. This is not a proof of RH: the remaining hard route to `AllZerosReal Xi` stays behind named Laguerre-Polya, Jensen, and total-positivity theorem boundaries.

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
def NonzeroFunction (F : Complex -> Complex) : Prop :=
  exists z : Complex, F z ≠ 0

def LaguerrePolyaZerosRealTheorem : Prop :=
  forall {F : Complex -> Complex},
    LaguerrePolyaClass F -> NonzeroFunction F -> AllZerosReal F
```

`LaguerrePolyaCertificate` packages membership in this class, an explicit nonzero-target witness, and that named theorem. It is not a direct wrapper around `AllZerosReal`.

The Jensen branch is represented as a separate route over the shared `XiCoefficientSequence` interface:

```lean
def JensenHyperbolicityToLaguerrePolyaXi : Prop :=
  forall gamma : XiCoefficientSequence,
    IsXiCoefficientSequence gamma ->
      AllJensenPolynomialsHyperbolic gamma ->
        Nonempty (LaguerrePolyaCertificate Xi)

def ExistsXiCoefficientSequenceWithJensenHyperbolicity : Prop :=
  exists gamma : XiCoefficientSequence,
    IsXiCoefficientSequence gamma /\ AllJensenPolynomialsHyperbolic gamma
```

These are named research theorem boundaries. The existential boundary packages
the analytic existence of usable `Xi` coefficients instead of making downstream
callers pick a sequence manually. It does not use the total-positivity route,
and it does not claim a proof of RH.

The total-positivity branch is represented as another separate route over the same xi coefficient object:

```lean
def TotalPositivityToLaguerrePolyaXi : Prop :=
  forall gamma : XiCoefficientSequence,
    IsXiCoefficientSequence gamma ->
      PFInfinitySequence gamma ->
        Nonempty (LaguerrePolyaCertificate Xi)

def PFInfinityToJensenHyperbolicity : Prop :=
  forall gamma : XiCoefficientSequence,
    IsXiCoefficientSequence gamma ->
      PFInfinitySequence gamma ->
        AllJensenPolynomialsHyperbolic gamma

def ExistsXiCoefficientSequenceWithPFInfinity : Prop :=
  exists gamma : XiCoefficientSequence,
    IsXiCoefficientSequence gamma /\ PFInfinitySequence gamma
```

These are also named research theorem boundaries. The PF-infinity interface
records Toeplitz minor determinants explicitly for strictly increasing row and
column index selections. The `PFInfinityToJensenHyperbolicity` boundary records
the separate dependency edge from PF-infinity coefficients to Jensen
hyperbolicity without duplicating Jensen polynomial definitions.
