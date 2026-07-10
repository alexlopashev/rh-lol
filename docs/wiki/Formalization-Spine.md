The core dependency spine is:

```text
Laguerre-Polya membership plus proved nonzero Xi plus the named zero theorem
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
- `LocallyUniformRealRootedApproximation : (Complex -> Complex) -> (Nat -> Polynomial Complex) -> Prop`
- `LocallyUniformRealRootedLimitZeroRealTheorem : Prop`
- `LocallyUniformRealRootedLimitOffRealAxisZeroExclusionTheorem : Prop`
- `LocallyUniformRealRootedLimitZerosRealTheorem : Prop`
- `LaguerrePolyaZerosRealTheorem : Prop`
- `XiCoefficientSequence : Type`
- `IsXiCoefficientSequence : XiCoefficientSequence -> Prop`
- `JensenPolynomial : XiCoefficientSequence -> Nat -> Nat -> Polynomial Complex`
- `JensenHyperbolicityToLaguerrePolyaXi : Prop`
- `IsIncreasingNatSelection : (Fin k -> Nat) -> Prop`
- `PFInfinitySequence : XiCoefficientSequence -> Prop`
- `toeplitzMinor : XiCoefficientSequence -> (Fin k -> Nat) -> (Fin k -> Nat) -> Complex`
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

The hard zero-preservation step is split out from the broader class-membership
wrapper:

```lean
def NonzeroFunction (F : Complex -> Complex) : Prop :=
  exists z : Complex, F z ≠ 0

def LocallyUniformRealRootedApproximation
    (F : Complex -> Complex) (p : Nat -> Polynomial Complex) : Prop :=
  (forall n : Nat, RealRootedPolynomial (p n)) /\
    TendstoLocallyUniformlyOn
      (fun (n : Nat) (z : Complex) => (p n).eval z) F Filter.atTop Set.univ

def LocallyUniformRealRootedLimitZeroRealTheorem : Prop :=
  forall {F : Complex -> Complex} {p : Nat -> Polynomial Complex} {z : Complex},
    LocallyUniformRealRootedApproximation F p -> NonzeroFunction F -> F z = 0 -> z.im = 0

def LocallyUniformRealRootedLimitOffRealAxisZeroExclusionTheorem : Prop :=
  forall {F : Complex -> Complex} {p : Nat -> Polynomial Complex} {z : Complex},
    LocallyUniformRealRootedApproximation F p -> NonzeroFunction F -> z.im ≠ 0 -> F z ≠ 0

def LocallyUniformRealRootedLimitZerosRealTheorem : Prop :=
  forall {F : Complex -> Complex} {p : Nat -> Polynomial Complex},
    LocallyUniformRealRootedApproximation F p -> NonzeroFunction F -> AllZerosReal F

def LaguerrePolyaZerosRealTheorem : Prop :=
  forall {F : Complex -> Complex},
    LaguerrePolyaClass F -> NonzeroFunction F -> AllZerosReal F

theorem laguerrePolyaZerosRealTheorem_of_locallyUniformRealRootedLimit
    (hlimit : LocallyUniformRealRootedLimitZerosRealTheorem) :
    LaguerrePolyaZerosRealTheorem

theorem Xi_nonzero : NonzeroFunction Xi
```

The public Laguerre-Polya RH wrapper keeps the hard inputs visible and supplies
the `Xi` nonzero fact internally:

```lean
theorem RH_from_LaguerrePolya_Xi
    (hzeros : LaguerrePolyaZerosRealTheorem)
    (hLP : LaguerrePolyaClass Xi) :
    RiemannHypothesis
```

It derives `AllZerosReal Xi` from membership, `Xi_nonzero`, and the named zero
theorem. This is not a direct wrapper around `AllZerosReal`.

The Jensen branch is represented as a separate route over the shared `XiCoefficientSequence` interface:

```lean
def JensenHyperbolicityToLaguerrePolyaXi : Prop :=
  forall gamma : XiCoefficientSequence,
    IsXiCoefficientSequence gamma ->
      AllJensenPolynomialsHyperbolic gamma ->
        Nonempty (LaguerrePolyaClass Xi)

def ExistsXiCoefficientSequenceWithJensenHyperbolicity : Prop :=
  exists gamma : XiCoefficientSequence,
    IsXiCoefficientSequence gamma /\ AllJensenPolynomialsHyperbolic gamma
```

These are named research theorem boundaries. The existential boundary packages
the analytic existence of usable `Xi` coefficients instead of making downstream
callers pick a sequence manually. It does not use the total-positivity route,
and it does not claim a proof of RH.

The Jensen RH wrappers do not construct a certificate behind the bridge. They
take `LaguerrePolyaZerosRealTheorem` as an explicit input alongside the
Jensen-to-membership theorem, and reuse `Xi_nonzero` before deriving
`AllZerosReal Xi`.

The total-positivity branch is represented as a separate route into the Jensen branch over the same xi coefficient object:

```lean
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
the dependency edge from PF-infinity coefficients to Jensen hyperbolicity
without duplicating Jensen polynomial definitions or adding a direct
certificate-producing route.
