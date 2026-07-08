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
- `LaguerrePolyaCertificate : (Complex -> Complex) -> Prop`

Current bridge theorem:

```lean
theorem RH_of_Xi_real_zeros
    (hcompleted : CompletedZetaZerosTransferToXi)
    (hXi : AllZerosReal Xi) :
    RiemannHypothesis
```

`CompletedZetaZerosTransferToXi` is the remaining named analytic transfer from completed zeta zeros to `Xi` zeros. It is a visible scaffold hypothesis, not a proof of RH.

The current certificate is intentionally thin:

```lean
structure LaguerrePolyaCertificate (F : Complex -> Complex) : Prop where
  zeros_real : AllZerosReal F
```

This is a scaffolding contract. It must be replaced by real Laguerre-Polya definitions after the first RH bridge compiles.
