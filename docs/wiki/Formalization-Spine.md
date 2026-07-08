# Formalization Spine

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
- `ZetaZerosTransferToXi : Prop`
- `LaguerrePolyaCertificate : (Complex -> Complex) -> Prop`

The current certificate is intentionally thin:

```lean
structure LaguerrePolyaCertificate (F : Complex -> Complex) : Prop where
  zeros_real : AllZerosReal F
```

This is a scaffolding contract. It must be replaced by real Laguerre-Polya definitions after the first RH bridge compiles.
