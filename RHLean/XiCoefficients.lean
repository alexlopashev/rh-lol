/-
Copyright (c) 2026 Sasha Lopashev. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sasha Lopashev
-/
import RHLean.ZetaXi
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Xi coefficient sequences

This file records the shared coefficient-sequence interface used by the Jensen
polynomial and total-positivity branches.
-/

noncomputable section

namespace RHLean

/-- A candidate coefficient sequence for the power-series expansion of `Xi`. -/
abbrev XiCoefficientSequence :=
  Nat → Complex

/-- The sequence `γ` is a power-series coefficient sequence for `Xi` at `0`. -/
def IsXiCoefficientSequence (γ : XiCoefficientSequence) : Prop :=
  ∀ z : Complex, HasSum (fun n : Nat => γ n * z ^ n) (Xi z)

end RHLean
