/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.ShuffleSpan

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators

/-!
# Regression tests for the general product formula (`ShuffleGen`)

Concrete instantiations over `ZMod 2`: the depth-one case recovers
`ZetaShuffle.zeta_single_mul_mem_Z`, depth-two products land in `𝒵 4`, the graded-algebra
statement `𝒵 1 · 𝒵 2 ≤ 𝒵 3`, and the `𝒯`-version.
-/

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

/-- Depth-one products of MZVs lie in `𝒵` at the sum of the weights. -/
example (a b : ℕ+) :
    ζ_A (ZMod 2) (single a) * ζ_A (ZMod 2) (single b) ∈ 𝒵 (ZMod 2) ((a : ℕ) + (b : ℕ)) := by
  have h := zeta_mul_mem_Z (F := ZMod 2) (by omega : 0 < 1) (by omega : 0 < 1)
    (single a) (single b)
  simpa [weight_single] using h

/-- `ζ_A(1,1)² ∈ 𝒵 4`. -/
example : ζ_A (ZMod 2) (pair 1 1) * ζ_A (ZMod 2) (pair 1 1) ∈ 𝒵 (ZMod 2) 4 := by
  have h := zeta_mul_mem_Z (F := ZMod 2) (by omega : 0 < 2) (by omega : 0 < 2)
    (pair 1 1) (pair 1 1)
  simpa [weight_pair] using h

/-- The graded-algebra statement at `(1,2)`. -/
example : 𝒵 (ZMod 2) 1 * 𝒵 (ZMod 2) 2 ≤ 𝒵 (ZMod 2) 3 :=
  Z_mul_Z_le (ZMod 2) 1 2

/-- Products of `𝒯`-elements land in `𝒵`. -/
example {x y : RatFunc.CompletionAtInfty (ZMod 2)} (hx : x ∈ 𝒯 (ZMod 2) 1)
    (hy : y ∈ 𝒯 (ZMod 2) 1) : x * y ∈ 𝒵 (ZMod 2) 2 :=
  T_mul_T_mem_Z (F := ZMod 2) (w := 1) (w' := 1) hx hy

/-- `𝒵 1 · 𝒵 1 ≤ 𝒵 2`. -/
example : 𝒵 (ZMod 2) 1 * 𝒵 (ZMod 2) 1 ≤ 𝒵 (ZMod 2) 2 :=
  Z_mul_Z_le_pnat (ZMod 2) 1 1

/-- A three-fold product: `(∏_{i<3} ζ_A(1)) ∈ 𝒵 3`. -/
example : (∏ _ : Fin 3, ζ_A (ZMod 2) (single 1)) ∈ 𝒵 (ZMod 2) 3 := by
  have hx : ∀ i : Fin 3, ζ_A (ZMod 2) (single 1) ∈ 𝒵 (ZMod 2) ((fun _ : Fin 3 => 1) i) :=
    fun _ => zeta_mem_Z (F := ZMod 2) (single 1) (by simp [weight_single])
  have h := Z_prod_mem_Z (ZMod 2) (fun _ : Fin 3 => 1) (fun _ => ζ_A (ZMod 2) (single 1)) hx
  simpa using h

/-- The depth filtration: `ζ_A(1,1) ∈ 𝒵depth 2 2`, and its multiplicativity. -/
example : ζ_A (ZMod 2) (pair 1 1) ∈ 𝒵depth (ZMod 2) 2 2 :=
  zeta_mem_Zdepth (ZMod 2) (pair 1 1) (weight_pair 1 1) (by norm_num)

example : 𝒵depth (ZMod 2) 1 1 * 𝒵depth (ZMod 2) 1 1 ≤ 𝒵depth (ZMod 2) 2 2 :=
  Zdepth_mul_le (ZMod 2) 1 1 1 1

/-- The filtration is exhaustive. -/
example : 𝒵depth (ZMod 2) 3 3 = 𝒵 (ZMod 2) 3 := Zdepth_eq_Z (ZMod 2) (le_refl 3)

/-- The classical stuffle relation below the threshold (over `F₃`, `1 + 1 ≤ 2`):
`ζ_A(1)² = ζ_A(2) + 2·ζ_A(1,1)`. -/
example : ζ_A (ZMod 3) (single 1) * ζ_A (ZMod 3) (single 1) =
    ζ_A (ZMod 3) (single 2) + ζ_A (ZMod 3) (pair 1 1) + ζ_A (ZMod 3) (pair 1 1) := by
  refine zeta_mul_zeta_of_le (ZMod 3) 1 1 ?_
  rw [Nat.card_eq_fintype_card, ZMod.card]
  norm_num

/-- The products of the Hoffman spanning sets stay in the Hoffman spanning set. -/
example {x y : RatFunc.CompletionAtInfty (ZMod 2)}
    (hx : x ∈ Submodule.span (RatFunc (ZMod 2)) (𝒯 (ZMod 2) 1))
    (hy : y ∈ Submodule.span (RatFunc (ZMod 2)) (𝒯 (ZMod 2) 2)) :
    x * y ∈ Submodule.span (RatFunc (ZMod 2)) (𝒯 (ZMod 2) 3) :=
  T_mul_mem_span_T (ZMod 2) (w := 1) (w' := 2) (by norm_num) (by norm_num) hx hy

end ZagierHoffmanPositiveChar