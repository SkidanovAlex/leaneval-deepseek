/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.ShuffleDepth
import Submission.ZagierHoffmanProof.StepL193

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open Polynomial RatFunc
open scoped BigOperators Pointwise

/-!
# Consequences of the product formula for the Hoffman spanning sets

Combining the product formula (`ShuffleGen`) with Theorem A (`𝒵 w = span K (𝒯 w)`, `StepL193`)
gives the multiplication law for the *Hoffman* spanning sets:

  ★★★ `T_mul_mem_span_T : span K (𝒯 w) · span K (𝒯 w') ⊆ span K (𝒯 (w+w'))`,
  ★★ `T0_mul_mem_span_T` (the same with `𝒯0` inputs),

and the paper's Remark 2.2(2) regime, where the Chen corrections `Δ^i_{a,b}` all vanish
(`a + b ≤ q - 1`) and the function field MZVs satisfy the *classical* stuffle relation:

  ★★ `zeta_mul_zeta_of_le (hab : a + b ≤ q - 1)`:
      `ζ_A(a)·ζ_A(b) = ζ_A(a+b) + ζ_A(a,b) + ζ_A(b,a)`,
  ★★ `tsum_diag_eq_of_le (hab) : Σ'_d P_d(a)·P_d(b) = ζ_A(a+b)`.

Everything is stated for an arbitrary finite field `F`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The paper's Remark 2.2(2) regime: below the threshold `a + b ≤ q - 1` the Chen coefficient
`Δ^i_{a,b}` vanishes for every `0 < i < a + b`. -/
lemma ChenDeltaZ_eq_zero_of_le {a b i : ℕ} (hab : a + b ≤ Nat.card F - 1) (hi1 : 1 ≤ i)
    (hi2 : i ≤ a + b - 1) : ChenDeltaZ F a b i = 0 := by
  rw [ChenDeltaZ, if_neg]
  intro hd
  have hpos : 0 < Nat.card F - 1 := by have := nat_card_ge_two F; omega
  have hge : Nat.card F - 1 ≤ i := Nat.le_of_dvd (by omega) hd
  omega

/-- ★★ **The classical stuffle relation for depth-one MZVs below the threshold.**  For
`a + b ≤ q - 1` the Chen corrections vanish and the function field MZVs satisfy the classical
stuffle relation `ζ_A(a)·ζ_A(b) = ζ_A(a+b) + ζ_A(a,b) + ζ_A(b,a)`. -/
theorem zeta_mul_zeta_of_le (a b : ℕ+) (hab : (a : ℕ) + (b : ℕ) ≤ Nat.card F - 1) :
    ζ_A F (single a) * ζ_A F (single b) =
      ζ_A F (single ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left a.pos (b : ℕ)⟩)
        + ζ_A F (pair a b) + ζ_A F (pair b a) := by
  rw [zeta_mul_zeta F a b]
  have hzero : ∀ i : DeltaIdx (a : ℕ) (b : ℕ), ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 = 0 := by
    intro i
    exact ChenDeltaZ_eq_zero_of_le F hab (Finset.mem_Icc.mp i.2).1 (Finset.mem_Icc.mp i.2).2
  rw [Finset.sum_eq_zero (fun i _ => by rw [hzero i, Int.cast_zero, zero_mul]), add_zero]

/-- ★★ **The diagonal identity below the threshold**: for `a + b ≤ q - 1`,
`Σ'_d P_d(a)·P_d(b) = ζ_A(a+b)`. -/
theorem tsum_diag_eq_of_le (a b : ℕ+) (hab : (a : ℕ) + (b : ℕ) ≤ Nat.card F - 1) :
    (∑' d : ℕ, P F d a * P F d b)
      = ζ_A F (single ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left a.pos (b : ℕ)⟩) := by
  rw [tsum_diag_eq F a b]
  have hzero : ∀ i : DeltaIdx (a : ℕ) (b : ℕ), ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 = 0 := by
    intro i
    exact ChenDeltaZ_eq_zero_of_le F hab (Finset.mem_Icc.mp i.2).1 (Finset.mem_Icc.mp i.2).2
  rw [Finset.sum_eq_zero (fun i _ => by rw [hzero i, Int.cast_zero, zero_mul]), add_zero]

/-- `𝒯0 w ⊆ 𝒯 w` (a tuple with all entries `< q` is a tuple with entries `≤ q` and last ` < q`). -/
lemma T0_subset_T (w : ℕ) : 𝒯0 F w ⊆ 𝒯 F w := by
  intro x hx
  rw [𝒯0, Set.mem_iUnion] at hx
  obtain ⟨r, hxr⟩ := hx
  rw [mem_𝒯0_aux_iff F w r] at hxr
  obtain ⟨𝔰, h𝔰, hlt, rfl⟩ := hxr
  rw [𝒯, Set.mem_iUnion]
  refine ⟨r, ?_⟩
  rw [mem_𝒯_aux_iff F w r]
  have hq : 2 ≤ Nat.card F := nat_card_ge_two F
  exact ⟨𝔰, h𝔰, fun i _ => by have := hlt i; omega, by have := hlt ⟨r - 1, by simp⟩; omega, rfl⟩

/-- ★★★ **The products of the Hoffman spanning sets lie in the Hoffman spanning set.** -/
theorem T_mul_mem_span_T {w w' : ℕ} (hw : 0 < w) (hw' : 0 < w')
    {x y : RatFunc.CompletionAtInfty F}
    (hx : x ∈ Submodule.span (RatFunc F) (𝒯 F w))
    (hy : y ∈ Submodule.span (RatFunc F) (𝒯 F w')) :
    x * y ∈ Submodule.span (RatFunc F) (𝒯 F (w + w')) := by
  rw [← theoremA_span_amb F w hw] at hx
  rw [← theoremA_span_amb F w' hw'] at hy
  rw [← theoremA_span_amb F (w + w') (by omega)]
  exact Z_mul_mem_Z F hx hy

/-- ★★ **The products of the `𝒯0`-spanning sets lie in the Hoffman spanning set.** -/
theorem T0_mul_mem_span_T {w w' : ℕ} (hw : 0 < w) (hw' : 0 < w')
    {x y : RatFunc.CompletionAtInfty F}
    (hx : x ∈ Submodule.span (RatFunc F) (𝒯0 F w))
    (hy : y ∈ Submodule.span (RatFunc F) (𝒯0 F w')) :
    x * y ∈ Submodule.span (RatFunc F) (𝒯 F (w + w')) := by
  refine T_mul_mem_span_T F hw hw' ?_ ?_
  · exact Submodule.span_mono (T0_subset_T F w) hx
  · exact Submodule.span_mono (T0_subset_T F w') hy

end ZagierHoffmanPositiveChar
