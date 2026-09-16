/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.CountT0More
import Submission.ZagierHoffmanProof.StepL193

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Pointwise

/-!
# The trivial range `w < q` of Theorem A

For `w < q` every MZV of weight `w` is *already* a Hoffman tuple: the entries are positive and sum
to `w < q`, so they are automatically `≤ q` and the last one is `< q`.  Consequently the algebraic
part of Theorem A is trivial in that range, exactly as the paper remarks
("the algebraic part (i.e. Theorem A) is trivial when `w ≤ q`"):

  ★★ `zeta_mem_T_of_lt_card` : every weight-`w` MZV with `w < q` lies in `𝒯 w`;
  ★★ `theoremA_span_trivial (1 ≤ w) (w < q) : 𝒵 w = span K (𝒯 w)` — without the machinery of §2.2–§3.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ **Every MZV of weight `w < q` is a Hoffman tuple.** -/
theorem zeta_mem_T_of_lt_card {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) {w : ℕ}
    (hw : w < Nat.card F) (h𝔰 : weight r 𝔰 = w) : ζ_A F 𝔰 ∈ 𝒯 F w := by
  rw [𝒯, Set.mem_iUnion]
  refine ⟨⟨r, hr⟩, ?_⟩
  rw [mem_𝒯_aux_iff F w ⟨r, hr⟩]
  have hlt : ∀ i : Fin r, (𝔰 i : ℕ) < Nat.card F := by
    intro i
    have h := entry_le_weight 𝔰 i
    omega
  exact ⟨𝔰, h𝔰, fun i _ => le_of_lt (hlt i), hlt ⟨r - 1, by omega⟩, rfl⟩

/-- ★★ **Theorem A is trivial for `1 ≤ w < q`**: every weight-`w` MZV is already a `𝒯`-element, so
the span statement holds without the machinery of §2.2–§3. -/
theorem theoremA_span_trivial (w : ℕ) (hw1 : 1 ≤ w) (hw : w < Nat.card F) :
    𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w) := by
  refine le_antisymm ?_ (Submodule.span_le.mpr (𝒯_subset_𝒵 F w))
  rw [𝒵]
  refine Submodule.span_le.mpr ?_
  rintro x hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨r, hxr⟩ := hx
  rw [ζ_A_weight_mem_iff F w r] at hxr
  obtain ⟨𝔰, h𝔰w, rfl⟩ := hxr
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · exfalso
      subst h0
      have h0' : weight 0 𝔰 = 0 := by simp [weight]
      have hw0 : w = 0 := h𝔰w.symm.trans h0'
      omega
    · exact hpos
  exact Submodule.subset_span (zeta_mem_T_of_lt_card F hr 𝔰 hw h𝔰w)

end ZagierHoffmanPositiveChar
