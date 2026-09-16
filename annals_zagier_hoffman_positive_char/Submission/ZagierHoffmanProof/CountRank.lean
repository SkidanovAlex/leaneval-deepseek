/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.CountT0More
import Submission.ZagierHoffmanProof.TrivialRange
import Submission.ZagierHoffmanProof.StepL204

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Pointwise

/-!
# Spanning, counting and rank for the `𝒯0` sets, and the logical form of Theorems B/D

* ★★ `theoremA_span_T0_of_le (1 ≤ w ≤ q) : 𝒵 w = span K (𝒯0 w)` — in the range `w ≤ q` the
  smaller Hoffman set `𝒯0_w` also spans (the paper's "the algebraic part is trivial for `w ≤ q`",
  together with `𝒯0_w = 𝒯_w`).
* ★★ `ncard_T0_eq_d_of_le (1 ≤ w ≤ q) : |𝒯0_w| = d(w)`.
* ★★ `rank_ge_ncard_T_of_linearIndependent` / `rank_ge_ncard_T0_of_linearIndependent`: the
  "in particular" implication of Theorems B/D — a `K`-linear independence statement for the
  Hoffman sets implies the lower bound on `dim_K 𝒵_w`.  (This isolates the *only* ingredient of
  Theorems B/D that is not available: the linear independence itself, which needs the
  Anderson–Brownawell–Papanikolas criterion.)
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `𝒯0 w ⊆ 𝒵 w`. -/
lemma T0_subset_𝒵 (w : ℕ) : 𝒯0 F w ⊆ 𝒵 F w :=
  fun x hx => 𝒯_subset_𝒵 F w (T0_subset_T F w hx)

/-- ★★ For `1 ≤ w ≤ q`, the smaller Hoffman-type set `𝒯0_w` also spans `𝒵 w`. -/
theorem theoremA_span_T0_of_le (w : ℕ) (hw1 : 1 ≤ w) (hwq : w ≤ Nat.card F) :
    𝒵 F w = Submodule.span (RatFunc F) (𝒯0 F w) := by
  rw [theoremA_span_amb F w hw1, ← T0_eq_T_of_le F w hwq]

/-- ★★ For `1 ≤ w ≤ q`, the number of `𝒯0`-elements is `d(w)`. -/
theorem ncard_T0_eq_d_of_le {w : ℕ} (hw1 : 1 ≤ w) (hwq : w ≤ Nat.card F) :
    Set.ncard (𝒯0 F w) = d F w := by
  rw [ncard_T0_eq_hoffCount0 F w hw1, hoffCount0_eq_d_of_le F hw1 hwq]

/-- ★★ **The "in particular" of Theorem B/D**: `K`-linear independence of the Hoffman set `𝒯 w`
gives the lower bound `d(w) ≤ dim_K 𝒵 w`. -/
theorem rank_ge_ncard_T_of_linearIndependent {w : ℕ} (hw : 1 ≤ w)
    (h : LinearIndependent (RatFunc F) ((↑) : 𝒯 F w → RatFunc.CompletionAtInfty F)) :
    (Set.ncard (𝒯 F w) : Cardinal) ≤ Module.rank (RatFunc F) (𝒵 F w) := by
  classical
  have hli : LinearIndependent (RatFunc F)
      (fun x : 𝒯 F w => (⟨x.1, 𝒯_subset_𝒵 F w x.2⟩ : 𝒵 F w)) :=
    h.of_comp (Submodule.subtype (𝒵 F w))
  calc (Set.ncard (𝒯 F w) : Cardinal)
      = Cardinal.mk {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯 F w} :=
        Set.cast_ncard (s := 𝒯 F w) (T_finite F w hw)
    _ ≤ Module.rank (RatFunc F) (𝒵 F w) := hli.cardinal_le_rank

/-- ★★ The same for `𝒯0`. -/
theorem rank_ge_ncard_T0_of_linearIndependent {w : ℕ} (hw : 1 ≤ w)
    (h : LinearIndependent (RatFunc F) ((↑) : 𝒯0 F w → RatFunc.CompletionAtInfty F)) :
    (Set.ncard (𝒯0 F w) : Cardinal) ≤ Module.rank (RatFunc F) (𝒵 F w) := by
  classical
  have hli : LinearIndependent (RatFunc F)
      (fun x : 𝒯0 F w => (⟨x.1, T0_subset_𝒵 F w x.2⟩ : 𝒵 F w)) :=
    h.of_comp (Submodule.subtype (𝒵 F w))
  calc (Set.ncard (𝒯0 F w) : Cardinal)
      = Cardinal.mk {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} :=
        Set.cast_ncard (s := 𝒯0 F w) (T0_finite F w hw)
    _ ≤ Module.rank (RatFunc F) (𝒵 F w) := hli.cardinal_le_rank

/-- The `𝒯0`-form of the lower bound with the count made explicit: for `1 ≤ w ≤ q` it reads
`d(w) ≤ dim_K 𝒵 w`. -/
theorem d_le_rank_of_linearIndependent_T0_of_le {w : ℕ} (hw1 : 1 ≤ w) (hwq : w ≤ Nat.card F)
    (h : LinearIndependent (RatFunc F) ((↑) : 𝒯0 F w → RatFunc.CompletionAtInfty F)) :
    (d F w : Cardinal) ≤ Module.rank (RatFunc F) (𝒵 F w) := by
  rw [← ncard_T0_eq_d_of_le F hw1 hwq]
  exact rank_ge_ncard_T0_of_linearIndependent F hw1 h

end ZagierHoffmanPositiveChar
