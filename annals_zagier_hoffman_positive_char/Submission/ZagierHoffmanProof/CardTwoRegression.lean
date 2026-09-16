import Submission.ZagierHoffmanProof.StepL203
import Submission.ZagierHoffmanProof.StepL202

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Regression checks: Theorems B and D over `F = ZMod 2`

Concrete instantiations of `theorem_B_card_two` / `theorem_D_card_two` at `F = ZMod 2`
(`q = 2`), where all three challenge theorems are now proven unconditionally: Theorem A is
general (StepL193), Theorems B/D are StepL203 in this case.

Also instantiates the generalised non-vanishing of StepL202 (entries `q^k·m`, `m ≤ q`) at
`F = ZMod 2`, e.g. the tuple `(4, 2)` (`= (2²·1, 2¹·1)`) and `(8, 4, 2)`.
-/

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

example : Nat.card (ZMod 2) = 2 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]

/-- `𝒯0 (ZMod 2) 3` is the singleton `{ζ_A(1,1,1)}`. -/
example : 𝒯0 (ZMod 2) 3 = ({ζ_A (ZMod 2) (onesTuple 3)} : Set (RatFunc.CompletionAtInfty (ZMod 2))) :=
  T0_card_two_eq (ZMod 2) (by rw [Nat.card_eq_fintype_card, ZMod.card]) 3 (by norm_num)

/-- ★ Theorem B over `F₂` at weight `3`. -/
example : LinearIndependent (RatFunc (ZMod 2))
      (Subtype.val : 𝒯0 (ZMod 2) 3 → RatFunc.CompletionAtInfty (ZMod 2)) ∧
    Module.rank (RatFunc (ZMod 2)) (𝒵 (ZMod 2) 3) ≥ Set.ncard (𝒯0 (ZMod 2) 3) :=
  theorem_B_card_two (ZMod 2) (by rw [Nat.card_eq_fintype_card, ZMod.card]) 3 (by norm_num)

/-- ★ Theorem B over `F₂` at weight `5`. -/
example : LinearIndependent (RatFunc (ZMod 2))
      (Subtype.val : 𝒯0 (ZMod 2) 5 → RatFunc.CompletionAtInfty (ZMod 2)) ∧
    Module.rank (RatFunc (ZMod 2)) (𝒵 (ZMod 2) 5) ≥ Set.ncard (𝒯0 (ZMod 2) 5) :=
  theorem_B_card_two (ZMod 2) (by rw [Nat.card_eq_fintype_card, ZMod.card]) 5 (by norm_num)

/-- `𝒯 (ZMod 2) 2` is the singleton `{ζ_A(1,1)}`. -/
example : 𝒯 (ZMod 2) 2 = ({ζ_A (ZMod 2) (onesTuple 2)} : Set (RatFunc.CompletionAtInfty (ZMod 2))) :=
  T_two_card_two_eq (ZMod 2) (by rw [Nat.card_eq_fintype_card, ZMod.card])

/-- ★ Theorem D over `F₂` at weight `2` (the whole hypothesis range `w ≤ 2`). -/
example : LinearIndependent (RatFunc (ZMod 2))
      (Subtype.val : 𝒯 (ZMod 2) 2 → RatFunc.CompletionAtInfty (ZMod 2)) ∧
    Module.rank (RatFunc (ZMod 2)) (𝒵 (ZMod 2) 2) = d (ZMod 2) 2 :=
  theorem_D_card_two (ZMod 2) (by rw [Nat.card_eq_fintype_card, ZMod.card]) 2 (by norm_num)

/-- `d (ZMod 2) 2 = 1`. -/
example : d (ZMod 2) 2 = 1 :=
  d_two_card_two (ZMod 2) (by rw [Nat.card_eq_fintype_card, ZMod.card])

/-- Non-vanishing of the pair `(q²·1, q·1) = (4,2)` over `F₂`: a different power of `q` in each
entry (out of reach of StepL201, which scales all entries by the same power). -/
example : ζ_A (ZMod 2)
    (fun i : Fin 2 => (qExp (ZMod 2)) ^ (if i = 0 then 2 else 1) * oneExp) ≠ 0 :=
  zeta_scaled_entries_ne_zero (ZMod 2) (by norm_num) _
    (fun i : Fin 2 => if i = 0 then 2 else 1) (fun _ => oneExp)
    (fun _ => by simp [oneExp]) (fun _ => rfl)

/-- Non-vanishing of `(q³·1, q²·1, q·1) = (8,4,2)` over `F₂`. -/
example : ζ_A (ZMod 2)
    (fun i : Fin 3 => (qExp (ZMod 2)) ^ (if i = 0 then 3 else if i = 1 then 2 else 1) * oneExp) ≠ 0 :=
  zeta_scaled_entries_ne_zero (ZMod 2) (by norm_num) _
    (fun i : Fin 3 => if i = 0 then 3 else if i = 1 then 2 else 1) (fun _ => oneExp)
    (fun _ => by simp [oneExp]) (fun _ => rfl)

/-- Non-vanishing of a mixed tuple: entries `q·1 = 2` and `q²·1 = 4` interleaved. -/
example : ζ_A (ZMod 2)
    (fun i : Fin 3 => (qExp (ZMod 2)) ^ (if i = 1 then 2 else 1) * oneExp) ≠ 0 :=
  zeta_scaled_entries_ne_zero (ZMod 2) (by norm_num) _
    (fun i : Fin 3 => if i = 1 then 2 else 1) (fun _ => oneExp)
    (fun _ => by simp [oneExp]) (fun _ => rfl)

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

/-- ★★★ **Theorem B of the challenge, over `F = ZMod 2`**: for every weight `w`, the MZVs in
`𝒯0 (ZMod 2) w` are linearly independent over `K` and `dim_K 𝒵 w ≥ |𝒯0 w|`. -/
theorem theorem_B_zmod2 (w : ℕ+) :
    LinearIndependent (RatFunc (ZMod 2))
        (Subtype.val : 𝒯0 (ZMod 2) w → RatFunc.CompletionAtInfty (ZMod 2)) ∧
      Module.rank (RatFunc (ZMod 2)) (𝒵 (ZMod 2) w) ≥ Set.ncard (𝒯0 (ZMod 2) w) :=
  theorem_B_card_two (ZMod 2) (by rw [Nat.card_eq_fintype_card, ZMod.card]) w w.pos

/-- ★★★ **Theorem D of the challenge, over `F = ZMod 2`**: for `w ≤ 2q - 2 = 2`, `𝒯 w` is a
`K`-basis of `𝒵 w` and `dim_K 𝒵 w = d(w)`. -/
theorem theorem_D_zmod2 (w : ℕ+) (hw : (w : ℕ) ≤ 2 * Nat.card (ZMod 2) - 2) :
    LinearIndependent (RatFunc (ZMod 2))
        (Subtype.val : 𝒯 (ZMod 2) w → RatFunc.CompletionAtInfty (ZMod 2)) ∧
      Module.rank (RatFunc (ZMod 2)) (𝒵 (ZMod 2) w) = d (ZMod 2) w :=
  theorem_D_card_two (ZMod 2) (by rw [Nat.card_eq_fintype_card, ZMod.card]) w hw

/-- ★★★ **Theorem A of the challenge, over `F = ZMod 2`** (the general proof, instantiated). -/
theorem theorem_A_zmod2 (w : ℕ+) :
    𝒵 (ZMod 2) w = Submodule.span (RatFunc (ZMod 2)) (𝒯 (ZMod 2) w) ∧
      Module.rank (RatFunc (ZMod 2)) (𝒵 (ZMod 2) w) ≤ d (ZMod 2) w :=
  theorem_A_amb (ZMod 2) w

end ZagierHoffmanPositiveChar
