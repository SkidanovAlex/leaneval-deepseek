import Submission.ZagierHoffmanProof.StepL170
import Submission.ZagierHoffmanProof.StepL162
import Submission.Commons.Data.List.lex_append_of_ne_nil

set_option autoImplicit false
set_option maxHeartbeats 20000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L171: the G5 a-side `Init` invariant (the `C2'`/`C3` cases of the ambient measure)

For the G5 (all-`q` front) chain of `maink_case1_j0` (StepL146) the a-members
`D.cA i` (`D = BCqIter F (k-1) (toData F R0)`, `i ≠ iterIdx u`) satisfy, exactly as
StepL162's `type1_Init` for the `(k,j)`-chain type-1 members,
  `InitLt q s m ∨ (initList q s = initList q m ∧
     pad0 m (initLen q m) < pad0 s (initLen q s))`,
which is the tie-break (`C2'`/`C3`) of `ambNu`'s third block when the depth invariant
`r ≤ D.depA i` (StepL170) is not strict.

Ingredients: `BCqIter_cA_pad0_front` (positions `< k-1` of the member are `q`) plus
`hallq` (the same for `s`), and `BCqIter_cA_pad0_head` (position `k-1` of the member is the
base head `< s_{k-1}`, `hhead`).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The G5 a-side member `Init` invariant. -/
theorem maink_g5_aSide_Init (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hhead : ∀ i : R0.ιA, i ≠ u →
      ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) :
    let D := RelData.BCqIter F (k - 1) (toData F R0)
    ∀ i : D.ιA, i ≠ RelData.iterIdx F (k - 1) (toData F R0) u →
      (InitLt (Nat.card F) s (D.cA i) ∨
        (initList (Nat.card F) s = initList (Nat.card F) (D.cA i) ∧
          pad0 (D.cA i) (initLen (Nat.card F) (D.cA i))
            < pad0 s (initLen (Nat.card F) s))) := by
  classical
  intro D i hi
  let i₀ : R0.ιA := Eq.mpr (RelData.BCqIter_ιA F (k - 1) (toData F R0)).symm i
  have hiter : RelData.iterIdx F (k - 1) (toData F R0) i₀ = i := by
    dsimp only [RelData.iterIdx, i₀]
    exact eq_mpr_symm_id (RelData.BCqIter_ιA F (k - 1) (toData F R0)) i
  have hi₀ : i₀ ≠ u := by intro hc; exact hi (by rw [← hiter, hc])
  let q : ℕ := Nat.card F
  have hk2 : 2 ≤ q := card_ge_two F
  have hdep : D.depA i = R0.depA i₀ + (k - 1) := by
    dsimp only [D]
    have h := RelData.BCqIter_depA_at F (k - 1) (toData F R0) i₀
    rw [hiter] at h
    exact h
  have hdepk : k ≤ D.depA i := by
    rw [hdep]
    have hpos : 1 ≤ R0.depA i₀ := R0.hdepA i₀
    omega
  have hfront : ∀ x : ℕ, x < k - 1 → pad0 (D.cA i) x = pad0 s x := by
    intro x hx
    have h := BCqIter_cA_pad0_front F (k - 1) R0 i₀ x hx
    dsimp only [D]
    rw [← hiter]
    rw [h, hallq x hx]
  have htake : (valueList s).take (k - 1) = (valueList (D.cA i)).take (k - 1) :=
    valueList_take_eq_of_pad0_eq (D.cA i) s k hk1 hdepk hkr hfront
  have hlenS : (valueList s).length = r := valueList_length s
  have hsleq' : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ q := by
    intro x hx
    rw [hallq x hx]
  have htakeleS : ∀ v ∈ (valueList s).take (k - 1), v ≤ q :=
    valueList_take_le q s (k - 1) hsleq'
  have hdropS : (valueList s).drop (k - 1) =
      (s ⟨k - 1, by omega⟩ : ℕ) :: (valueList s).drop k := by
    have hlt : k - 1 < (valueList s).length := by rw [hlenS]; omega
    rw [List.drop_eq_getElem_cons hlt]
    have hk' : k - 1 + 1 = k := by omega
    rw [hk']
    congr 1
    exact valueList_getElem s (k - 1) (by omega)
  have hinitS : initList q s = (valueList s).take (k - 1) := by
    have hsplit : valueList s = (valueList s).take (k - 1) ++ (valueList s).drop (k - 1) :=
      (List.take_append_drop (k - 1) (valueList s)).symm
    have happ := initListAux_append_le q ((valueList s).take (k - 1))
      ((valueList s).drop (k - 1)) htakeleS
    have hnil : initListAux q ((valueList s).drop (k - 1)) = [] := by
      rw [hdropS]
      exact initListAux_cons_gt q _ _ (by simpa [q] using hbig)
    rw [initList, hsplit, happ, hnil, List.append_nil]
    rw [List.take_append_of_le_length (by rw [List.length_take]; rw [hlenS]; omega)]
    rw [List.take_take]
    congr 1
    omega
  have htakeleM : ∀ v ∈ (valueList (D.cA i)).take (k - 1), v ≤ q := by
    apply valueList_take_le q (D.cA i) (k - 1)
    intro x hx
    rw [hfront x hx]
    exact hsleq' x hx
  have hinitM : initList q (D.cA i) =
      (valueList (D.cA i)).take (k - 1) ++
        initListAux q ((valueList (D.cA i)).drop (k - 1)) := by
    have hsplit : valueList (D.cA i) =
        (valueList (D.cA i)).take (k - 1) ++ (valueList (D.cA i)).drop (k - 1) :=
      (List.take_append_drop (k - 1) (valueList (D.cA i))).symm
    conv_lhs => rw [initList, hsplit]
    exact initListAux_append_le q _ _ htakeleM
  have hmain : initList q (D.cA i) = initList q s ++
      initListAux q ((valueList (D.cA i)).drop (k - 1)) := by
    rw [hinitM, hinitS, ← htake]
  have hlenS2 : (initList q s).length = k - 1 := by
    rw [hinitS, List.length_take]
    rw [hlenS]
    omega
  set R : List ℕ := initListAux q ((valueList (D.cA i)).drop (k - 1)) with hRdef
  by_cases hR : R = []
  · right
    refine ⟨?_, ?_⟩
    · rw [hmain, hR, List.append_nil]
    · have hinitMlen : (initList q (D.cA i)).length = k - 1 := by
        rw [hmain, hR, List.append_nil, hlenS2]
      have hinitLenM : initLen q (D.cA i) = k - 1 := hinitMlen
      have hinitLenS : initLen q s = k - 1 := hlenS2
      rw [hinitLenM, hinitLenS]
      have hval := BCqIter_cA_pad0_head F (k - 1) R0 i₀
      dsimp only [D]
      rw [← hiter]
      rw [hval]
      have hss : pad0 s (k - 1) = (s ⟨k - 1, by omega⟩ : ℕ) := pad0_of_lt s (by omega)
      rw [hss]
      exact hhead i₀ hi₀
  · left
    rw [InitLt, hmain]
    exact Commons.Data.List.lex_append_of_ne_nil (fun a b : ℕ => a < b) (initList q s) R hR

end ZagierHoffmanPositiveChar
