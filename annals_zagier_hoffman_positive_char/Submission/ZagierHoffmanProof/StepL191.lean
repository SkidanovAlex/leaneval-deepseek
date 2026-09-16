import Submission.ZagierHoffmanProof.StepL182
import Submission.ZagierHoffmanProof.StepL168
import Submission.ZagierHoffmanProof.StepL164

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L191: the level-1 base as an AMBIENT port - the member descents

Route (C) needs the level-1 chain (Lemma 2.9 / `H1_expT`, StepL51) as a port at an
arbitrary ambient level: an input `s` with `q < s_1` expands at level `Lam` provided
each member `c` of the chain either is `Lam`-admissible or descends in the ambient
measure `ambNu Lam`.  This module supplies the two member descents:

  * the `a`-members `ca i` (`aSide_order` + `aSide_weight_lt` + `level1_aMember_dep_ge`):
    the ambient prefix sum drops, else the depth is at least as large (and strictly
    larger gives the descent), else the `Init`-length of `s` is `0` (its head exceeds
    `q`) and the member grows the `Init` or strictly drops the head;
  * the `b`-members `1 :: cb j` (the same, with the head literally `1`, so the `Init`
    of the member is never empty).

Also the elementary `Init`/`initVal` helpers used by both.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The `initVal` of a tuple with empty `Init` vanishes. -/
lemma initVal_eq_zero_of_initList_eq_nil (q w : ℕ) {r : ℕ} (s : Fin r → ℕ+)
    (h : initList q s = []) : initVal q w s = 0 := by
  show padCode (q + 2) (w + 1) (initList q s) = 0
  rw [h]
  exact padCode_nil (q + 2) (w + 1)

/-- A tuple with nonempty `Init` has positive `initVal` (its leading digit is `>= 1`). -/
lemma initVal_pos_of_initList_ne_nil (q w : ℕ) {r : ℕ} (s : Fin r → ℕ+)
    (h : initList q s ≠ []) : 0 < initVal q w s := by
  classical
  obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil h
  have ha : 1 ≤ a := initList_mem_pos q s a (by rw [ht]; simp)
  have hB : 1 ≤ q + 2 := by omega
  have hp : 0 < (q + 2) ^ w := pow_pos (by omega : 0 < q + 2) w
  have hmul : 0 < a * (q + 2) ^ w := Nat.mul_pos (by omega : 0 < a) hp
  show 0 < padCode (q + 2) (w + 1) (initList q s)
  rw [ht]
  show 0 < padCode (q + 2) (w + 1) (a :: t)
  rw [show padCode (q + 2) (w + 1) (a :: t) = a * (q + 2) ^ w + padCode (q + 2) w t from rfl]
  omega

/-- A tuple whose visible head exceeds `q` has empty `Init`. -/
lemma initLen_eq_zero_of_head_gt (q : ℕ) {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+)
    (h : q < pad0 s 0) : initLen q s = 0 := by
  have h' : q < (s ⟨0, hr⟩ : ℕ) := by rwa [pad0_of_lt s hr] at h
  have hle := initLen_le_of_gt q s 0 hr h'
  omega

/-- A tuple whose visible head is `<= q` has nonempty `Init`. -/
lemma initList_ne_nil_of_head_le (q : ℕ) {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+)
    (h : pad0 s 0 ≤ q) : initList q s ≠ [] := by
  intro hnil
  have hlen : initLen q s = 0 := by simp [initLen, hnil]
  have hlt : initLen q s < r := by omega
  have hgt := initLen_entry_gt q s hlt
  have hidx : (⟨initLen q s, hlt⟩ : Fin r) = ⟨0, hr⟩ := Fin.ext (by simp [hlen])
  have hval : (s ⟨initLen q s, hlt⟩ : ℕ) = (s ⟨0, hr⟩ : ℕ) :=
    congrArg (fun i : Fin r => (s i : ℕ)) hidx
  have hh : pad0 s 0 = (s ⟨0, hr⟩ : ℕ) := pad0_of_lt s hr
  rw [hval, ← hh] at hgt
  omega

/-- The `a`-members of the level-1 chain descend in the ambient measure `ambNu Lam`. -/
theorem level1_aMember_amb_step (Lam w : ℕ) (hLam : 1 ≤ Lam) {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+)
    (hw : weight r s = w) (hgt : (Nat.card F : ℕ) < (s ⟨0, hr⟩ : ℕ))
    {ι : Type} [Fintype ι] (depa : ι → ℕ) (hdepa : ∀ i, 0 < depa i)
    (ca : ∀ i, Fin (depa i) → ℕ+)
    (hleA : ∀ i, LePad (ca i) (single (qExp F))
      (consVec ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩ (expTail s)) ∧
        ((ca i) ⟨0, hdepa i⟩ : ℕ) < (qExp F : ℕ) +
          ((s ⟨0, hr⟩ : ℕ) - Nat.card F)) :
    ∀ i, ambNu Lam (Nat.card F) w (ca i) < ambNu Lam (Nat.card F) w s := by
  classical
  intro i
  have hwt : weight (depa i) (ca i) = w :=
    (aSide_weight_lt F r hr s hgt depa hdepa ca hleA i).1.trans hw
  have hhd : ((ca i) ⟨0, hdepa i⟩ : ℕ) < (s ⟨0, hr⟩ : ℕ) :=
    (aSide_weight_lt F r hr s hgt depa hdepa ca hleA i).2
  have hdep : r ≤ depa i := level1_aMember_dep_ge F hr s hgt depa hdepa ca hleA i
  have hs1 : pad0 s 0 = (s ⟨0, hr⟩ : ℕ) := pad0_of_lt s hr
  have hilen : initLen (Nat.card F) s = 0 := by
    refine initLen_eq_zero_of_head_gt (Nat.card F) hr s ?_
    rw [hs1]
    exact hgt
  have hivs : initVal (Nat.card F) w s = 0 := by
    refine initVal_eq_zero_of_initList_eq_nil _ _ _ ?_
    exact List.length_eq_zero_iff.mp (by simpa [initLen] using hilen)
  have hpad0s : pad0 s (initLen (Nat.card F) s) = (s ⟨0, hr⟩ : ℕ) := by
    rw [hilen]
    exact hs1
  have hwr : r ≤ w := by have h := weight_ge_depth r s; omega
  have hwm : depa i ≤ w := by have h := weight_ge_depth (depa i) (ca i); omega
  by_cases hlt : psum (ca i) Lam < psum s Lam
  · exact ambNu_lt_of_psum_lt Lam (Nat.card F) w s (ca i) hlt
  · have hle : psum (ca i) Lam ≤ psum s Lam :=
      aSide_order F hr s hgt depa hdepa ca hleA i Lam hLam
    have heq : psum (ca i) Lam = psum s Lam := le_antisymm hle (not_lt.mp hlt)
    rcases lt_or_eq_of_le hdep with hdlt | hdeq
    · exact ambNu_lt_of_depth_gt Lam (Nat.card F) w s (ca i) hwr hwm hdlt hle
    · by_cases hnil : initList (Nat.card F) (ca i) = []
      · have hivm : initVal (Nat.card F) w (ca i) = 0 :=
          initVal_eq_zero_of_initList_eq_nil _ _ _ hnil
        have hilenm : initLen (Nat.card F) (ca i) = 0 := by simp [initLen, hnil]
        have hpadm : pad0 (ca i) (initLen (Nat.card F) (ca i)) = ((ca i) ⟨0, hdepa i⟩ : ℕ) := by
          rw [hilenm]
          exact pad0_of_lt (ca i) (hdepa i)
        refine ambNu_lt_of_entry Lam (Nat.card F) w s (ca i) heq hdeq ?_ ?_
        · rw [hivm, hivs]
        · rw [hpadm, hpad0s]
          exact hhd
      · have hpos : 0 < initVal (Nat.card F) w (ca i) :=
          initVal_pos_of_initList_ne_nil _ _ _ hnil
        exact ambNu_lt_of_initVal Lam (Nat.card F) w s (ca i) hw hwt heq hdeq (by omega)

/-- The `b`-members `1 :: cb j` of the level-1 chain descend in the ambient measure. -/
theorem level1_bMember_amb_step (Lam w : ℕ) (hLam : 1 ≤ Lam) {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+)
    (hw : weight r s = w) (hgt : (Nat.card F : ℕ) < (s ⟨0, hr⟩ : ℕ))
    {ι : Type} [Fintype ι] (depb : ι → ℕ) (hdepb : ∀ j, 0 < depb j)
    (cb : ∀ j, Fin (depb j) → ℕ+)
    (hleB : ∀ j, LePad (cb j) (single (qMinusExp F))
      (consVec ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩ (expTail s))) :
    ∀ j, ambNu Lam (Nat.card F) w (consVec oneExp (cb j)) < ambNu Lam (Nat.card F) w s := by
  classical
  intro j
  have hwt : weight (depb j + 1) (consVec oneExp (cb j)) = w :=
    (head_one_weight F r hr s hgt depb hdepb cb hleB j).trans hw
  have hdep : r ≤ depb j + 1 := level1_bMember_dep_ge F hr s hgt depb hdepb cb hleB j
  have hs1 : pad0 s 0 = (s ⟨0, hr⟩ : ℕ) := pad0_of_lt s hr
  have hilen : initLen (Nat.card F) s = 0 := by
    refine initLen_eq_zero_of_head_gt (Nat.card F) hr s ?_
    rw [hs1]
    exact hgt
  have hivs : initVal (Nat.card F) w s = 0 := by
    refine initVal_eq_zero_of_initList_eq_nil _ _ _ ?_
    exact List.length_eq_zero_iff.mp (by simpa [initLen] using hilen)
  have hwr : r ≤ w := by have h := weight_ge_depth r s; omega
  have hwm : depb j + 1 ≤ w := by
    have h := weight_ge_depth (depb j + 1) (consVec oneExp (cb j)); omega
  by_cases hlt : psum (consVec oneExp (cb j)) Lam < psum s Lam
  · exact ambNu_lt_of_psum_lt Lam (Nat.card F) w s (consVec oneExp (cb j)) hlt
  · have hle : psum (consVec oneExp (cb j)) Lam ≤ psum s Lam :=
      bMember_order F hr s hgt depb hdepb cb hleB j Lam hLam
    have heq : psum (consVec oneExp (cb j)) Lam = psum s Lam :=
      le_antisymm hle (not_lt.mp hlt)
    rcases lt_or_eq_of_le hdep with hdlt | hdeq
    · exact ambNu_lt_of_depth_gt Lam (Nat.card F) w s (consVec oneExp (cb j)) hwr hwm hdlt hle
    · have h00 : 0 < depb j + 1 := by omega
      have hhead : pad0 (consVec oneExp (cb j)) 0 = 1 := by
        rw [pad0_of_lt (consVec oneExp (cb j)) h00]
        exact congrArg (fun t : ℕ+ => (t : ℕ)) (consVec_zero oneExp (cb j))
      have hheadle : pad0 (consVec oneExp (cb j)) 0 ≤ Nat.card F := by
        rw [hhead]
        have h2 : 2 ≤ Nat.card F := card_ge_two F
        omega
      have hne : initList (Nat.card F) (consVec oneExp (cb j)) ≠ [] :=
        initList_ne_nil_of_head_le (Nat.card F) h00 (consVec oneExp (cb j)) hheadle
      have hpos : 0 < initVal (Nat.card F) w (consVec oneExp (cb j)) :=
        initVal_pos_of_initList_ne_nil _ _ _ hne
      exact ambNu_lt_of_initVal Lam (Nat.card F) w s (consVec oneExp (cb j)) hw hwt heq hdeq
        (by omega)

end ZagierHoffmanPositiveChar
