import Submission.ZagierHoffmanProof.StepL126
import Submission.ZagierHoffmanProof.StepM2
set_option autoImplicit false
set_option maxHeartbeats 800000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L127: list-level Init machinery and the type-1 depth bound (SESSION 258t)

(iii) of PLAN SESSION 258s: lift StepL126's entrywise facts to the value-list
level, plus the general `initListAux` append/positivity lemmas used by the
head ≤ q / head > q case split of `maink_mixed_type1_init_bound`.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## generic initListAux list lemmas -/

/-- ★ Head-only `padCode` growth: appending a list whose head is ≥ 1 strictly
increases the code (the remaining entries contribute ≥ 0). -/
lemma padCode_lt_append_cons (B : ℕ) (hB : 1 ≤ B) (xs : List ℕ) (W : ℕ) (c : ℕ) (rest : List ℕ)
    (hlen : xs.length < W) (hc : 1 ≤ c) :
    padCode B W xs < padCode B W (xs ++ (c :: rest)) := by
  have hle : xs.length ≤ W := le_of_lt hlen
  rw [padCode_append B xs W (c :: rest) hle]
  have hW : W - xs.length = (W - xs.length - 1) + 1 := by omega
  have hpos : 0 < padCode B (W - xs.length) (c :: rest) := by
    rw [hW]
    have hstep : padCode B ((W - xs.length - 1) + 1) (c :: rest) =
        c * B ^ (W - xs.length - 1) + padCode B (W - xs.length - 1) rest := rfl
    rw [hstep]
    have hpow : 1 ≤ B ^ (W - xs.length - 1) := Nat.one_le_pow _ B hB
    have h1 : 1 ≤ c * B ^ (W - xs.length - 1) := by
      calc 1 = 1 * 1 := by rw [one_mul]
        _ ≤ c * B ^ (W - xs.length - 1) := Nat.mul_le_mul hc hpow
    omega
  omega

/-- Entries of `valueList` are positive. -/
lemma valueList_pos {r : ℕ} (s : Fin r → ℕ+) : ∀ v ∈ valueList s, 1 ≤ v := by
  intro v hv
  rw [valueList] at hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact (s i).pos

/-! ## the type-1 depth bound and the value-list prefix -/

/-- ★ The depth of a type-1 member is at least the chain level. -/
theorem maink_type1_dep_ge (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA, k ≤ Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) := by
  classical
  intro D Bs Q i₀
  rw [FixedOver.prependList_dep]
  have hBs : Bs.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))
      = (RelData.BCqIter F (k - j - 1) (toData F R0)).depA
          (RelData.iterIdx F (k - j - 1) (toData F R0) i₀) + 1 := by
    dsimp [Bs, ofBstarOver, D]
  have hdepD : (RelData.BCqIter F (k - j - 1) (toData F R0)).depA
      (RelData.iterIdx F (k - j - 1) (toData F R0) i₀) = R0.depA i₀ + (k - j - 1) :=
    RelData.BCqIter_depA_at F (k - j - 1) (toData F R0) i₀
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  rw [hBs, hdepD, hlen]
  have hpos : 0 < R0.depA i₀ := R0.hdepA i₀
  omega

/-- ★ The value-list prefix of a type-1 member agrees with s's, up to k−1
(via StepM2's `valueList_take_eq_of_pad0_eq` + StepL126's entrywise equality +
the depth bound `maink_type1_dep_ge`). -/
theorem maink_type1_valList_take (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA,
      (valueList (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))).take (k - 1)
        = (valueList s).take (k - 1) := by
  classical
  intro D Bs Q i₀
  have hdep := maink_type1_dep_ge F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i₀
  refine valueList_take_eq_of_pad0_eq s
    (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) k hk1 hkr hdep ?_
  intro x hx
  exact (maink_type1_entry_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i₀ x hx).symm

/-- ★ The Init-bound for mixed type-1 members (i₀ ≠ u): the initial value
`initVal q w` weakly increases, and when it is EQUAL the entry at
`initLen q s` strictly drops (the a-head < s⟨k−1⟩).  This is the C2′/C3 pair of
the μ3 measure (PLAN SESSION 258q). -/
theorem maink_mixed_type1_init_bound (r : ℕ) (s : Fin r → ℕ+) (k w j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hw : weight r s = w)
    (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hadm : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hhead : ∀ i : R0.ιA, i ≠ u →
      ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA, i₀ ≠ u →
      initVal (Nat.card F) w s
          ≤ initVal (Nat.card F) w (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) ∧
      (initVal (Nat.card F) w (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))
          = initVal (Nat.card F) w s →
        pad0 (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))
            (initLen (Nat.card F) s) < pad0 s (initLen (Nat.card F) s)) := by
  classical
  intro D Bs Q i₀ hi₀
  set M := Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) with hM
  have hk1r : k - 1 < r := by omega
  have hinit_s : initList (Nat.card F) s = (valueList s).take (k - 1) :=
    initList_eq_take (Nat.card F) s (k - 1) hk1r hadm hbig
  have hlen_s : initLen (Nat.card F) s = k - 1 := by
    rw [initLen, hinit_s, List.length_take, valueList_length]
    omega
  have hdep : k ≤ Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) :=
    maink_type1_dep_ge F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i₀
  have hdepM : k - 1 < Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) := by omega
  have htake : (valueList M).take (k - 1) = (valueList s).take (k - 1) :=
    maink_type1_valList_take F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i₀
  have hpiv : pad0 M (k - 1) = ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) :=
    maink_type1_pivot_eq F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i₀
  have hsplit : valueList M = (valueList M).take (k - 1) ++ (valueList M).drop (k - 1) :=
    (List.take_append_drop (k - 1) (valueList M)).symm
  have hfront_le : ∀ v ∈ (valueList M).take (k - 1), v ≤ Nat.card F := by
    intro v hv
    obtain ⟨i, hi, heq⟩ := List.mem_take_iff_getElem.mp hv
    have hik : i < k - 1 := lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have hid : i < Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) :=
      lt_of_lt_of_le hi (by simpa [valueList_length] using Nat.min_le_right (k - 1) (valueList M).length)
    rw [← heq]
    have hget : (valueList M)[i]'(by simp [valueList_length, hid]) = pad0 M i := by
      rw [valueList_getElem M i hid, pad0_of_lt M hid]
    rw [hget, maink_type1_entry_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i₀ i hik]
    exact hadm i hik
  have hdrop : (valueList M).drop (k - 1)
      = (valueList M)[k - 1]'(by simp [valueList_length, hdepM]) :: (valueList M).drop ((k - 1) + 1) :=
    List.drop_eq_getElem_cons (by simpa [valueList_length] using hdepM)
  have hhead_eq : (valueList M)[k - 1]'(by simp [valueList_length, hdepM])
      = ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) := by
    rw [valueList_getElem M (k - 1) hdepM, ← pad0_of_lt M hdepM]
    exact hpiv
  have hinit_m : initList (Nat.card F) M
      = initList (Nat.card F) s ++ initListAux (Nat.card F) ((valueList M).drop (k - 1)) := by
    calc initList (Nat.card F) M
        = initListAux (Nat.card F) ((valueList M).take (k - 1) ++ (valueList M).drop (k - 1)) := by
            rw [initList]
            exact congrArg (fun l => initListAux (Nat.card F) l) hsplit
      _ = (valueList M).take (k - 1) ++ initListAux (Nat.card F) ((valueList M).drop (k - 1)) :=
            initListAux_append_le (Nat.card F) ((valueList M).take (k - 1)) ((valueList M).drop (k - 1)) hfront_le
      _ = (valueList s).take (k - 1) ++ initListAux (Nat.card F) ((valueList M).drop (k - 1)) := by
            rw [htake]
      _ = initList (Nat.card F) s ++ initListAux (Nat.card F) ((valueList M).drop (k - 1)) := by
            rw [← hinit_s]
  by_cases hpq : ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) ≤ Nat.card F
  · -- the a-head is ≤ q: the init list extends strictly
    have hcons : initListAux (Nat.card F) ((valueList M).drop (k - 1))
        = ((valueList M)[k - 1]'(by simp [valueList_length, hdepM])) ::
            initListAux (Nat.card F) ((valueList M).drop ((k - 1) + 1)) := by
      rw [hdrop]
      have hle : (valueList M)[k - 1]'(by simp [valueList_length, hdepM]) ≤ Nat.card F := by
        rw [hhead_eq]; exact hpq
      rw [initListAux_cons_le (Nat.card F) ((valueList M)[k - 1]'(by simp [valueList_length, hdepM]))
        ((valueList M).drop ((k - 1) + 1)) hle]
    have hwidth : (initList (Nat.card F) s).length < w + 1 := by
      have hwle := initLen_le_weight (Nat.card F) s w hw
      rw [initLen] at hwle
      omega
    have hpiv_pos : 1 ≤ ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) := (R0.cA i₀ ⟨0, R0.hdepA i₀⟩).pos
    have hlt : initVal (Nat.card F) w s < initVal (Nat.card F) w M := by
      rw [initVal, initVal, hinit_m, hcons, hhead_eq]
      exact padCode_lt_append_cons (Nat.card F + 2) (by omega : 1 ≤ Nat.card F + 2)
        (initList (Nat.card F) s) (w + 1) (((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ))
        (initListAux (Nat.card F) ((valueList M).drop ((k - 1) + 1))) hwidth hpiv_pos
    exact ⟨le_of_lt hlt, fun hcon => absurd hcon.symm (ne_of_lt hlt)⟩
  · -- the a-head exceeds q: the init lists coincide, and the pivot entry drops
    have hcons0 : initListAux (Nat.card F) ((valueList M).drop (k - 1)) = [] := by
      rw [hdrop]
      have hgt : Nat.card F < (valueList M)[k - 1]'(by simp [valueList_length, hdepM]) := by
        rw [hhead_eq]; omega
      exact initListAux_cons_gt (Nat.card F) ((valueList M)[k - 1]'(by simp [valueList_length, hdepM]))
        ((valueList M).drop ((k - 1) + 1)) hgt
    have heq_init : initList (Nat.card F) M = initList (Nat.card F) s := by
      rw [hinit_m, hcons0, List.append_nil]
    have heq_val : initVal (Nat.card F) w M = initVal (Nat.card F) w s := by
      rw [initVal, initVal, heq_init]
    refine ⟨le_of_eq heq_val.symm, fun _ => ?_⟩
    rw [hlen_s]
    have hm : pad0 M (k - 1) = ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) := hpiv
    have hs : pad0 s (k - 1) = (s ⟨k - 1, by omega⟩ : ℕ) := pad0_of_lt s hk1r
    rw [hm, hs]
    exact hhead i₀ hi₀

end ZagierHoffmanPositiveChar
