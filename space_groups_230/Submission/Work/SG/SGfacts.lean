import Submission.Work.SG.SGdata
import Submission.Work.SG.SGinfra

/-! Data facts extracted from the certificate checks in `SGdata`. -/

namespace Work.SG

theorem lenCheck_eq (k : Fin 230) : lenCheck k = true := by
  have h := chkAll k
  simp only [checkData, Bool.and_eq_true] at h
  tauto

theorem oneCheck_eq (k : Fin 230) : oneCheck k = true := by
  have h := chkAll k
  simp only [checkData, Bool.and_eq_true] at h
  tauto

theorem cloCheck_eq (k : Fin 230) : cloCheck k = true := by
  have h := chkAll k
  simp only [checkData, Bool.and_eq_true] at h
  tauto

theorem nodupCheck_eq (k : Fin 230) : nodupCheck k = true := by
  have h := chkAll k
  simp only [checkData, Bool.and_eq_true] at h
  tauto

theorem redCheck_eq (k : Fin 230) : redCheck k = true := by
  have h := chkAll k
  simp only [checkData, Bool.and_eq_true] at h
  tauto

theorem idxCheck_eq' (k : Fin 230) : idxCheck k = true := by
  have h := chkAll k
  simp only [checkData, Bool.and_eq_true] at h
  tauto

theorem detCheck_eq (k : Fin 230) : detCheck k = true := by
  have h := chkAll k
  simp only [checkData, Bool.and_eq_true] at h
  tauto

/-- The raw class index stored for representative `k` is a genuine class index. -/
theorem idxCheck_eq (k : Fin 230) :
    (sgArith k).val = (sgDataList.getD k.val (0, 1, [], 0)).1 := by
  have h := idxCheck_eq' k
  rw [idxCheck] at h
  have hlt : (sgDataList.getD k.val (0, 1, [], 0)).1 < 73 := of_decide_eq_true h
  simp only [sgArith]
  exact Nat.mod_eq_of_lt hlt

/-- The certified table of representative `k` is closed under right multiplication by its
generators. -/
theorem TZclo (k : Fin 230) : ∀ t ∈ TZ k, ∀ g ∈ gensZ k, zMul (sgDen k) t g ∈ TZ k := by
  have h := cloCheck_eq k
  simp only [cloCheck, List.all_eq_true] at h
  intro t ht g hg
  exact of_decide_eq_true (h t ht g hg)

/-- The identity is an entry of the certified table. -/
theorem TZone (k : Fin 230) : zOne ∈ TZ k := by
  have h := oneCheck_eq k
  rw [oneCheck] at h
  exact of_decide_eq_true h

/-- No two entries of the certified table have the same matrix. -/
theorem TZnodup (k : Fin 230) : ((TZ k).map (·.1)).Nodup := by
  have h := nodupCheck_eq k
  rw [nodupCheck] at h
  exact of_decide_eq_true h

/-- All numerators of the certified table are reduced mod the denominator. -/
theorem TZred (k : Fin 230) : ∀ t ∈ TZ k, ∀ x ∈ t.2, 0 ≤ x ∧ x < (sgDen k : ℤ) := by
  have h := redCheck_eq k
  simp only [redCheck, List.all_eq_true] at h
  intro t ht x hx
  exact of_decide_eq_true (h t ht x hx)

/-- All matrices of the certified table are cubical. -/
theorem TZshape (k : Fin 230) : ∀ t ∈ TZ k, (t.1.length = 9 ∧ t.2.length = 3) := by
  have h := lenCheck_eq k
  simp only [lenCheck, List.all_eq_true] at h
  intro t ht
  exact of_decide_eq_true (h t ht)

/-- All matrices of the certified table are unimodular. -/
theorem TZdet (k : Fin 230) : ∀ t ∈ TZ k, det9 t.1 = 1 ∨ det9 t.1 = -1 := by
  have h := detCheck_eq k
  simp only [detCheck, List.all_eq_true] at h
  intro t ht
  exact of_decide_eq_true (h t ht)

theorem sizeCheck_eq (k : Fin 230) : sizeCheck k = true := by
  have h := chkAll k
  simp only [checkData, Bool.and_eq_true] at h
  tauto

/-- The certified table has at most 48 entries. -/
theorem TZsize (k : Fin 230) : (TZ k).length ≤ 48 := by
  have h := sizeCheck_eq k
  rw [sizeCheck] at h
  exact of_decide_eq_true h

theorem chainCheck_eq (k : Fin 230) : chainCheck k = true := by
  have h := chkAll k
  simp only [checkData, Bool.and_eq_true] at h
  tauto

/-- Each table entry is either the identity or a generator-multiple of an earlier entry. -/
theorem TZchain (k : Fin 230) : ∀ i < (TZ k).length,
    (i = 0 ∧ (TZ k).getD i zOne = zOne) ∨
      ∃ p, ∃ g, g ∈ gensZ k ∧ p < i ∧
        (TZ k).getD i zOne = zMul (sgDen k) ((TZ k).getD p zOne) g := by
  have h := chainCheck_eq k
  rw [chainCheck, List.all_eq_true] at h
  intro i hi
  have key := h i (List.mem_range.mpr hi)
  by_cases h0 : i = 0
  · subst h0
    left
    exact ⟨rfl, by simpa using key⟩
  · right
    simp only [h0, ite_false, decide_eq_true_eq] at key
    obtain ⟨hp1, hp2, hz⟩ := key
    refine ⟨((certK k).getD i (0, 0)).1, (gensZ k).getD ((certK k).getD i (0, 0)).2 zOne,
      ?_, hp1, hz.symm⟩
    rw [List.getD_eq_getElem _ _ hp2]
    exact List.getElem_mem ..

/-- Every table entry lies in the integer closure of its generators. -/
theorem TZ_subset_zClose (k : Fin 230) :
    ∀ t, t ∈ TZ k → t ∈ zClose (gensZ k) (sgDen k) 48 [zOne] := by
  have key : ∀ i, i < (TZ k).length →
      (TZ k).getD i zOne ∈ zClose (gensZ k) (sgDen k) (i + 1) [zOne] := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases TZchain k i hi with ⟨h0, hz⟩ | ⟨p, g, hg, hp, hz⟩
      · subst h0
        rw [hz]
        exact mem_zClose_self 1 (List.mem_singleton_self zOne)
      · rw [hz]
        have hp' : (TZ k).getD p zOne ∈ zClose (gensZ k) (sgDen k) i [zOne] :=
          zClose_mono_fuel (Nat.succ_le_of_lt hp) (ih p hp (lt_of_lt_of_le hp hi.le))
        exact mem_zClose_succ.mpr (mem_zF.mpr (Or.inr ⟨_, hp', g, hg, rfl⟩))
  intro t ht
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ht
  have hsz := TZsize k
  have h1 : (TZ k).getD i.val zOne = (TZ k).get i := by
    rw [List.getD_eq_getElem _ _ i.isLt]
    rfl
  rw [← h1]
  exact zClose_mono_fuel (by omega) (key i.val i.isLt)

end Work.SG
