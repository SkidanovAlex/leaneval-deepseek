import Mathlib
import Submission.Work.Peluse.SwapC.cprocNodup

namespace Work.Peluse.SwapC

/-- A point in the cell of a splittable leaf lies in the cell of one of the leaf's two children
(the children split the parent's cell along the `m.dep`-th coordinate). -/
private theorem agreeExistsMemChildren' {s : ℕ} {m : CLeaf s} {h : m.dep < s}
    {x : Fin s → Bool} (hx : Agree x m) :
    ∃ a ∈ m.children h, Agree x a := by
  -- name the two children of `m` explicitly, together with their string/depth
  obtain ⟨c1, c2, hc, hc1str, hc1dep, hc2str, hc2dep⟩ :
      ∃ c1 c2 : CLeaf s, m.children h = [c1, c2] ∧ c1.str = m.str ∧
        c1.dep = m.dep + 1 ∧ c2.str = Function.update m.str ⟨m.dep, h⟩ true ∧
        c2.dep = m.dep + 1 := ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩
  by_cases hb : x ⟨m.dep, h⟩ = true
  · -- the `true` child agrees with `x` when `x` takes the value `true` at the split coordinate
    refine ⟨c2, ?_, ?_⟩
    · rw [hc]; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
    · intro i hi
      rw [hc2dep] at hi
      rw [hc2str]
      have hle : i.val ≤ m.dep := by omega
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hne : i ≠ ⟨m.dep, h⟩ := by
          intro hh
          have hvv : i.val = m.dep := by simpa using congrArg Fin.val hh
          omega
        rw [Function.update_apply, if_neg hne]
        exact hx i hlt
      · have hie : i = ⟨m.dep, h⟩ := Fin.ext heq
        rw [hie, Function.update_self]
        exact hb.symm
  · -- otherwise the `false` child does
    refine ⟨c1, ?_, ?_⟩
    · rw [hc]; exact List.mem_cons_self ..
    · intro i hi
      rw [hc1dep] at hi
      rw [hc1str]
      rw [Bool.not_eq_true] at hb
      have hle : i.val ≤ m.dep := by omega
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hx i hlt
      · have hie : i = ⟨m.dep, h⟩ := Fin.ext heq
        rw [hie, m.pad ⟨m.dep, h⟩ (le_refl _)]
        exact hb.symm

theorem coversSplit {s : ℕ} {P Q : List (Work.Peluse.SwapC.CLeaf s)} {m : Work.Peluse.SwapC.CLeaf s}
    (h : m.dep < s) :
    Work.Peluse.SwapC.Covers (P ++ m :: Q) → Work.Peluse.SwapC.Covers (P ++ m.children h ++ Q) := by
  intro hcov x
  obtain ⟨l, hl, hx⟩ := hcov x
  rcases List.mem_append.mp hl with hlP | hlQ
  · -- the leaf already lies in `P`
    exact ⟨l, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hlP))), hx⟩
  · rcases List.mem_cons.mp hlQ with rfl | hlQ
    · -- the leaf is `m` itself: replace it by a child whose cell contains `x`
      obtain ⟨a, ha, hxa⟩ := agreeExistsMemChildren' hx
      exact ⟨a, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ha))), hxa⟩
    · -- the leaf lies in `Q`
      exact ⟨l, List.mem_append.mpr (Or.inr hlQ), hx⟩

end Work.Peluse.SwapC
