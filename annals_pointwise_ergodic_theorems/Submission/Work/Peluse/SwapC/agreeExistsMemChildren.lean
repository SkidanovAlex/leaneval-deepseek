import Mathlib
import Submission.Work.Peluse.SwapC.cprocNodup

namespace Work.Peluse.SwapC

/-- A point in the cell of `m` lies in the cell of one of its two children: the child whose
coordinate `m.dep` is the value `x` takes there. -/
theorem agreeExistsMemChildren {s : ℕ} {m : Work.Peluse.SwapC.CLeaf s} {h : m.dep < s}
    {x : Fin s → Bool} (hx : Work.Peluse.SwapC.Agree x m) :
    ∃ a ∈ m.children h, Work.Peluse.SwapC.Agree x a := by
  cases hb : x ⟨m.dep, h⟩
  · -- `x` takes the value `false` at coordinate `m.dep`: take the first child.
    refine ⟨⟨m.str, m.dep + 1, by omega, fun i hi => ?_⟩, ?_, ?_⟩
    · have hi' : m.dep + 1 ≤ i.val := hi
      exact m.pad i (by omega)
    · rw [CLeaf.children]
      exact List.mem_cons_self ..
    · intro i hi
      have hi' : i.val < m.dep + 1 := hi
      by_cases hlt : i.val < m.dep
      · exact hx i hlt
      · have heq : i.val = m.dep := by omega
        have hie : i = ⟨m.dep, h⟩ := Fin.ext heq
        subst hie
        change m.str ⟨m.dep, h⟩ = x ⟨m.dep, h⟩
        rw [m.pad ⟨m.dep, h⟩ le_rfl]
        exact hb.symm
  · -- `x` takes the value `true` at coordinate `m.dep`: take the second child.
    refine ⟨⟨Function.update m.str ⟨m.dep, h⟩ true, m.dep + 1, by omega, ?_⟩, ?_, ?_⟩
    · intro i hi
      have hi' : m.dep + 1 ≤ i.val := hi
      have hne : i ≠ ⟨m.dep, h⟩ := by
        intro he
        have hv : i.val = m.dep := by simpa using congrArg Fin.val he
        omega
      change Function.update m.str ⟨m.dep, h⟩ true i = false
      rw [Function.update_apply, if_neg hne]
      exact m.pad i (by omega)
    · rw [CLeaf.children]
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · intro i hi
      have hi' : i.val < m.dep + 1 := hi
      change Function.update m.str ⟨m.dep, h⟩ true i = x i
      rw [Function.update_apply]
      by_cases hie : i = ⟨m.dep, h⟩
      · subst hie
        simp [hb]
      · rw [if_neg hie]
        rcases lt_or_eq_of_le (by omega : i.val ≤ m.dep) with hlt | heq
        · exact hx i hlt
        · exact absurd (Fin.ext heq) hie

end Work.Peluse.SwapC
