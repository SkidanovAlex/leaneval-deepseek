import Mathlib
import Submission.Work.ORHughesFree.Tree.Log

set_option autoImplicit false

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- Characterization of `log`: if `c` is an element of the family of `z` which dominates the whole
family, then `log z = some c`. -/
theorem log_eq_some_of_max {z c : Tree} (hc : c ∈ fam z)
    (hmax : ∀ a ∈ fam z, Tree.le a c) : log z = some c := by
  have hz : z ≠ 0 := by
    intro h
    rw [h, fam_zero] at hc
    simp at hc
  obtain ⟨d, hd⟩ := (log_spec z).2.2 hz
  obtain ⟨hdmem, hdmax⟩ := (log_spec z).2.1 d hd
  have hdc : Tree.le d c := hmax d hdmem
  have hcd : Tree.le c d := hdmax c hc
  rw [hd]
  exact congrArg some (Tree.le_antisymm hdc hcd)

/-- The maximum of two optional trees, when the first is below the second. -/
theorem omax_some_some_of_le {a b : Tree} (h : Tree.le a b) :
    omax (some a) (some b) = some b := by
  classical
  simp only [omax]
  rw [if_pos h]

/-- The maximum of two optional trees, when the first is not below the second. -/
theorem omax_some_some_of_not_le {a b : Tree} (h : ¬ Tree.le a b) :
    omax (some a) (some b) = some a := by
  classical
  simp only [omax]
  rw [if_neg h]

theorem log_add {x y : Work.ORHughesFree.Tree} (hx : x ≠ 0) (hy : y ≠ 0) :
    Work.ORHughesFree.Tree.log (x + y) =
      Work.ORHughesFree.Tree.omax (Work.ORHughesFree.Tree.log x)
        (Work.ORHughesFree.Tree.log y) := by
  obtain ⟨a, ha⟩ := (log_spec x).2.2 hx
  obtain ⟨b, hb⟩ := (log_spec y).2.2 hy
  obtain ⟨hmema, hmaxa⟩ := (log_spec x).2.1 a ha
  obtain ⟨hmemb, hmaxb⟩ := (log_spec y).2.1 b hb
  rw [ha, hb]
  by_cases h : Tree.le a b
  · rw [omax_some_some_of_le h]
    refine log_eq_some_of_max ?_ ?_
    · rw [Tree.fam_add]
      exact Multiset.mem_add.mpr (Or.inr hmemb)
    · intro c hc
      rw [Tree.fam_add] at hc
      rcases Multiset.mem_add.mp hc with hcx | hcy
      · exact Tree.le_trans (hmaxa c hcx) h
      · exact hmaxb c hcy
  · rw [omax_some_some_of_not_le h]
    have hba : Tree.le b a := (Tree.le_total a b).resolve_left h
    refine log_eq_some_of_max ?_ ?_
    · rw [Tree.fam_add]
      exact Multiset.mem_add.mpr (Or.inl hmema)
    · intro c hc
      rw [Tree.fam_add] at hc
      rcases Multiset.mem_add.mp hc with hcx | hcy
      · exact hmaxa c hcx
      · exact Tree.le_trans (hmaxb c hcy) hba

end Work.ORHughesFree.Tree
