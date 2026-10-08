import Mathlib
import Submission.Work.Clifford.Classes
import Submission.Work.Skeleton.eq_one_of_isConj_inv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Clifford

/-- In a finite group of odd order, every real conjugacy class is the class of the
identity. -/
theorem eq_mk_one_of_isRealClass {G : Type*} [Group G] [Fintype G]
    (hG : Odd (Nat.card G)) {C : ConjClasses G} (hC : IsRealClass C) :
    C = ConjClasses.mk (1 : G) := by
  obtain ⟨g, hg⟩ := (ConjClasses.mk_surjective C : ∃ g : G, ConjClasses.mk g = C)
  rw [← hg] at hC ⊢
  have h : IsConj g g⁻¹ := isRealClass_mk_iff.mp hC
  rw [Work.Skeleton.eq_one_of_isConj_inv hG h]

theorem card_realClasses_eq_one_of_odd {G : Type*} [Group G] [Fintype G]
    (hG : Odd (Nat.card G)) :
    Nat.card {C : ConjClasses G // Work.Clifford.IsRealClass C} = 1 := by
  have hne : Nonempty {C : ConjClasses G // Work.Clifford.IsRealClass C} :=
    ⟨⟨ConjClasses.mk 1, isRealClass_one⟩⟩
  have hsub : Subsingleton {C : ConjClasses G // Work.Clifford.IsRealClass C} :=
    ⟨fun a b => Subtype.ext (by
      rw [eq_mk_one_of_isRealClass hG a.2, eq_mk_one_of_isRealClass hG b.2])⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, hne⟩

end Work.Clifford
