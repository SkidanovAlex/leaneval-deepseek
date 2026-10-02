import Mathlib
import Submission.Work.ThomBordism.h0SignUnit
import Submission.Work.ThomBordism.localThomMap_cup_general

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.ThomBordism

theorem localThom_unit_relation {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) {P : Set B}
    (τ τ' : Work.Thom.PieceCoh Z P n)
    (hτ : ∀ k : ℕ, Function.Bijective (Work.Thom.localThomMap Z n P τ k))
    (hτ' : ∀ k : ℕ, Function.Bijective (Work.Thom.localThomMap Z n P τ' k)) :
    ∃ u : Work.Thom.Coh ℤ 0 ↥P,
      ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥P)) 0 0) u u)
        = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥P)) ∧
      τ' = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n P τ 0 u) := by
  classical
  have hcast : ((Nat.zero_add n) ▸ ((Nat.zero_add n).symm ▸ τ') :
      Work.Thom.PieceCoh Z P n) = τ' := by
    rw [Work.Thom.eqRec_comp (P := fun t => Work.Thom.PieceCoh Z P t)
      (a := n) (b := 0 + n) (c := n) (Nat.zero_add n).symm (Nat.zero_add n) τ']
  obtain ⟨u, hu⟩ := (hτ 0).surjective ((Nat.zero_add n).symm ▸ τ')
  have hτ'eq : τ' = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n P τ 0 u) := by
    rw [hu]
    exact hcast.symm
  have hrel : ∀ y : Work.Thom.Coh ℤ 0 ↥P,
      Work.Thom.localThomMap Z n P τ' 0 y
        = Work.Thom.localThomMap Z n P τ 0
            ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥P)) 0 0) y u) := by
    intro y
    rw [hτ'eq]
    exact Work.ThomBordism.localThomMap_cup_general Z n P τ u 0 y
  have hunit : ∃ y : Work.Thom.Coh ℤ 0 ↥P,
      (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥P)) 0 0) y u
        = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥P)) := by
    obtain ⟨y, hy⟩ := (hτ' 0).surjective (Work.Thom.localThomMap Z n P τ 0
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥P))))
    exact ⟨y, (hτ 0).injective (by rw [← hrel y, hy])⟩
  refine ⟨u, ?_, hτ'eq⟩
  obtain ⟨y, hyu⟩ := hunit
  have hpm : ∀ p : ↥P, Work.Thom.ptEv p u = 1 ∨ Work.Thom.ptEv p u = -1 := by
    intro p
    have h1 := Work.Thom.ptEv_cup p y u
    rw [hyu, Work.Thom.ptEv_one] at h1
    exact Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact h1.symm)
  apply Work.Thom.ptEv_ext
  intro p
  rw [Work.Thom.ptEv_cup, Work.Thom.ptEv_one]
  rcases hpm p with h | h <;> rw [h] <;> norm_num

end Work.ThomBordism
