import Mathlib
import Submission.Work.Tate.Coinvariants
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

open scoped BigOperators

/-- The quotient map `A → A_G` onto the coinvariants is surjective. -/
theorem coinvMk_surjective {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] : Function.Surjective (coinvMk G A) :=
  QuotientAddGroup.mk'_surjective (augmentation G A)

theorem range_Hm1ToCoinv_eq_ker_normCoinv {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] :
    (Work.Tate.Hm1ToCoinv G A).range = (Work.Tate.normCoinv G A).ker := by
  ext x
  constructor
  · intro hx
    rw [AddMonoidHom.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨a, rfl⟩ := Hm1π_surjective y
    rw [AddMonoidHom.mem_ker, Hm1ToCoinv_apply]
    exact Subtype.ext (by rw [normCoinv_apply]; exact a.2)
  · intro hx
    rw [AddMonoidHom.mem_ker] at hx
    obtain ⟨a, rfl⟩ := coinvMk_surjective x
    rw [AddMonoidHom.mem_range]
    have ha : norm G A a = 0 := by
      have hcoe : (normCoinv G A (coinvMk G A a) : A) = 0 := by rw [hx]; rfl
      rwa [normCoinv_apply] at hcoe
    exact ⟨Hm1π G A ⟨a, ha⟩, by rw [Hm1ToCoinv_apply]⟩

end Work.Tate
