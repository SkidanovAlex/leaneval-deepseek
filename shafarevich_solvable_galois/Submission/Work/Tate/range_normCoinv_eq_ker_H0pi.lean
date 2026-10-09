import Mathlib
import Submission.Work.Tate.Coinvariants
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- The norm `A_G → A^G` factors the norm `A → A^G` through the quotient `A → A_G`; since the
quotient map is surjective, the two maps have the same range. -/
theorem range_normCoinv_eq_range_normToFixed {G : Type*} {A : Type*} [Group G]
    [AddCommGroup A] [DistribMulAction G A] [Fintype G] :
    (normCoinv G A).range = (normToFixed G A).range := by
  have hkey : ∀ a : A, normCoinv G A (coinvMk G A a) = normToFixed G A a := by
    intro a; apply Subtype.ext; rw [normCoinv_apply, normToFixed_apply]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective (augmentation G A) x
    refine ⟨a, ?_⟩
    rw [← ha]
    exact (hkey a).symm
  · rintro _ ⟨a, rfl⟩
    exact ⟨coinvMk G A a, hkey a⟩

theorem range_normCoinv_eq_ker_H0pi {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] :
    (Work.Tate.normCoinv G A).range = (Work.Tate.H0π G A).ker := by
  rw [range_normCoinv_eq_range_normToFixed]
  exact (QuotientAddGroup.ker_mk' (normToFixed G A).range).symm

end Work.Tate
