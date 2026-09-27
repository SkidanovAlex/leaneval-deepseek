import Mathlib

/-!
# The Grothendieck group of a commutative monoid

For an additive commutative monoid `M`, the group completion is realised as the localization
of `M` at the top submonoid `⊤`.  It is an additive commutative group `G` equipped with an
additive map `of : M → G` whose kernel is exactly the relation
`a ~ b ↔ ∃ c, a + c = b + c`.
-/

namespace Work.KT

theorem monoid_grothendieck (M : Type) [AddCommMonoid M] :
    ∃ (G : Type) (_ : AddCommGroup G) (f : M → G),
      (∀ a b : M, f (a + b) = f a + f b) ∧
      (∀ a b : M, f a = f b ↔ ∃ c : M, a + c = b + c) := by
  refine ⟨AddLocalization (⊤ : AddSubmonoid M), inferInstance,
    fun a => AddLocalization.mk a (0 : (⊤ : AddSubmonoid M)), ?_, ?_⟩
  · intro a b
    rw [AddLocalization.mk_add]
    simp
  · intro a b
    rw [AddLocalization.mk_eq_mk_iff, AddLocalization.r_iff_exists]
    simp only [Subtype.exists, AddSubmonoid.mem_top, true_and, exists_prop,
      AddSubmonoid.coe_zero, zero_add]
    constructor <;> rintro ⟨c, hc⟩
    · exact ⟨c, by rw [add_comm a c, add_comm b c]; exact hc⟩
    · exact ⟨c, by rw [add_comm c a, add_comm c b]; exact hc⟩

end Work.KT
