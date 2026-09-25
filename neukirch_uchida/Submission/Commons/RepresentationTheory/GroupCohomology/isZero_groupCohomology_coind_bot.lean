import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

namespace Commons.RepresentationTheory.GroupCohomology

theorem isZero_groupCohomology_coind_bot {k : Type} [CommRing k] {G : Type} [Group G] (A : Rep k (⊥ : Subgroup G)) (n : ℕ) : CategoryTheory.Limits.IsZero (groupCohomology (Rep.coind (⊥ : Subgroup G).subtype A) (n + 1)) := by
  have hsub : Subsingleton (⊥ : Subgroup G) :=
    ⟨fun a b => Subtype.ext (by rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
  have hz : CategoryTheory.Limits.IsZero (groupCohomology A (n + 1)) :=
    @isZero_groupCohomology_succ_of_subsingleton k (⊥ : Subgroup G) _ _ hsub A n
  exact CategoryTheory.Limits.IsZero.of_iso hz (groupCohomology.coindIso A (n + 1))

end Commons.RepresentationTheory.GroupCohomology
