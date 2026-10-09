import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory CategoryTheory.Limits

namespace Commons.RepresentationTheory.GroupCohomology

/-- Group cohomology of a representation coinduced from the trivial subgroup vanishes in
positive degrees. Indeed, Shapiro's lemma identifies `Hⁿ⁺¹(G, Coind_1^G A)` with
`Hⁿ⁺¹(1, A)`, and the trivial group has cohomological dimension `0`, so its cohomology
vanishes above degree `0`. -/
theorem subsingleton_groupCohomology_coind_bot {G : Type} [Group G] (A : Rep ℤ (⊥ : Subgroup G))
    (n : ℕ) :
    Subsingleton (groupCohomology (Rep.coind (⊥ : Subgroup G).subtype A) (n + 1)) := by
  have hsub : Subsingleton (⊥ : Subgroup G) :=
    ⟨fun a b => Subtype.ext (by rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
  have hz : IsZero (groupCohomology A (n + 1)) :=
    @isZero_groupCohomology_succ_of_subsingleton ℤ (⊥ : Subgroup G) _ _ hsub A n
  have hz' : IsZero (groupCohomology (Rep.coind (⊥ : Subgroup G).subtype A) (n + 1)) :=
    IsZero.of_iso hz (groupCohomology.coindIso A (n + 1))
  exact ModuleCat.subsingleton_of_isZero hz'

end Commons.RepresentationTheory.GroupCohomology