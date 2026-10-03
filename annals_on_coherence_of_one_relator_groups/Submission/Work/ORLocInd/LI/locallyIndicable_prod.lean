import Mathlib
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.LI.subgroup_locallyIndicable

namespace Work.ORLocInd.LI

/-- **A subgroup with nontrivial image under a homomorphism into a locally indicable group is
indicable.**

If `K ≤ G` is finitely generated and `f : G →* N` maps `K` onto a nontrivial subgroup of a
locally indicable group `N`, then the restricted map `K →* N` is a surjection onto `K.map f`
(its range), so a surjection `K.map f →* Multiplicative ℤ` supplied by local indicability of `N`
pulls back to a surjection out of `K`. -/
lemma indicable_of_map_ne_bot {G N : Type*} [Group G] [Group N] (f : G →* N)
    (hN : Group.LocallyIndicable N) {K : Subgroup G} (hKfg : K.FG) (hmap : K.map f ≠ ⊥) :
    ∃ g : K →* Multiplicative ℤ, Function.Surjective g := by
  obtain ⟨φ, hφ⟩ := hN (K.map f) (subgroup_fg_map f hKfg) hmap
  -- the restriction of `f` to `K`, corestricted to its range `K.map f`, is surjective
  have hmem : ∀ x : K, f x ∈ K.map f := fun x => ⟨x, x.2, rfl⟩
  refine ⟨φ.comp ((f.comp K.subtype).codRestrict (K.map f) hmem), ?_⟩
  intro y
  obtain ⟨z, hz⟩ := hφ y
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp z.2
  refine ⟨⟨w, hw⟩, ?_⟩
  have hz' : ((f.comp K.subtype).codRestrict (K.map f) hmem) ⟨w, hw⟩ = z := Subtype.ext hwz
  rw [MonoidHom.comp_apply, hz', hz]

/-- **Local indicability is preserved by direct products.**

Let `K ≤ G × H` be a nontrivial finitely generated subgroup.  Its images `K.map fst` and
`K.map snd` under the two projections are finitely generated.  They cannot both be trivial, since
their intersection of kernels is the trivial subgroup `⊥ × ⊥ ≤ G × H`; so one of them, say the
image under `fst`, is a nontrivial finitely generated subgroup of the locally indicable group `G`.
The projection `K →* K.map fst` is surjective, and composing it with a surjection
`K.map fst →* Multiplicative ℤ` witnesses that `K` is indicable. -/
theorem locallyIndicable_prod {G H : Type*} [Group G] [Group H]
    (hG : Group.LocallyIndicable G) (hH : Group.LocallyIndicable H) :
    Group.LocallyIndicable (G × H) := by
  intro K hKfg hKne
  by_cases h1 : K.map (MonoidHom.fst G H) = ⊥
  · -- the image under `fst` is trivial, so the image under `snd` is not
    have h2 : K.map (MonoidHom.snd G H) ≠ ⊥ := by
      intro h2bot
      exact hKne ((Subgroup.eq_bot_iff_forall K).mpr fun x hx =>
        Prod.ext ((Subgroup.map_eq_bot_iff K).mp h1 hx)
          ((Subgroup.map_eq_bot_iff K).mp h2bot hx))
    exact indicable_of_map_ne_bot (MonoidHom.snd G H) hH hKfg h2
  · exact indicable_of_map_ne_bot (MonoidHom.fst G H) hG hKfg h1

end Work.ORLocInd.LI
