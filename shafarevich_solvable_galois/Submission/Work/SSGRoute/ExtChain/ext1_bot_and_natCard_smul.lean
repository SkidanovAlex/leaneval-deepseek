import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ext_corestriction
import Submission.Work.SSGRoute.ext_one_iso_lattice_cohomology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtChain

/-- Two facts about `Ext¹` with a `ℤ`-lattice as first variable.

(i) For the trivial subgroup `⊥ ≤ G`, `Ext¹_{↥⊥}(K|_⊥, U|_⊥) = 0`: the `Ext`-cohomology
dictionary for a lattice (`Work.SSGRoute.ext_one_iso_lattice_cohomology`, applied to the group
`↥⊥`) identifies it with `Work.GroupCohomology.H1 ↥⊥ (K|_⊥.V →ₗ U|_⊥.V)`, which vanishes because
`⊥` is a subsingleton group (`Work.GroupCohomology.H1_subsingleton_of_subsingleton`).

(ii) Consequently `Nat.card G` kills `Ext¹_G(K,U)`: corestriction from the trivial subgroup
(`Work.SSGRoute.ext_corestriction`, giving `cor ∘ extRes = [G : ⊥] = Nat.card G`) applied to `x`
kills `x` by `Nat.card G`, since `extRes x` lives in the subsingleton of (i). -/
theorem ext1_bot_and_natCard_smul {G : Type} [Group G] [Fintype G]
    (K U : Rep.{0} SSGRoute.PTExt.Coeff G) [Module.Free ℤ K.V] [Module.Finite ℤ K.V] :
    Subsingleton (CategoryTheory.Abelian.Ext.{0}
        (Rep.res (⊥ : Subgroup G).subtype K) (Rep.res (⊥ : Subgroup G).subtype U) 1) ∧
      (∀ x : CategoryTheory.Abelian.Ext.{0} K U 1, Nat.card G • x = 0) := by
  classical
  -- (i) `↥⊥` is a subsingleton group, so the `Ext`-cohomology dictionary for the lattice `K|_⊥`
  -- identifies `Ext¹_{↥⊥}(K|_⊥, U|_⊥)` with the vanishing `H¹(↥⊥, Hom_ℤ(K|_⊥, U|_⊥))`.
  have hsub : Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (Rep.res (⊥ : Subgroup G).subtype K) (Rep.res (⊥ : Subgroup G).subtype U) 1) := by
    obtain ⟨e⟩ := Work.SSGRoute.ext_one_iso_lattice_cohomology (↥(⊥ : Subgroup G))
      (Rep.res (⊥ : Subgroup G).subtype K) (Rep.res (⊥ : Subgroup G).subtype U)
    have h : Subsingleton (Work.GroupCohomology.H1 (↥(⊥ : Subgroup G))
        ((Rep.res (⊥ : Subgroup G).subtype K).V →ₗ[SSGRoute.PTExt.Coeff]
          (Rep.res (⊥ : Subgroup G).subtype U).V)) :=
      Work.GroupCohomology.H1_subsingleton_of_subsingleton
    exact ⟨fun a b => e.injective (h.allEq (e a) (e b))⟩
  refine ⟨hsub, ?_⟩
  -- (ii) corestriction along `⊥ ≤ G` retracts `Ext¹_G(K,U)` onto the classes restricting trivially
  -- to `⊥`, and `cor ∘ extRes` is multiplication by the index `[G : ⊥] = Nat.card G`.
  intro x
  obtain ⟨cor, hcor⟩ := Work.SSGRoute.ext_corestriction (G := G) (⊥ : Subgroup G)
  have h0 : SSGRoute.PTExt.extRes (⊥ : Subgroup G).subtype x = 0 := hsub.allEq _ _
  have h1 : (⊥ : Subgroup G).index • x = 0 := by
    rw [← hcor K U 1 x, h0, map_zero]
  rwa [Subgroup.index_bot] at h1

end Work.SSGRoute.ExtChain
