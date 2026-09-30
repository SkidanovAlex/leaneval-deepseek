import Mathlib
import Submission.Work.Domain.Graph
import Submission.Work.Domain.Theta

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry Set

namespace Work.Domain.Engine

/-- The domain of definition of a partial map, as a scheme, is irreducible as soon as the
ambient scheme is: its underlying open is nonempty (it is dense) and open, and an open subset
of an irreducible space is irreducible. -/
lemma irreducibleSpace_toScheme_domain {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) : IrreducibleSpace ↥g.domain.toScheme := by
  have hne : (g.domain : Set X).Nonempty := g.dense_domain.nonempty
  have hpre : IsPreirreducible (univ : Set X) := PreirreducibleSpace.isPreirreducible_univ
  have hirr : IsIrreducible (g.domain : Set X) :=
    hpre.subset_irreducible hne g.domain.2 (fun _ => id) (Set.subset_univ _)
  exact isIrreducible_iff_irreducibleSpace.mp hirr

/-- `pr₁ : Γ → X` is surjective: it is proper (hence closed) and its image contains the dense
open `g.domain`. -/
lemma surjective_pr₁ {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsIntegral X] [IsLocallyNoetherian X]
    [IsProper (Work.Domain.overHom S Y)]
    (g : X.PartialMap Y) [hg : g.IsOver S] : Surjective (PartialMap.pr₁ S g) := by
  have hclosed : IsClosed (Set.range ⇑(PartialMap.pr₁ S g)) :=
    (Scheme.Hom.isClosedMap (PartialMap.pr₁ S g)).isClosed_range
  have hdense : Dense (Set.range ⇑(PartialMap.pr₁ S g)) := by
    have hsub : Set.range ⇑(PartialMap.toGraph S g ≫ PartialMap.pr₁ S g) ⊆
        Set.range ⇑(PartialMap.pr₁ S g) := by
      rintro _ ⟨u, rfl⟩
      exact ⟨PartialMap.toGraph S g u, rfl⟩
    have hd : Dense (Set.range ⇑(PartialMap.toGraph S g ≫ PartialMap.pr₁ S g)) := by
      rw [PartialMap.toGraph_pr₁]
      simpa using g.dense_domain
    exact hd.mono hsub
  refine ⟨?_⟩
  rw [← Set.range_eq_univ]
  exact hclosed.closure_eq.symm.trans (dense_iff_closure_eq.mp hdense)

/-- The generic point of the graph closure is mapped by `pr₁` to the generic point of `X`. -/
lemma pr₁_genericPoint {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsIntegral X] [IsLocallyNoetherian X]
    [IsProper (Work.Domain.overHom S Y)]
    (g : X.PartialMap Y) [hg : g.IsOver S] [hgint : IsIntegral (PartialMap.graph S g)] :
    PartialMap.pr₁ S g (genericPoint (PartialMap.graph S g)) = genericPoint X := by
  have hsurj : Surjective (PartialMap.pr₁ S g) := surjective_pr₁ g
  have hγ : PartialMap.pr₁ S g (genericPoint (PartialMap.graph S g)) ⤳ genericPoint X := by
    obtain ⟨γ', hγ'⟩ := hsurj.surj (genericPoint X)
    have hspec : (genericPoint (PartialMap.graph S g)) ⤳ γ' :=
      (genericPoint_spec _).specializes trivial
    have h2 : PartialMap.pr₁ S g (genericPoint (PartialMap.graph S g)) ⤳
        PartialMap.pr₁ S g γ' := hspec.map (PartialMap.pr₁ S g).continuous
    rw [hγ'] at h2
    exact h2
  exact Inseparable.eq (hγ.antisymm ((genericPoint_spec X).specializes trivial))

/-- The stalk map of `pr₁` at the generic point of the graph closure is an isomorphism: it is a
composite of the (iso) stalk maps of the open immersions `toGraph : g.domain ⟶ Γ` and
`g.domain.ι : g.domain ⟶ X`. -/
lemma isIso_stalkMap_pr₁_genericPoint {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsIntegral X] [IsLocallyNoetherian X]
    [IsProper (Work.Domain.overHom S Y)]
    (g : X.PartialMap Y) [hg : g.IsOver S] [hgint : IsIntegral (PartialMap.graph S g)] :
    IsIso ((PartialMap.pr₁ S g).stalkMap (genericPoint (PartialMap.graph S g))) := by
  haveI : IrreducibleSpace ↥g.domain.toScheme := irreducibleSpace_toScheme_domain g
  have ht : PartialMap.toGraph S g (genericPoint g.domain.toScheme) =
      genericPoint (PartialMap.graph S g) :=
    genericPoint_eq_of_isOpenImmersion (PartialMap.toGraph S g)
  have hpr : IsIso ((PartialMap.pr₁ S g).stalkMap
      (PartialMap.toGraph S g (genericPoint g.domain.toScheme))) := by
    have h1 : IsIso ((PartialMap.toGraph S g ≫ PartialMap.pr₁ S g).stalkMap
        (genericPoint g.domain.toScheme)) := by
      rw [Scheme.Hom.stalkMap_congr_hom (PartialMap.toGraph S g ≫ PartialMap.pr₁ S g)
        (g.domain.ι) (PartialMap.toGraph_pr₁ S g) (genericPoint g.domain.toScheme)]
      infer_instance
    rw [Scheme.Hom.stalkMap_comp] at h1
    haveI : IsIso ((PartialMap.pr₁ S g).stalkMap
        (PartialMap.toGraph S g (genericPoint g.domain.toScheme)) ≫
        (PartialMap.toGraph S g).stalkMap (genericPoint g.domain.toScheme)) := h1
    exact IsIso.of_isIso_comp_right
      ((PartialMap.pr₁ S g).stalkMap (PartialMap.toGraph S g (genericPoint g.domain.toScheme)))
      ((PartialMap.toGraph S g).stalkMap (genericPoint g.domain.toScheme))
  rw [← ht]
  exact hpr

theorem pr1_genericPoint_facts {S X Y : AlgebraicGeometry.Scheme} [X.Over S] [Y.Over S]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    [AlgebraicGeometry.IsProper (Work.Domain.overHom S Y)]
    (g : AlgebraicGeometry.Scheme.PartialMap X Y)
    [hg : AlgebraicGeometry.Scheme.PartialMap.IsOver S g]
    [hgint : AlgebraicGeometry.IsIntegral (Work.Domain.PartialMap.graph S g)] :
    AlgebraicGeometry.Surjective (Work.Domain.PartialMap.pr₁ S g) ∧
      Work.Domain.PartialMap.pr₁ S g (genericPoint (Work.Domain.PartialMap.graph S g)) =
        genericPoint X ∧
      CategoryTheory.IsIso ((Work.Domain.PartialMap.pr₁ S g).stalkMap
        (genericPoint (Work.Domain.PartialMap.graph S g))) :=
  ⟨surjective_pr₁ g, pr₁_genericPoint g, isIso_stalkMap_pr₁_genericPoint g⟩

end Work.Domain.Engine
