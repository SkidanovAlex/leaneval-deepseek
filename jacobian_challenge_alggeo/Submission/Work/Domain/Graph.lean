/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The closure of the graph of a partial map (area DM, part 1)

This file builds the geometric object that the "domain engine" `Work.Domain` runs on: the
closure of the graph of a partial `S`-map `g : X ⇢ Y`, realised as the scheme-theoretic image of
the graph morphism `g.domain ⟶ X ×_S Y`.

## Main definitions

* `Work.Domain.prod S X Y`: the fibre product `X ×_S Y` of two `S`-schemes.
* `Work.Domain.PartialMap.graphMap`: the graph `g.domain ⟶ X ×_S Y`.
* `Work.Domain.PartialMap.graph`: the scheme-theoretic image (the graph closure).
* `Work.Domain.PartialMap.graphι`: the closed immersion `graph g ⟶ X ×_S Y`.
* `Work.Domain.PartialMap.toGraph`: the dominant morphism `g.domain ⟶ graph g`.
* `Work.Domain.PartialMap.pr₁`, `…pr₂`: the two projections `graph g ⟶ X`, `graph g ⟶ Y`.

## Main results

* `Work.Domain.PartialMap.isProper_pr₁`: `pr₁` is proper (hence closed, hence surjective).
* `Work.Domain.PartialMap.isOpenImmersion_toGraph`: `toGraph` is an open immersion.
* `Work.Domain.PartialMap.toGraph_pr₁`, `…toGraph_pr₂`: the two triangles.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.Domain

/-- The fibre product `X ×_S Y` of two `S`-schemes. -/
noncomputable abbrev prod (S X Y : Scheme.{u}) [X.Over S] [Y.Over S] : Scheme.{u} :=
  pullback (X ↘ S) (Y ↘ S)

namespace PartialMap

variable {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]

/-- The commutativity of the square defining the graph of an `S`-partial map. -/
lemma isOver_comm (S : Scheme.{u}) [X.Over S] [Y.Over S] (g : X.PartialMap Y) [g.IsOver S] :
    g.domain.ι ≫ (X ↘ S) = g.hom ≫ (Y ↘ S) :=
  ((Scheme.PartialMap.isOver_iff (S := S)).mp ‹g.IsOver S›).symm

/-- The graph of an `S`-partial map `g : X ⇢ Y`, as a morphism `g.domain ⟶ X ×_S Y`. -/
noncomputable def graphMap (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] : g.domain.toScheme ⟶ prod S X Y :=
  pullback.lift g.domain.ι g.hom (isOver_comm S g)

/-- The closure of the graph of `g`: the scheme-theoretic image of `graphMap`. -/
noncomputable abbrev graph (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] : Scheme.{u} := (graphMap S g).image

/-- The closed immersion of the graph closure into `X ×_S Y`. -/
noncomputable abbrev graphι (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] : graph S g ⟶ prod S X Y :=
  (graphMap S g).imageι

/-- The morphism from the domain of `g` onto the graph closure. -/
noncomputable abbrev toGraph (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] : g.domain.toScheme ⟶ graph S g :=
  (graphMap S g).toImage

/-- The first projection from the graph closure to `X`. -/
noncomputable abbrev pr₁ (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] : graph S g ⟶ X :=
  graphι S g ≫ pullback.fst (X ↘ S) (Y ↘ S)

/-- The second projection from the graph closure to `Y`. -/
noncomputable abbrev pr₂ (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] : graph S g ⟶ Y :=
  graphι S g ≫ pullback.snd (X ↘ S) (Y ↘ S)

instance (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] : IsClosedImmersion (graphι S g) := inferInstance

lemma toGraph_graphι (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] :
    toGraph S g ≫ graphι S g = graphMap S g := Scheme.Hom.toImage_imageι _

lemma toGraph_pr₁ (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] : toGraph S g ≫ pr₁ S g = g.domain.ι := by
  rw [pr₁, ← Category.assoc, toGraph_graphι, graphMap, pullback.lift_fst]

lemma toGraph_pr₂ (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] : toGraph S g ≫ pr₂ S g = g.hom := by
  rw [pr₂, ← Category.assoc, toGraph_graphι, graphMap, pullback.lift_snd]

instance (S : Scheme.{u}) [X.Over S] [Y.Over S] (g : X.PartialMap Y) [g.IsOver S]
    [IsProper (Y ↘ S)] : IsProper (pr₁ S g) := by
  rw [pr₁]
  infer_instance

/-! ## The graph map is an immersion, and quasi-compact

We factor `graphMap` as a closed immersion (the graph inside `g.domain ×_S Y`) followed by the
open immersion `g.domain ×_S Y ⟶ X ×_S Y`.  This exhibits `graphMap` as an immersion; and
(assuming `X` is locally Noetherian) it is quasi-compact, because open immersions into a locally
Noetherian scheme are quasi-compact. -/

/-- The intermediate scheme `g.domain ×_X (X ×_S Y) ≅ g.domain ×_S Y`. -/
noncomputable abbrev graphPU (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] : Scheme.{u} :=
  pullback (g.hom ≫ (Y ↘ S)) (Y ↘ S)

/-- The graph of `g` inside `g.domain ×_S Y` (a closed immersion). -/
noncomputable abbrev graphUToPU (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] : g.domain.toScheme ⟶ graphPU S g :=
  pullback.lift (𝟙 g.domain.toScheme) g.hom (Category.id_comp (g.hom ≫ (Y ↘ S)))

instance (S : Scheme.{u}) [X.Over S] [Y.Over S] (g : X.PartialMap Y) [g.IsOver S]
    [IsSeparated (Y ↘ S)] : IsClosedImmersion (graphUToPU S g) := inferInstance

instance (S : Scheme.{u}) [X.Over S] [Y.Over S] (g : X.PartialMap Y) [g.IsOver S]
    [IsSeparated (Y ↘ S)] : IsImmersion (graphUToPU S g) := inferInstance

instance (S : Scheme.{u}) [X.Over S] [Y.Over S] (g : X.PartialMap Y) [g.IsOver S]
    [IsSeparated (Y ↘ S)] : QuasiCompact (graphUToPU S g) := inferInstance

/-- The open immersion `g.domain ×_S Y ⟶ X ×_S Y`. -/
noncomputable abbrev PUToP (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] : graphPU S g ⟶ prod S X Y :=
  (pullback.congrHom (isOver_comm S g).symm rfl).hom ≫
    (pullbackRightPullbackFstIso (X ↘ S) (Y ↘ S) g.domain.ι).inv ≫
      pullback.snd g.domain.ι (pullback.fst (X ↘ S) (Y ↘ S))

instance (S : Scheme.{u}) [X.Over S] [Y.Over S] (g : X.PartialMap Y) [g.IsOver S] :
    IsOpenImmersion (PUToP S g) := by
  rw [PUToP]
  infer_instance

/-- The first component of `PUToP`. -/
lemma PUToP_fst (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] :
    PUToP S g ≫ pullback.fst (X ↘ S) (Y ↘ S) =
      pullback.fst (g.hom ≫ (Y ↘ S)) (Y ↘ S) ≫ g.domain.ι := by
  have key : (pullback.congrHom (isOver_comm S g).symm rfl).hom ≫
      pullback.fst (g.domain.ι ≫ (X ↘ S)) (Y ↘ S) =
      pullback.fst (g.hom ≫ (Y ↘ S)) (Y ↘ S) := by
    rw [pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id]
  rw [PUToP, Category.assoc, Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst,
    ← Category.assoc, key]

/-- The second component of `PUToP`. -/
lemma PUToP_snd (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] :
    PUToP S g ≫ pullback.snd (X ↘ S) (Y ↘ S) =
      pullback.snd (g.hom ≫ (Y ↘ S)) (Y ↘ S) := by
  have key : (pullback.congrHom (isOver_comm S g).symm rfl).hom ≫
      pullback.snd (g.domain.ι ≫ (X ↘ S)) (Y ↘ S) =
      pullback.snd (g.hom ≫ (Y ↘ S)) (Y ↘ S) := by
    rw [pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id]
  rw [PUToP, Category.assoc, Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd, key]

lemma graphUToPU_PUToP (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] :
    graphUToPU S g ≫ PUToP S g = graphMap S g := by
  apply pullback.hom_ext
  · rw [Category.assoc, PUToP_fst, ← Category.assoc, pullback.lift_fst, Category.id_comp]
    rw [graphMap, pullback.lift_fst]
  · rw [Category.assoc, PUToP_snd, pullback.lift_snd]
    rw [graphMap, pullback.lift_snd]

instance (S : Scheme.{u}) [X.Over S] [Y.Over S] (g : X.PartialMap Y) [g.IsOver S]
    [IsSeparated (Y ↘ S)] : IsImmersion (graphMap S g) := by
  rw [← graphUToPU_PUToP S g]
  infer_instance

instance (S : Scheme.{u}) [X.Over S] [Y.Over S] (g : X.PartialMap Y) [g.IsOver S]
    [IsLocallyNoetherian X] [IsSeparated (Y ↘ S)] : QuasiCompact (graphMap S g) := by
  rw [← graphUToPU_PUToP S g]
  infer_instance

instance (S : Scheme.{u}) [X.Over S] [Y.Over S] (g : X.PartialMap Y) [g.IsOver S]
    [IsLocallyNoetherian X] [IsSeparated (Y ↘ S)] : IsOpenImmersion (toGraph S g) := by
  rw [toGraph]
  infer_instance

instance (S : Scheme.{u}) [X.Over S] [Y.Over S] (g : X.PartialMap Y) [g.IsOver S]
    [QuasiCompact (graphMap S g)] : IsDominant (toGraph S g) := by
  rw [toGraph]
  infer_instance


/-! ## The generic point of the graph closure

The graph closure carries a canonical point, the image of the generic point of the domain of `g`.
For an open immersion with dense image this point is the generic point of the graph closure; we
only need the consequence that it specialises to every point, which lets us restrict functions
from `O_{graph,γ}` to the function field of the graph. -/

/-- The underlying set of the graph closure is the closure of the graph. -/
lemma range_graphι (S : Scheme.{u}) [X.Over S] [Y.Over S] (g : X.PartialMap Y) [g.IsOver S]
    [IsLocallyNoetherian X] [IsSeparated (Y ↘ S)] :
    Set.range (graphι S g) = closure (Set.range (graphMap S g)) := by
  have h1 : Set.range ⇑(Scheme.Hom.imageι (graphMap S g)) =
      (Scheme.Hom.ker (graphMap S g)).support := by simp
  rw [graphι, h1, Scheme.Hom.support_ker]

/-- Every point of the graph closure is a specialisation of the image of the generic point of the
domain of `g`. -/
lemma specializes_toGraph_genericPoint (S : Scheme.{u}) [X.Over S] [Y.Over S]
    (g : X.PartialMap Y) [g.IsOver S] [QuasiCompact (graphMap S g)]
    [IrreducibleSpace g.domain.toScheme] (γ : graph S g) :
    Specializes (toGraph S g (genericPoint g.domain.toScheme)) γ := by
  rw [specializes_iff_forall_open]
  intro s hs hγ
  have hd : DenseRange ⇑(toGraph S g) := IsDominant.denseRange
  obtain ⟨u, hu⟩ : ∃ u, toGraph S g u ∈ s := by
    by_contra h
    have hsub : Set.range ⇑(toGraph S g) ⊆ sᶜ := by
      rintro _ ⟨u, rfl⟩
      simp only [Set.mem_compl_iff]
      exact fun hmem => h ⟨u, hmem⟩
    have hclosed : IsClosed (sᶜ) := hs.isClosed_compl
    have : closure (Set.range ⇑(toGraph S g)) ⊆ sᶜ := closure_minimal hsub hclosed
    rw [denseRange_iff_closure_range.mp hd] at this
    exact (this trivial) hγ
  have h1 : (genericPoint g.domain.toScheme) ⤳ u := (genericPoint_spec _).specializes trivial
  exact h1.mem_open (hs.preimage (toGraph S g).continuous) hu

end PartialMap

end Work.Domain
