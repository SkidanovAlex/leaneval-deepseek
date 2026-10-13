import Mathlib
import Submission.Work.DSG2.Setup
import Submission.Work.DSG2.closure_range_comp_eq_of_denseRange

/-!
# DSG2: the projections `pi : Z ⟶ Zi` are surjective

For Chow data `D` we prove that `ChowSetup.pi D i : Z D ⟶ Zi D i` is surjective.  The argument is
purely topological: `pi` is proper, hence a closed map, so its image is closed; on the other hand
`qi = pi ≫ Ziι = Zι ≫ p i` and the `i`-th projection of the scheme-theoretic image `Z` of the
product map `jU` meets every point of `Zi = image (j i)` because the `i`-th component of `jU` is
`j i` precomposed with the embedding `U0 ⊆ U i`, whose image is dense.

The two ingredients are

* `range_imageι_eq_closure_range` : the underlying set of the scheme-theoretic image of a
  quasi-compact morphism `g` is the closure of the range of `g`;
* `image_closure_eq_of_isClosedMap` : for a closed continuous map, the image of a closure is the
  closure of the image.
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace Work.DSG2

/-- The image of the closure of a set under a closed continuous map is the closure of the image. -/
lemma image_closure_eq_of_isClosedMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {g : X → Y} (hg : Continuous g) (hcl : IsClosedMap g) (s : Set X) :
    g '' closure s = closure (g '' s) := by
  refine Set.Subset.antisymm (image_closure_subset_closure_image hg) ?_
  exact (hcl (closure s) isClosed_closure).closure_subset_iff.mpr (Set.image_mono subset_closure)

/-- The underlying set of the scheme-theoretic image of a quasi-compact morphism is the closure of
the range of the morphism. -/
lemma range_imageι_eq_closure_range {X Y : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g] :
    Set.range ⇑(g.imageι) = closure (Set.range ⇑g) := by
  have h1 : Set.range ⇑(g.imageι) = ↑(g.ker).support :=
    Scheme.IdealSheafData.range_subschemeι g.ker
  rw [h1, Scheme.Hom.support_ker]

/-- The range of a composite of scheme morphisms. -/
lemma range_comp_scheme {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) :
    Set.range ⇑(g ≫ h) = ⇑h '' Set.range ⇑g := by
  rw [show ⇑(g ≫ h) = ⇑h ∘ ⇑g from funext fun x => Scheme.Hom.comp_apply g h x,
    Set.range_comp]

/-- The open subscheme `U0` of a Noetherian scheme is a Noetherian topological space. -/
lemma noetherianSpace_opens {A : Type u} [CommRing A] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of A)} (D : ChowSetup A X f) :
    TopologicalSpace.NoetherianSpace (D.U0 : Scheme.{u}) := by
  haveI : IsNoetherian X := D.hNoeth
  haveI : TopologicalSpace.NoetherianSpace X := inferInstance
  exact (Scheme.Opens.ι (D.U0 : X.Opens)).isOpenEmbedding.isEmbedding.isInducing.noetherianSpace

/-- The inclusion `U0 ↪ U i` of the common refinement into a member of the cover has dense range:
`U0` is dense in `X` and `U i` is open. -/
lemma denseRange_homOfLE {A : Type u} [CommRing A] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of A)} (D : ChowSetup A X f) (i : Fin D.m) :
    DenseRange ⇑(X.homOfLE (D.hU0le i)) := by
  have hd : DenseRange ⇑(Scheme.Opens.ι (D.U0 : X.Opens)) := by
    rw [denseRange_iff_closure_range, Scheme.Opens.range_ι]
    exact Dense.closure_eq D.hU0dense
  -- `U0.ι` factors as `(U0 ↪ U i) ≫ (U i).ι`
  have hfun : ⇑(Scheme.Opens.ι (D.U0 : X.Opens)) =
      ⇑(Scheme.Opens.ι (D.U i : X.Opens)) ∘ ⇑(X.homOfLE (D.hU0le i)) := by
    funext x
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  have hemb : Topology.IsEmbedding ⇑(Scheme.Opens.ι (D.U i : X.Opens)) :=
    (Scheme.Opens.ι (D.U i : X.Opens)).isOpenEmbedding.isEmbedding
  have key := hemb.closure_eq_preimage_closure_image (Set.range ⇑(X.homOfLE (D.hU0le i)))
  have hrange : ⇑(Scheme.Opens.ι (D.U i : X.Opens)) '' Set.range ⇑(X.homOfLE (D.hU0le i)) =
      Set.range ⇑(Scheme.Opens.ι (D.U0 : X.Opens)) := by
    rw [← Set.range_comp, ← hfun]
  rw [hrange, hd.closure_eq, Set.preimage_univ] at key
  rwa [denseRange_iff_closure_range]

/-- The topological range of `qi` is the range of the closed immersion `Ziι`. -/
lemma range_qi_eq_range_ZiIota {A : Type u} [CommRing A] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of A)} (D : ChowSetup A X f) (i : Fin D.m) :
    Set.range ⇑(ChowSetup.qi D i) = Set.range ⇑(ChowSetup.ZiIota D i) := by
  haveI : QuasiCompact D.jU := by
    haveI := noetherianSpace_opens D
    infer_instance
  haveI : QuasiCompact (D.j i) := D.quasiCompact_j i
  have hZ : Set.range ⇑(ChowSetup.Ziota D) = closure (Set.range ⇑(D.jU)) :=
    range_imageι_eq_closure_range D.jU
  have hZi : Set.range ⇑(ChowSetup.ZiIota D i) = closure (Set.range ⇑(D.j i)) :=
    range_imageι_eq_closure_range (D.j i)
  have hcl : IsClosedMap ⇑(D.p i) := by
    haveI : IsProper (D.p i) := D.pProper i
    exact (D.p i).isClosedMap
  calc Set.range ⇑(ChowSetup.qi D i)
      = Set.range ⇑(ChowSetup.Ziota D ≫ D.p i) := rfl
    _ = ⇑(D.p i) '' Set.range ⇑(ChowSetup.Ziota D) := range_comp_scheme (ChowSetup.Ziota D) (D.p i)
    _ = ⇑(D.p i) '' closure (Set.range ⇑(D.jU)) := by rw [hZ]
    _ = closure (⇑(D.p i) '' Set.range ⇑(D.jU)) :=
        image_closure_eq_of_isClosedMap (D.p i).continuous hcl _
    _ = closure (Set.range ⇑(D.jU ≫ D.p i)) := by rw [range_comp_scheme]
    _ = closure (Set.range ⇑(X.homOfLE (D.hU0le i) ≫ D.j i)) := by rw [D.jU_proj i]
    _ = closure (Set.range (⇑(D.j i) ∘ ⇑(X.homOfLE (D.hU0le i)))) := by
        rw [Set.range_comp, range_comp_scheme]
    _ = closure (Set.range ⇑(D.j i)) :=
        closure_range_comp_eq_of_denseRange _ _ (denseRange_homOfLE D i) (D.j i).continuous
    _ = Set.range ⇑(ChowSetup.ZiIota D i) := hZi.symm

theorem surjective_pi {A : Type u} [CommRing A] {X : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)}
    (D : Work.DSG2.ChowSetup A X f) (i : Fin D.m) :
    Function.Surjective (Work.DSG2.ChowSetup.pi D i) := by
  have hrange := range_qi_eq_range_ZiIota D i
  intro y
  have hy : ⇑(ChowSetup.ZiIota D i) y ∈ Set.range ⇑(ChowSetup.qi D i) := by
    rw [hrange]
    exact Set.mem_range_self y
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, ?_⟩
  apply (ChowSetup.ZiIota D i).isClosedEmbedding.toIsEmbedding.injective
  rw [← Scheme.Hom.comp_apply, ChowSetup.pi_spec]
  exact hx

end Work.DSG2
