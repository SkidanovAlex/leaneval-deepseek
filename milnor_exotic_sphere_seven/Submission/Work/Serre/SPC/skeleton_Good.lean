import Mathlib
import Submission.Work.Serre.SPC.B1Setup
import Submission.Work.Serre.SPC.B1Skeleton
import Submission.Work.Serre.SPC.OneCellX
import Submission.Work.Serre.SPC.FibreData
import Submission.Work.Serre.Assembly.pullbackFst_serre
import Submission.Work.Serre.SPC.attachFibreData
import Submission.Work.Serre.SPC.discDefs
import Submission.Work.StemsB.SphLoopRelPair

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `1`-skeleton of the model of `B` satisfies the comparison invariant

`Work.Serre.SPC.skeleton_Good` is the base case of the `b = 1` model of the Serre comparison: for a
Serre fibration `p : E → B` whose fibre over `b₀` is homologically `f`-connected (`H_j = 0` for
`0 < j < f`, `H₀ ≅ ℤ`), the invariant `Work.Serre.SPC.GoodN` — the pair map
`(skeletonMap^*E, fibre) → (Skeleton B b₀, base point)` is an isomorphism in degrees `< 1 + f` and
surjective in degree `1 + f` — holds for the `1`-skeleton
`Skeleton B b₀ = attachOneCells PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀)`.

## The argument

The skeleton is obtained from the *one-point* base `PUnit` by attaching `1`-cells, so the `D = 1`
cell step `Work.Serre.SPC.CellStepHypOne` applies with `Y := PUnit`.  Now `PUnit` is a
subsingleton, so the "old part" `Set.range (oneIncl PUnit ι fr)` of the cell step is exactly the
base point `{skeletonBase B b₀}`; consequently the relative part of the one-cell step map
`Work.Serre.SPC.oneCellStepMap` and that of the pair map `Work.StemsB.relPairMap` are the same pair,
and the two maps differ only by the reindexing isomorphisms

`relChains Q (q⁻¹{γ}) ≅ relChains Q (q⁻¹ range oneIncl)`,   `relChains Z {γ} ≅ relChains Z (range oneIncl)`

of the relative chain complexes induced by the identity (both are the identity on the underlying
space, with the two relative parts equal).  The isomorphisms are instances of
`Work.StemsB.isIso_relChainsMapOf_homeomorph`, and the two maps are conjugated by them; `IsIso` and
surjectivity are then transferred along the conjugated square
(`Work.Serre.SPC.isIso_iff_of_comm_square`, `Work.Serre.SPC.surjective_iff_of_comm_square`).

The fibre data of the base change `q = pullbackFst (skeletonMap B b₀) p` required by the cell step
is supplied by `Work.Serre.SPC.attachFibreData` (fibre transport along paths, since the skeleton is
path connected).
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.SPC

noncomputable section

/-! ## The index type of the `1`-cells -/

/-- The index type of the cells of the `1`-skeleton: the based loops of `B`. -/
abbrev SkelIdx (B : Type) [TopologicalSpace B] (b₀ : B) : Type := ↥(GenLoop (Fin 1) B b₀)

/-! ## The pullback of `p` along the structure map of the skeleton -/

/-- The total space of the pullback of `p` along the structure map of the `1`-skeleton. -/
abbrev skelQ (B : Type) [TopologicalSpace B] (b₀ : B) {E : Type} [TopologicalSpace E]
    (p : C(E, B)) : Type := Work.StemsB.Pullback (skeletonMap B b₀) p

/-- The base change `q : skeletonMap^*E → Skeleton B b₀` of `p`. -/
abbrev skelq (B : Type) [TopologicalSpace B] (b₀ : B) {E : Type} [TopologicalSpace E]
    (p : C(E, B)) : C(skelQ B b₀ p, Skeleton B b₀) :=
  Work.StemsB.pullbackFst (skeletonMap B b₀) p

/-- The range of the inclusion of the point of `PUnit` into the skeleton: the "old part" of the
one-cell step, i.e. the base point. -/
abbrev skelRng (B : Type) [TopologicalSpace B] (b₀ : B) : Set (Skeleton B b₀) :=
  Set.range (⇑(oneIncl PUnit (SkelIdx B b₀) (skeletonAttach B b₀)))

/-- The relative part of the one-cell step map: the preimage of the old part. -/
abbrev skelA₂ (B : Type) [TopologicalSpace B] (b₀ : B) {E : Type} [TopologicalSpace E]
    (p : C(E, B)) : Set (skelQ B b₀ p) := {x | skelq B b₀ p x ∈ skelRng B b₀}

/-- The relative part of the pair map: the fibre over the base point. -/
abbrev skelA₁ (B : Type) [TopologicalSpace B] (b₀ : B) {E : Type} [TopologicalSpace E]
    (p : C(E, B)) : Set (skelQ B b₀ p) :=
  (skelq B b₀ p) ⁻¹' ({skeletonBase B b₀} : Set (Skeleton B b₀))

/-! ## Two elementary facts -/

/-- **The range of the inclusion of a subsingleton is a point.** -/
theorem range_oneIncl_subsingleton {Y : Type} [TopologicalSpace Y] [Subsingleton Y] (ι : Type)
    (fr : ι → C(cellS0, Y)) (y₀ : Y) :
    Set.range (⇑(oneIncl Y ι fr)) = ({oneIncl Y ι fr y₀} : Set (attachOneCells Y ι fr)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨y, rfl⟩
    exact Set.mem_singleton_iff.mpr (congrArg _ (Subsingleton.elim y y₀))
  · rintro _ rfl
    exact ⟨y₀, rfl⟩

/-- **The identity homeomorphism is the identity morphism of `TopCat`.** -/
theorem sphHomeoHom_refl (X : TopCat) :
    Work.StemsB.sphHomeoHom (Homeomorph.refl X) = 𝟙 X := by
  apply TopCat.hom_ext
  ext x
  rfl

/-! ## The base case -/

theorem skeleton_Good (hone : Work.Serre.SPC.CellStepHypOne) {B : Type} [TopologicalSpace B] (b₀ : B) {E : Type} [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E) (he₀ : p e₀ = b₀) (f : ℕ) (hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩)) (hfib : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p b₀))).homology j)) (htr : Work.Serre.SPC.FibreTransport) [PathConnectedSpace (Work.Serre.SPC.Skeleton B b₀)] : Work.Serre.SPC.GoodN b₀ p (1 + f) (Work.Serre.SPC.skeletonBase B b₀) (Work.Serre.SPC.skeletonMap B b₀) := by
  -- ## the connectivity data of the fibres of the base change
  have hq : Work.StemsB.IsSerreFibration (skelq B b₀ p) :=
    Work.Serre.Assembly.pullbackFst_serre (skeletonMap B b₀) p hp
  have hdata := Work.Serre.SPC.attachFibreData p hp b₀ e₀ he₀ f htr hfib hfib0
    (skeletonBase B b₀) (skeletonMap B b₀) rfl
  -- ## the `D = 1` cell step, at the one-point base
  obtain ⟨hstepIso, hstepSurj⟩ :=
    hone PUnit (SkelIdx B b₀) (skeletonAttach B b₀) (skelQ B b₀ p) (skelq B b₀ p)
      hq f hdata.1 hdata.2
  -- ## the two relative parts coincide with those of the pair map
  have hrange : skelRng B b₀ = ({skeletonBase B b₀} : Set (Skeleton B b₀)) := by
    rw [show (skeletonBase B b₀ : Skeleton B b₀)
        = oneIncl PUnit (SkelIdx B b₀) (skeletonAttach B b₀) ⟨⟩ from rfl]
    exact range_oneIncl_subsingleton (SkelIdx B b₀) (skeletonAttach B b₀) ⟨⟩
  have hA : skelA₂ B b₀ p = skelA₁ B b₀ p := by
    show ({x | skelq B b₀ p x ∈ skelRng B b₀} : Set _) = _
    rw [hrange]
    rfl
  -- ## the reindexing isomorphisms of the relative chain complexes
  have hAB : ∀ x : skelQ B b₀ p, x ∈ skelA₂ B b₀ p
      ↔ (Homeomorph.refl (TopCat.of (skelQ B b₀ p))) x ∈ skelA₁ B b₀ p := by
    intro x
    show _ ↔ x ∈ _
    rw [hA]
  have hAB' : ∀ x : Skeleton B b₀, x ∈ skelRng B b₀
      ↔ (Homeomorph.refl (TopCat.of (Skeleton B b₀))) x ∈
        ({skeletonBase B b₀} : Set (Skeleton B b₀)) := by
    intro x
    show x ∈ skelRng B b₀ ↔ x ∈ ({skeletonBase B b₀} : Set (Skeleton B b₀))
    rw [hrange]
  set UG := Work.StemsB.relChainsMapOf
    (Work.StemsB.sphHomeoHom (Homeomorph.refl (TopCat.of (skelQ B b₀ p))))
    (skelA₂ B b₀ p) (skelA₁ B b₀ p) (Work.StemsB.homeoPairMem hAB) with hUGdef
  set VG := Work.StemsB.relChainsMapOf
    (Work.StemsB.sphHomeoHom (Homeomorph.refl (TopCat.of (Skeleton B b₀))))
    (skelRng B b₀) ({skeletonBase B b₀} : Set (Skeleton B b₀))
    (Work.StemsB.homeoPairMem hAB') with hVGdef
  have hUG : IsIso UG := Work.StemsB.isIso_relChainsMapOf_homeomorph _ _ _ hAB
  have hVG : IsIso VG := Work.StemsB.isIso_relChainsMapOf_homeomorph _ _ _ hAB'
  -- ## the naturality of the projections onto the relative chain complexes
  have hπU : cokernel.π (Work.Cohomology.inclChains (TopCat.of (skelQ B b₀ p)) (skelA₂ B b₀ p))
      ≫ UG = Work.Cohomology.chainMap ℤ (TopCat.of (skelQ B b₀ p)) (TopCat.of (skelQ B b₀ p))
        (Work.StemsB.sphHomeoHom (Homeomorph.refl (TopCat.of (skelQ B b₀ p))))
      ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (skelQ B b₀ p)) (skelA₁ B b₀ p)) :=
    Work.StemsB.π_comp_relChainsMapOf _ _ _ _
  have hπV : cokernel.π (Work.Cohomology.inclChains (TopCat.of (Skeleton B b₀))
        (skelRng B b₀)) ≫ VG
      = Work.Cohomology.chainMap ℤ (TopCat.of (Skeleton B b₀)) (TopCat.of (Skeleton B b₀))
        (Work.StemsB.sphHomeoHom (Homeomorph.refl (TopCat.of (Skeleton B b₀))))
      ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Skeleton B b₀))
          ({skeletonBase B b₀} : Set (Skeleton B b₀))) :=
    Work.StemsB.π_comp_relChainsMapOf _ _ _ _
  have hπR : cokernel.π (Work.Cohomology.inclChains (TopCat.of (skelQ B b₀ p)) (skelA₁ B b₀ p))
      ≫ Work.StemsB.relPairMap (skelq B b₀ p) (skeletonBase B b₀)
    = Work.Cohomology.chainMap ℤ (TopCat.of (skelQ B b₀ p)) (TopCat.of (Skeleton B b₀))
        (TopCat.ofHom (skelq B b₀ p))
      ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Skeleton B b₀))
          ({skeletonBase B b₀} : Set (Skeleton B b₀))) := by
    unfold Work.StemsB.relPairMap Work.Cohomology.relChainsMapOf
    exact Work.Cohomology.cokernel_π_map _ _ _ _ _
  have hπS : cokernel.π (Work.Cohomology.inclChains (TopCat.of (skelQ B b₀ p)) (skelA₂ B b₀ p))
      ≫ oneCellStepMap (SkelIdx B b₀) (skeletonAttach B b₀) (skelq B b₀ p)
    = Work.Cohomology.chainMap ℤ (TopCat.of (skelQ B b₀ p)) (TopCat.of (Skeleton B b₀))
        (TopCat.ofHom (skelq B b₀ p))
      ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Skeleton B b₀)) (skelRng B b₀)) := by
    unfold oneCellStepMap Work.Cohomology.relChainsMapOf
    exact Work.Cohomology.cokernel_π_map _ _ _ _ _
  -- ## the two maps are conjugated by the reindexings
  have hL : cokernel.π (Work.Cohomology.inclChains (TopCat.of (skelQ B b₀ p)) (skelA₂ B b₀ p))
        ≫ (UG ≫ Work.StemsB.relPairMap (skelq B b₀ p) (skeletonBase B b₀))
      = Work.Cohomology.chainMap ℤ (TopCat.of (skelQ B b₀ p)) (TopCat.of (Skeleton B b₀))
          (TopCat.ofHom (skelq B b₀ p))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Skeleton B b₀))
            ({skeletonBase B b₀} : Set (Skeleton B b₀))) := by
    rw [← Category.assoc, hπU, Category.assoc, hπR, sphHomeoHom_refl,
      Work.StemsB.chainMap_id, Category.id_comp]
  have hR : cokernel.π (Work.Cohomology.inclChains (TopCat.of (skelQ B b₀ p)) (skelA₂ B b₀ p))
        ≫ (oneCellStepMap (SkelIdx B b₀) (skeletonAttach B b₀) (skelq B b₀ p) ≫ VG)
      = Work.Cohomology.chainMap ℤ (TopCat.of (skelQ B b₀ p)) (TopCat.of (Skeleton B b₀))
          (TopCat.ofHom (skelq B b₀ p))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Skeleton B b₀))
            ({skeletonBase B b₀} : Set (Skeleton B b₀))) := by
    rw [← Category.assoc, hπS, Category.assoc, hπV, sphHomeoHom_refl,
      Work.StemsB.chainMap_id, Category.id_comp]
  have hsquare : UG ≫ Work.StemsB.relPairMap (skelq B b₀ p) (skeletonBase B b₀)
      = oneCellStepMap (SkelIdx B b₀) (skeletonAttach B b₀) (skelq B b₀ p) ≫ VG := by
    apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains (TopCat.of (skelQ B b₀ p))
      (skelA₂ B b₀ p)))).mp
    rw [hL, hR]
  -- ## transfer the cell step to the pair map
  rw [Work.Serre.SPC.GoodN]
  constructor
  · intro i hi
    haveI : IsIso (HomologicalComplex.homologyMap UG i) := by
      rw [← HomologicalComplex.homologyFunctor_map]
      exact Functor.map_isIso _ UG
    haveI : IsIso (HomologicalComplex.homologyMap VG i) := by
      rw [← HomologicalComplex.homologyFunctor_map]
      exact Functor.map_isIso _ VG
    have hsq : HomologicalComplex.homologyMap UG i
          ≫ HomologicalComplex.homologyMap
              (Work.StemsB.relPairMap (skelq B b₀ p) (skeletonBase B b₀)) i
        = HomologicalComplex.homologyMap
              (oneCellStepMap (SkelIdx B b₀) (skeletonAttach B b₀) (skelq B b₀ p)) i
          ≫ HomologicalComplex.homologyMap VG i := by
      have h := congrArg (fun m => HomologicalComplex.homologyMap m i) hsquare
      simpa only [HomologicalComplex.homologyMap_comp] using h
    exact (Work.Serre.SPC.isIso_iff_of_comm_square _ _ _ _ hsq).mpr (hstepIso i hi)
  · haveI : IsIso (HomologicalComplex.homologyMap UG (1 + f)) := by
      rw [← HomologicalComplex.homologyFunctor_map]
      exact Functor.map_isIso _ UG
    haveI : IsIso (HomologicalComplex.homologyMap VG (1 + f)) := by
      rw [← HomologicalComplex.homologyFunctor_map]
      exact Functor.map_isIso _ VG
    have hsq : HomologicalComplex.homologyMap UG (1 + f)
          ≫ HomologicalComplex.homologyMap
              (Work.StemsB.relPairMap (skelq B b₀ p) (skeletonBase B b₀)) (1 + f)
        = HomologicalComplex.homologyMap
              (oneCellStepMap (SkelIdx B b₀) (skeletonAttach B b₀) (skelq B b₀ p)) (1 + f)
          ≫ HomologicalComplex.homologyMap VG (1 + f) := by
      have h := congrArg (fun m => HomologicalComplex.homologyMap m (1 + f)) hsquare
      simpa only [HomologicalComplex.homologyMap_comp] using h
    exact (Work.Serre.SPC.surjective_iff_of_comm_square _ _ _ _ hsq).mpr hstepSurj

end

end Work.Serre.SPC
