import Mathlib
import Submission.Work.Orient.Closed
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.ThomBordism.sourceCoord
import Submission.Work.ThomBordism.sourceCoordAssembly
import Submission.Work.PTGeometric.LevelModel
import Submission.Work.PTGeometric.ConcreteCollapse
import Submission.Work.ThomBordism.Transversality.OrientBridge.isFundClass_sum_push

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: a **cycle-free, axiom-clean** assembly of the boundary coordination

The requested assembly lemma
`Work.ThomBordism.sourceBoundaryCoord_of_piecewiseLocalClass`
(`Submission/Work/ThomBordism/sourceBoundaryCoord_of_piecewiseLocalClass.lean`) is stated about
`Work.PTGeometric.producedRawData` and therefore lives *above* `SourceWiring`; consequently it (and
its module) can **not** be imported by `sourceRawAmbientData_tied_collar.lean`, whose `sorry` is the
last mile.  The same applies to the witness-abstract copies of
`Submission/Work/ThomBordism/levelClassData_of_coord_generic.lean`, because that module imports
`levelClassData_of_coord` (which imports `levelModelSetup` → `SourceWiring`).

This file contains the *same* assembly in a module whose entire import closure is free of
`SourceWiring` and of `sourceRawAmbientData_tied_collar` (checked on the import graph), so that it can
be imported **inside the construction** — the pattern already used by the construction's own `…V2`
files.  The only difference from the material in
`sourceBoundaryCoord_of_piecewiseLocalClass.lean` is that the collapse identification is an explicit
*parameter* `e : ∂W ≃ Σ_i (Fam i).pt` (together with the pointwise agreement with `piecePush D0`,
which is `rfl` for the canonical identification), and that the comparison is asked **pointwise** —
the form in which the local tube computation is available, and the only one that needs no
connectedness of the pieces (`Man8` provides none, and the construction's datum has `Nonempty` but
not connected pieces).

Mathematical content (the same as the requested lemma): `hPairδ w = ε • Σ_i (push_i)_* c_i` with
`ε = ±1` implies that the sum of the pushed classes dies under the inclusion of the boundary part
(`Work.Cohomology.hPairδ_comp`, the long exact sequence of `(W, ∂W)`), and the vanishing transfers
along the identification of the boundary part with the raw one (`mem_boundary_iff`).

Everything here is `sorryAx`-free and mentions no `Classical.choose` of a `sorry`-ed existence
theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.ThomBordism

noncomputable section

open Work.PTGeometric Work.Cohomology

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
  {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]

/-- **Transfer of the boundary class along an identification of the boundary part** (private copy of
`Work.ThomBordism.boundaryClass_transfer`, kept here so that this module is cycle-free: the original
lives in a module that imports `SourceWiring`). -/
private theorem boundaryClass_transfer' {X : TopCat} {A₀ A₁ : Set X} (hA : A₀ = A₁)
    {ι' : Type} [Fintype ι'] {Fam' : ι' → Work.ThomBordism.Man8}
    (f : ∀ i, (Fam' i).X ⟶ TopCat.of A₀) (g : ∀ i, (Fam' i).X ⟶ TopCat.of A₁)
    (hfg : ∀ i y, Homeomorph.setCongr hA (ConcreteCategory.hom (f i) y)
      = ConcreteCategory.hom (g i) y) :
    (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A₀) 8).hom
        (∑ i, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (Fam' i).X (TopCat.of A₀) (f i)) 8 (Fam' i).c)
      = (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A₁) 8).hom
        (∑ i, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (Fam' i).X (TopCat.of A₁) (g i)) 8 (Fam' i).c) := by
  let Ψ : TopCat.of A₀ ⟶ TopCat.of A₁ :=
    TopCat.ofHom ⟨Homeomorph.setCongr hA, (Homeomorph.setCongr hA).continuous⟩
  have hsub : Ψ ≫ Work.Cohomology.subtypeIncl X A₁ = Work.Cohomology.subtypeIncl X A₀ := by
    apply TopCat.Hom.ext
    apply ContinuousMap.ext
    intro x
    rfl
  have hw : Work.Cohomology.chainMap ℤ (TopCat.of A₀) (TopCat.of A₁) Ψ
      ≫ Work.Cohomology.inclChains X A₁ = Work.Cohomology.inclChains X A₀ := by
    simp only [Work.Cohomology.inclChains, Work.Cohomology.chainMap]
    rw [← Functor.map_comp, hsub]
  have hterm : ∀ i, Work.Cohomology.chainMap ℤ (Fam' i).X (TopCat.of A₁) (g i)
      = Work.Cohomology.chainMap ℤ (Fam' i).X (TopCat.of A₀) (f i)
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of A₀) (TopCat.of A₁) Ψ := by
    intro i
    have hgf : f i ≫ Ψ = g i := by
      apply TopCat.Hom.ext
      apply ContinuousMap.ext
      intro y
      show (Homeomorph.setCongr hA) ((ConcreteCategory.hom (f i)) y)
        = (ConcreteCategory.hom (g i)) y
      exact hfg i y
    rw [← hgf]
    simp only [Work.Cohomology.chainMap]
    rw [Functor.map_comp]
  have key : (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of A₀) (TopCat.of A₁) Ψ) 8)
      ≫ (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A₁) 8)
      = HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A₀) 8 := by
    rw [← HomologicalComplex.homologyMap_comp, hw]
  have key2 : ∀ y, (HomologicalComplex.homologyMap
        (Work.Cohomology.inclChains X A₁) 8).hom
        ((HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of A₀) (TopCat.of A₁) Ψ) 8).hom y)
      = (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A₀) 8).hom y := by
    intro y
    rw [← ModuleCat.comp_apply, key]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 : (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (Fam' i).X (TopCat.of A₁) (g i)) 8).hom (Fam' i).c
      = (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of A₀) (TopCat.of A₁) Ψ) 8).hom
        ((HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (Fam' i).X (TopCat.of A₀) (f i)) 8).hom (Fam' i).c) := by
    rw [hterm i, HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply]
  rw [h1, key2]

/-- The two presentations of the boundary part of the level model of `D0` are equal
(`Work.PTGeometric.Lvl.Setup.mem_boundary_iff`), so they are homeomorphic by `Homeomorph.setCongr`;
this is the collapse-identification-agnostic transfer homeomorphism. -/
abbrev boundaryTransferHomeo {mU m : ℕ}
    (D0 : Work.PTGeometric.RawAmbientData (k + mU) k (Fin m × ι) (fun a => Fam a.2))
    {hWcl : IsClosed (Work.ThomBordism.sourceLevelSet D0)}
    {L : Work.PTGeometric.LocalLevelData k D0.M (Work.ThomBordism.sourceLevelSet D0)} :
    ↥((modelWithCornersEuclideanHalfSpace 9).boundary
        (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L))
      ≃ₜ ↥(Work.ThomBordism.sourceLevelBdry D0) :=
  Homeomorph.setCongr (Set.ext fun x =>
    Work.PTGeometric.Lvl.Setup.mem_boundary_iff
      (Work.PTGeometric.levelSetup (Work.ThomBordism.sourceLevelSet D0) hWcl L) x)

/-- The transfer homeomorphism as a morphism of `TopCat`. -/
abbrev boundaryTransferTop {mU m : ℕ}
    (D0 : Work.PTGeometric.RawAmbientData (k + mU) k (Fin m × ι) (fun a => Fam a.2))
    {hWcl : IsClosed (Work.ThomBordism.sourceLevelSet D0)}
    {L : Work.PTGeometric.LocalLevelData k D0.M (Work.ThomBordism.sourceLevelSet D0)} :
    TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
        (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L))
      ⟶ TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0) :=
  TopCat.ofHom ⟨boundaryTransferHomeo D0, (boundaryTransferHomeo D0).continuous⟩

/-- The inverse transfer homeomorphism as a morphism of `TopCat`. -/
abbrev boundaryTransferTopSymm {mU m : ℕ}
    (D0 : Work.PTGeometric.RawAmbientData (k + mU) k (Fin m × ι) (fun a => Fam a.2))
    {hWcl : IsClosed (Work.ThomBordism.sourceLevelSet D0)}
    {L : Work.PTGeometric.LocalLevelData k D0.M (Work.ThomBordism.sourceLevelSet D0)} :
    TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0)
      ⟶ TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
        (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L)) :=
  TopCat.ofHom ⟨(boundaryTransferHomeo D0).symm, (boundaryTransferHomeo D0).symm.continuous⟩

/-- **The two avatars of the class of the pieces agree**, for any homeomorphism `e` of the boundary
part with the pieces whose inverse composed with the `i`-th summand is the piece push `piecePush D0 i`
(this is `rfl`-like for the canonical collapse identification): the sum of the pushed fundamental
classes in the *level-model* presentation is the pullback along the transfer homeomorphism of the raw
class `sourceBoundaryClass D0`.

This is the bridge between the two ways the last mile phrases the `ῆ`-side, and it needs no geometry:
it is chain-level functoriality plus the pointwise agreement of the maps. -/
theorem sum_pushClass_eq_sourceBoundaryClass
    (hk : 11 ≤ k) (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (D0 : Work.PTGeometric.RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2))
    {hWcl : IsClosed (Work.ThomBordism.sourceLevelSet D0)}
    {L : Work.PTGeometric.LocalLevelData k D0.M (Work.ThomBordism.sourceLevelSet D0)}
    (e : ↥((modelWithCornersEuclideanHalfSpace 9).boundary
        (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L))
      ≃ₜ (Σ a : Fin m × ι, (Fam a.2).pt))
    (he : ∀ (a : Fin m × ι) (y : (Fam a.2).pt),
        ((e.symm ⟨a, y⟩ : ↥((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L))).1 :
            ↥(Work.ThomBordism.sourceLevelSet D0))
          = ((Work.ThomBordism.piecePush D0 a y : ↥(Work.ThomBordism.sourceLevelBdry D0)) :
              ↥(Work.ThomBordism.sourceLevelSet D0))) :
    (∑ i : Fin m × ι, Work.ThomBordism.Transversality.OrientBridge.pushClass
        (Fam := fun a : Fin m × ι => Fam a.2) e.symm i)
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ
            (TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0))
            (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
              (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L)))
            (boundaryTransferTopSymm D0)) 8))
          (Work.ThomBordism.sourceBoundaryClass D0) := by
  classical
  -- the pushforward of the sum along the transfer homeomorphism is the raw class
  have hmap : ∀ i : Fin m × ι,
      Work.Cohomology.chainMap ℤ (Fam i.2).X
          (TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0))
          (TopCat.ofHom (Work.ThomBordism.piecePush D0 i))
        = Work.Cohomology.chainMap ℤ (Fam i.2).X
            (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
              (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L)))
            (Work.ThomBordism.Transversality.OrientBridge.pushPt e.symm i)
          ≫ Work.Cohomology.chainMap ℤ
              (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
                (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L)))
              (TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0))
              (boundaryTransferTop D0) := by
    intro i
    have h : Work.ThomBordism.Transversality.OrientBridge.pushPt e.symm i
          ≫ boundaryTransferTop D0
        = TopCat.ofHom (Work.ThomBordism.piecePush D0 i) := by
      apply TopCat.Hom.ext
      apply ContinuousMap.ext
      intro y
      show (Homeomorph.setCongr (Set.ext fun x =>
          Work.PTGeometric.Lvl.Setup.mem_boundary_iff
            (Work.PTGeometric.levelSetup (Work.ThomBordism.sourceLevelSet D0) hWcl L) x))
          ((Work.ThomBordism.Transversality.OrientBridge.pushPt e.symm i) y)
        = (Work.ThomBordism.piecePush D0 i) y
      exact Subtype.ext (he i y)
    rw [← h]
    simp only [Work.Cohomology.chainMap]
    rw [Functor.map_comp]
  have hsum : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ
        (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
          (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L)))
        (TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0))
        (boundaryTransferTop D0)) 8))
      (∑ i : Fin m × ι, Work.ThomBordism.Transversality.OrientBridge.pushClass
        (Fam := fun a : Fin m × ι => Fam a.2) e.symm i)
      = Work.ThomBordism.sourceBoundaryClass D0 := by
    rw [map_sum, Work.ThomBordism.sourceBoundaryClass]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hmap i, HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply]
  -- the transfer homeomorphism induces an isomorphism on homology
  have hcom' : boundaryTransferTop (hWcl := hWcl) (L := L) D0
      ≫ boundaryTransferTopSymm (hWcl := hWcl) (L := L) D0 = 𝟙 _ := by
    apply TopCat.Hom.ext
    apply ContinuousMap.ext
    intro x
    rfl
  have hrev : (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ
          (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L)))
          (TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0))
          (boundaryTransferTop D0)) 8)
      ≫ (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ
            (TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0))
            (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
              (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L)))
            (boundaryTransferTopSymm D0)) 8) = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, ← Work.Cohomology.chainMap_comp', hcom',
      Work.Cohomology.chainMap_id', HomologicalComplex.homologyMap_id]
  have hfin := congrArg (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ
        (TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0))
        (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
          (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L)))
        (boundaryTransferTopSymm D0)) 8)) hsum
  rw [← ModuleCat.comp_apply, hrev, ModuleCat.id_apply] at hfin
  exact hfin

/-- **The assembly datum of the boundary coordination** (cycle-free, witness-free form).

It consists of

* a homeomorphism `e` of the boundary part `∂W` of the level model with the pieces `Σ_i (Fam i).pt`
  (in the source construction this is the collapse identification; for the *canonical* identification
  `levelBdryHomeoFullOf` the agreement is `rfl`);
* the pointwise agreement of `e.symm ∘ σ_i` with the piece pushes `piecePush D0 i`;
* a single sign `ε = ±1` and a relative class `w ∈ H_9(W, ∂W)` whose boundary has, at **every** point
  of `∂W`, the local class `ε` times the local class of the sum of the pieces' pushed classes. -/
def SourceBoundaryCoordAssemblyData
    (hk : 11 ≤ k) (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (D0 : Work.PTGeometric.RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2))
    {hWcl : IsClosed (Work.ThomBordism.sourceLevelSet D0)}
    {L : Work.PTGeometric.LocalLevelData k D0.M (Work.ThomBordism.sourceLevelSet D0)} : Prop := by
  let S : Work.PTGeometric.Lvl.Setup k :=
    Work.PTGeometric.levelSetup (Work.ThomBordism.sourceLevelSet D0) hWcl L
  letI := Work.PTGeometric.Lvl.Setup.instChartedSpace S
  letI := Work.PTGeometric.Lvl.Setup.instIsManifold S
  letI := Work.PTGeometric.Lvl.Setup.instCompactSpace S
  exact ∃ e : ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre) ≃ₜ
        (Σ a : Fin m × ι, (Fam a.2).pt),
      (∀ (a : Fin m × ι) (y : (Fam a.2).pt),
        ((e.symm ⟨a, y⟩ : ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre)).1 :
            ↥(Work.ThomBordism.sourceLevelSet D0))
          = ((Work.ThomBordism.piecePush D0 a y : ↥(Work.ThomBordism.sourceLevelBdry D0)) :
              ↥(Work.ThomBordism.sourceLevelSet D0))) ∧
      ∃ (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
        ∃ w : (Work.Cohomology.relChains (TopCat.of S.Pre)
            ((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre)).homology 9,
          ∀ x : ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre),
            Work.Orient.locClass
                (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre)) 8
                ((Work.Cohomology.hPairδ (TopCat.of S.Pre)
                  ((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre) 8).hom w) x
              = ε • Work.Orient.locClass
                  (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre)) 8
                  (∑ i : Fin m × ι,
                    Work.ThomBordism.Transversality.OrientBridge.pushClass
                      (Fam := fun a : Fin m × ι => Fam a.2) e.symm i) x

/-- **The assembly**: the datum `SourceBoundaryCoordAssemblyData` gives the boundary coordination of
the raw datum.  Cycle-free and axiom-clean; importable by the source construction. -/
theorem sourceBoundaryCoord_of_assemblyData
    (hk : 11 ≤ k) (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (D0 : Work.PTGeometric.RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2))
    {hWcl : IsClosed (Work.ThomBordism.sourceLevelSet D0)}
    {L : Work.PTGeometric.LocalLevelData k D0.M (Work.ThomBordism.sourceLevelSet D0)}
    (h : SourceBoundaryCoordAssemblyData hk G m hm hpow D0 (hWcl := hWcl) (L := L)) :
    Work.ThomBordism.SourceBoundaryCoord D0 := by
  classical
  let S : Work.PTGeometric.Lvl.Setup k :=
    Work.PTGeometric.levelSetup (Work.ThomBordism.sourceLevelSet D0) hWcl L
  letI := Work.PTGeometric.Lvl.Setup.instChartedSpace S
  letI := Work.PTGeometric.Lvl.Setup.instIsManifold S
  letI := Work.PTGeometric.Lvl.Setup.instCompactSpace S
  obtain ⟨e, he, ε, hε, w, hw⟩ := h
  -- the difference class has vanishing local class everywhere, hence is `0`
  set Dd : (Work.Cohomology.singularChains ℤ
      (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre))).homology 8 :=
    (Work.Cohomology.hPairδ (TopCat.of S.Pre)
        ((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre) 8).hom w
      - ε • ∑ i, Work.ThomBordism.Transversality.OrientBridge.pushClass
          (Fam := fun a : Fin m × ι => Fam a.2) e.symm i with hDd
  have hall : ∀ x : ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre),
      Work.Orient.locClass
        (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre)) 8 Dd x = 0 := by
    intro x
    rw [hDd, Work.Orient.locClass_sub, Work.Orient.locClass_zsmul, hw x, sub_self]
  haveI : CompactSpace ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre) :=
    isCompact_iff_compactSpace.mp
      (ModelWithCorners.isClosed_boundary (I := modelWithCornersEuclideanHalfSpace 9)
        (M := S.Pre) (n := ((⊤ : ENat) : WithTop ENat)) (by simp)).isCompact
  have hDd0 : Dd = 0 :=
    Work.Orient.eq_zero_of_locClass_eq_zero 8 (by norm_num)
      (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre)) Dd hall
  have hsign : (Work.Cohomology.hPairδ (TopCat.of S.Pre)
        ((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre) 8).hom w
      = ε • ∑ i, Work.ThomBordism.Transversality.OrientBridge.pushClass
          (Fam := fun a : Fin m × ι => Fam a.2) e.symm i :=
    sub_eq_zero.mp hDd0
  -- the connecting map of the pair `(W, ∂W)` followed by the inclusion of `∂W` is zero
  have hcomp : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of S.Pre)
        ((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre)) 8))
      ((ModuleCat.Hom.hom (Work.Cohomology.hPairδ (TopCat.of S.Pre)
        ((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre) 8)) w) = 0 := by
    rw [← ModuleCat.comp_apply, Work.Cohomology.hPairδ_comp]
    simp
  rw [hsign] at hcomp
  have hz : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of S.Pre)
        ((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre)) 8))
      (∑ i, Work.ThomBordism.Transversality.OrientBridge.pushClass
        (Fam := fun a : Fin m × ι => Fam a.2) e.symm i) = 0 := by
    rw [map_zsmul] at hcomp
    rcases hε with h | h
    · rw [h, one_smul] at hcomp
      exact hcomp
    · rw [h] at hcomp
      simpa using hcomp
  -- the two presentations of the boundary part
  have hA : (modelWithCornersEuclideanHalfSpace 9).boundary S.Pre =
      Work.ThomBordism.sourceLevelBdry D0 :=
    Set.ext fun x => Work.PTGeometric.Lvl.Setup.mem_boundary_iff S x
  have htransfer := boundaryClass_transfer' (X := TopCat.of S.Pre) hA
    (Fam' := fun a : Fin m × ι => Fam a.2)
    (fun i => Work.ThomBordism.Transversality.OrientBridge.pushPt e.symm i)
    (fun i => TopCat.ofHom (Work.ThomBordism.piecePush D0 i))
    (fun i y => Subtype.ext (he i y))
  have hgoal : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of S.Pre)
        (Work.ThomBordism.sourceLevelBdry D0)) 8))
      (Work.ThomBordism.sourceBoundaryClass D0) = 0 :=
    htransfer ▸ hz
  exact hgoal

/-- **The assembly datum, phrased with the raw class `ῆ`** (`SourceBoundaryCoordAssemblyData`'s
comparison, but against the *pullback* of `sourceBoundaryClass D0` along the transfer
homeomorphism — the form in which the tube dictionary computes the local class of the boundary of a
relative fundamental class).  By `Work.ThomBordism.sum_pushClass_eq_sourceBoundaryClass` the two
phrasings are the same datum. -/
def SourceBoundaryCoordAssemblyDataRaw
    (hk : 11 ≤ k) (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (D0 : Work.PTGeometric.RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2))
    {hWcl : IsClosed (Work.ThomBordism.sourceLevelSet D0)}
    {L : Work.PTGeometric.LocalLevelData k D0.M (Work.ThomBordism.sourceLevelSet D0)} : Prop := by
  let S : Work.PTGeometric.Lvl.Setup k :=
    Work.PTGeometric.levelSetup (Work.ThomBordism.sourceLevelSet D0) hWcl L
  letI := Work.PTGeometric.Lvl.Setup.instChartedSpace S
  letI := Work.PTGeometric.Lvl.Setup.instIsManifold S
  letI := Work.PTGeometric.Lvl.Setup.instCompactSpace S
  exact ∃ e : ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre) ≃ₜ
        (Σ a : Fin m × ι, (Fam a.2).pt),
      (∀ (a : Fin m × ι) (y : (Fam a.2).pt),
        ((e.symm ⟨a, y⟩ : ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre)).1 :
            ↥(Work.ThomBordism.sourceLevelSet D0))
          = ((Work.ThomBordism.piecePush D0 a y : ↥(Work.ThomBordism.sourceLevelBdry D0)) :
              ↥(Work.ThomBordism.sourceLevelSet D0))) ∧
      ∃ (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
        ∃ w : (Work.Cohomology.relChains (TopCat.of S.Pre)
            ((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre)).homology 9,
          ∀ x : ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre),
            Work.Orient.locClass
                (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre)) 8
                ((Work.Cohomology.hPairδ (TopCat.of S.Pre)
                  ((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre) 8).hom w) x
              = ε • Work.Orient.locClass
                  (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre)) 8
                  ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
                      (Work.Cohomology.chainMap ℤ
                        (TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0))
                        (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre))
                        (boundaryTransferTopSymm (hWcl := hWcl) (L := L) D0)) 8))
                    (Work.ThomBordism.sourceBoundaryClass D0)) x

/-- **The raw-phrased assembly**: `SourceBoundaryCoordAssemblyDataRaw` also gives the coordination
(the comparison against the pullback of `sourceBoundaryClass D0` differs from the comparison against
the sum of the pushed classes only by
`Work.ThomBordism.sum_pushClass_eq_sourceBoundaryClass`). -/
theorem sourceBoundaryCoord_of_assemblyDataRaw
    (hk : 11 ≤ k) (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (D0 : Work.PTGeometric.RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2))
    {hWcl : IsClosed (Work.ThomBordism.sourceLevelSet D0)}
    {L : Work.PTGeometric.LocalLevelData k D0.M (Work.ThomBordism.sourceLevelSet D0)}
    (h : SourceBoundaryCoordAssemblyDataRaw hk G m hm hpow D0 (hWcl := hWcl) (L := L)) :
    Work.ThomBordism.SourceBoundaryCoord D0 := by
  classical
  obtain ⟨e, he, ε, hε, w, hw⟩ := h
  refine sourceBoundaryCoord_of_assemblyData hk G m hm hpow D0 (hWcl := hWcl) (L := L)
    ⟨e, he, ε, hε, w, fun x => ?_⟩
  have hbr := Work.ThomBordism.sum_pushClass_eq_sourceBoundaryClass
    (hk := hk) (G := G) (m := m) (hm := hm) (hpow := hpow) D0 (hWcl := hWcl) (L := L) e he
  rw [hw x, ← hbr]

end

end Work.ThomBordism
