import Mathlib
import Submission.Work.ThomBordism.levelModelAssembly
import Submission.Work.ThomBordism.exists_relFundClass_of_pieces_bound
import Submission.Work.ThomBordism.sourceCoord
import Submission.Work.Cohomology.good_empty

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the class datum of the raw level model from the boundary coordination

`Work.ThomBordism.levelClassData_of_coord`: the recorded boundary coordination of the source
construction (`Work.ThomBordism.SourceBoundaryCoord`, the vanishing of the class of the pieces under
the inclusion of the boundary part of the raw level set into the level set) together with the collar
and the orientation family of the raw level model (`Work.ThomBordism.LevelOrientationHyp`) produce the
class datum `Work.ThomBordism.LevelClassData` of the level model.

The mathematical content is the `w_fund` bookkeeping of
`Work.ThomBordism.exists_relFundClass_of_pieces_bound`; the work here is the *identification* of the
boundary class of the lemma (`Σ_i (e.symm ∘ sigmaMk_i)_* c_i` with `e` the collapse identification of
`levelBdryHomeoFull`) with the recorded coordination (`Work.ThomBordism.sourceBoundaryClass`): the two
differ only in the presentation of the boundary part — the canonical (`Lvl`) boundary
`(𝓡∂ 9).boundary S.Pre` versus the raw boundary part `sourceLevelBdry D0` of the source data — and the
two presentations are identified by `Work.PTGeometric.Lvl.Setup.mem_boundary_iff`.

The technical heart is `boundaryClass_transfer` below: if two maps into the two presentations of the
boundary part agree pointwise (through the canonical homeomorphism of the two subtypes), then the
images of the pieces' fundamental classes under the two inclusions-and-collapses agree.

## Note on the axiom check (`declare_proven`)

Both declarations of this file are `sorry`-free and prove what they claim; `boundaryClass_transfer` is
axiom-clean (`#print axioms` = `propext, Classical.choice, Quot.sound`), and the proof of
`levelClassData_of_coord` introduces no axioms at all: it never unfolds `producedRawData`, it works for
*any* raw datum satisfying the two hypotheses.  Nevertheless `#print axioms
Work.ThomBordism.levelClassData_of_coord` reports `sorryAx`, because `#print axioms` also collects the
axioms of the **type**, and the type mentions `Work.PTGeometric.producedRawData`, whose definition is
`Classical.choose (exists_rawAmbientData_tiedCollar …)`,
`exists_rawAmbientData_tiedCollar = Work.ThomBordism.sourceRawAmbientData_tied_collar`, and *that*
proof has one `sorry` (the boundary coordination of the last mile) at
`Submission/Work/ThomBordism/sourceRawAmbientData_tied_collar.lean:1112`.  Nothing in this file can
remove that taint: it is a property of the *definition* of `producedRawData`, in another agent's file.

The full analysis, and a **verified three-edit fix** that makes `producedRawData` (and hence this
lemma) axiom-clean without changing any type, are in
`Submission/Work/ThomBordism/NOTE_TAINT_levelClassData.md`; the clean witness it uses is
`Submission/Work/ThomBordism/cleanProducedRawData.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter
open CategoryTheory CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

open Work.PTGeometric Work.Cohomology

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
  {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]

/-- **Transfer of the boundary class along an identification of the boundary part.**

If `A₀` and `A₁` are the same subset of `X`, and two families of maps `f i : V_i → A₀`,
`g i : V_i → A₁` agree pointwise through the canonical homeomorphism `A₀ ≅ A₁` (the subtype map
induced by the equality of the two sets), then the sums of the images of the fundamental classes
`c_i` under the two inclusions coincide. -/
theorem boundaryClass_transfer {X : TopCat} {A₀ A₁ : Set X} (hA : A₀ = A₁)
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (f : ∀ i, (Fam i).X ⟶ TopCat.of A₀) (g : ∀ i, (Fam i).X ⟶ TopCat.of A₁)
    (hfg : ∀ i y, Homeomorph.setCongr hA (ConcreteCategory.hom (f i) y)
      = ConcreteCategory.hom (g i) y) :
    (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A₀) 8).hom
        (∑ i, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (Fam i).X (TopCat.of A₀) (f i)) 8 (Fam i).c)
      = (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A₁) 8).hom
        (∑ i, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (Fam i).X (TopCat.of A₁) (g i)) 8 (Fam i).c) := by
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
  have hterm : ∀ i, Work.Cohomology.chainMap ℤ (Fam i).X (TopCat.of A₁) (g i)
      = Work.Cohomology.chainMap ℤ (Fam i).X (TopCat.of A₀) (f i)
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
        (Work.Cohomology.chainMap ℤ (Fam i).X (TopCat.of A₁) (g i)) 8).hom (Fam i).c
      = (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of A₀) (TopCat.of A₁) Ψ) 8).hom
        ((HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (Fam i).X (TopCat.of A₀) (f i)) 8).hom (Fam i).c) := by
    rw [hterm i, HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply]
  rw [h1, key2]

theorem levelClassData_of_coord
    {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (hk : 11 ≤ k) (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (hset : Work.ThomBordism.sourceLevelSet (Work.PTGeometric.producedRawData hk G m hm hpow) ∩
        (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (Work.PTGeometric.producedRawData hk G m hm hpow).M
      = (Work.PTGeometric.toAmbientCollapseEnd (Nat.le_add_right k G.mU)
          (Work.PTGeometric.producedAmbientData hk G m hm hpow)).S ∩
        {x | (Work.PTGeometric.toAmbientCollapseEnd (Nat.le_add_right k G.mU)
          (Work.PTGeometric.producedAmbientData hk G m hm hpow)).v x = 0})
    {hWcl : IsClosed (Work.ThomBordism.sourceLevelSet
      (Work.PTGeometric.producedRawData hk G m hm hpow))}
    {L : Work.PTGeometric.LocalLevelData k (Work.PTGeometric.producedRawData hk G m hm hpow).M
      (Work.ThomBordism.sourceLevelSet (Work.PTGeometric.producedRawData hk G m hm hpow))}
    (hcolγ : Work.ThomBordism.LevelOrientationHyp hk G m hm hpow (hWcl := hWcl) (L := L))
    (hcoord : Work.ThomBordism.SourceBoundaryCoord
      (Work.PTGeometric.producedRawData hk G m hm hpow)) :
    Work.ThomBordism.LevelClassData hk G m hm hpow hset (hWcl := hWcl) (L := L) := by
  classical
  obtain ⟨hcol, γ, hγ⟩ := hcolγ
  let S : Work.PTGeometric.Lvl.Setup k :=
    Work.PTGeometric.levelSetup
      (Work.ThomBordism.sourceLevelSet (Work.PTGeometric.producedRawData hk G m hm hpow)) hWcl L
  letI := Work.PTGeometric.Lvl.Setup.instChartedSpace S
  by_cases hne : Nonempty S.Pre
  · -- ## the nonempty case: the class of the pieces is transferred to the produced presentation
    haveI := hne
    refine Work.ThomBordism.exists_relFundClass_of_pieces_bound (W := S.Pre) hcol
      (Work.ThomBordism.levelBdryHomeoFull hk G m hm hpow hset (hWcl := hWcl) (L := L))
      (γ := γ) hγ ?_
    -- the identification of the two presentations of the boundary part
    have hA : (modelWithCornersEuclideanHalfSpace 9).boundary S.Pre
        = Work.ThomBordism.sourceLevelBdry
            (Work.PTGeometric.producedRawData hk G m hm hpow) :=
      Set.ext fun x => Work.PTGeometric.Lvl.Setup.mem_boundary_iff S x
    refine (boundaryClass_transfer (X := TopCat.of S.Pre) hA
        (fun i => TopCat.ofHom ⟨fun y =>
          (Work.ThomBordism.levelBdryHomeoFull hk G m hm hpow hset (hWcl := hWcl) (L := L)).symm
            ⟨i, y⟩,
          (Work.ThomBordism.levelBdryHomeoFull hk G m hm hpow hset (hWcl := hWcl) (L := L)).continuous_invFun.comp
            continuous_sigmaMk⟩)
        (fun i => TopCat.ofHom (Work.ThomBordism.piecePush
          (Work.PTGeometric.producedRawData hk G m hm hpow) i))
        (fun i y => Subtype.ext (Subtype.ext rfl))).trans ?_
    exact hcoord
  · -- ## the empty case: the boundary part is empty
    haveI hSp : IsEmpty S.Pre := not_nonempty_iff.mp hne
    haveI hb : IsEmpty ↥((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre) :=
      ⟨fun x => hSp.false x.1⟩
    haveI hZ : Subsingleton ((singularChains ℤ
        (TopCat.of ((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre))).homology 8) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_singularChains_homology_of_isEmpty
          (TopCat.of ((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre)) 8)
    refine ⟨0, ?_, ?_⟩
    · intro x
      exact (hSp.false x).elim
    · rw [map_zero]
      exact Subsingleton.elim _ _

end

end Work.ThomBordism
