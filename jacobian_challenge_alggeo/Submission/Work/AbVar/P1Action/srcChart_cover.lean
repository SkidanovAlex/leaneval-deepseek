/-
Area AV: the scaled `𝔾_m`-action on `ℙ¹` — the two charts cover the source `ℙ¹ ⊗ 𝔾_m`.

The source is the explicit model `srcScheme k = ℙ¹ ×_{Spec k} Spec k[T;T⁻¹]` and the charts are
`Spec (chartRing k i ⊗[k] k[T;T⁻¹])`, included by `srcChartι k i`.  We prove that the two chart
inclusions cover the source,

  `iSup (fun i : Fin 2 => (srcChartι k i).opensRange) = ⊤`,

by computing the range of `srcChartι k i`: it is the preimage under the projection
`pullback.fst (P1 k).hom (gmHom k)` of the standard chart `D₊(Xᵢ)` of `ℙ¹`, and the two standard
charts `D₊(X₀)`, `D₊(X₁)` cover `ℙ¹`.

The computation of the range goes through the pasting isomorphism
`pullbackRightPullbackFstIso`, which identifies the chart source `Spec (chartRing k i ⊗[k] k[T;T⁻¹])`
with the pullback `Spec (chartRing k i) ×_{ℙ¹} (ℙ¹ ×_{Spec k} Spec k[T;T⁻¹])`; the range of the
projection of that pullback to the source is `Scheme.Hom.opensRange_pullbackSnd`.
-/
import Mathlib
import Submission.Work.AbVar.P1Action.SourceChart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry MonObj MvPolynomial HomogeneousLocalization Limits
  RingHomClass
open scoped MonoidalCategory TensorProduct AlgebraicGeometry

namespace Work.AbVar.P1Action

section

variable (k : Type*) [Field k]

/-- The chart `D₊(Xᵢ) × 𝔾_m` of the source is the preimage of the standard chart `D₊(Xᵢ)` of `ℙ¹`
under the projection `ℙ¹ × Spec k[T;T⁻¹] ⟶ ℙ¹`. -/
private lemma srcChart_cover_range (i : Fin 2) :
    (srcChartι k i).opensRange
      = pullback.fst (Work.AbVar.P1 k).hom (gmHom k) ⁻¹ᵁ
          (Proj.basicOpen (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i)) := by
  -- the pasting isomorphism `Spec (chartRing k i) ×_{ℙ¹} (ℙ¹ ×_k 𝔾_m) ≅ Spec (chartRing k i ⊗ L)`
  have hmain : (pullbackRightPullbackFstIso (Work.AbVar.P1 k).hom (gmHom k) (chartObjHom k i)).hom
        ≫ srcChartMap k i
      = pullback.snd (chartObjHom k i) (pullback.fst (Work.AbVar.P1 k).hom (gmHom k)) := by
    apply pullback.hom_ext
    · rw [Category.assoc, srcChartMap_fst, ← Category.assoc, pullbackRightPullbackFstIso_hom_fst,
        ← pullback.condition]
    · rw [Category.assoc, srcChartMap_snd, pullbackRightPullbackFstIso_hom_snd]
  have key : srcChartMap k i
      = (pullbackRightPullbackFstIso (Work.AbVar.P1 k).hom (gmHom k) (chartObjHom k i)).inv
        ≫ pullback.snd (chartObjHom k i) (pullback.fst (Work.AbVar.P1 k).hom (gmHom k)) := by
    rw [← hmain, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hι : srcChartι k i
      = ((srcChartIso k i).inv ≫
          (pullbackRightPullbackFstIso (Work.AbVar.P1 k).hom (gmHom k) (chartObjHom k i)).inv)
        ≫ pullback.snd (chartObjHom k i) (pullback.fst (Work.AbVar.P1 k).hom (gmHom k)) := by
    rw [srcChartι, key, Category.assoc]
  -- the range of the projection of the pasted pullback is the required preimage
  have haw : (chartObjHom k i).opensRange
      = Proj.basicOpen (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i) :=
    Proj.opensRange_awayι (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i)
      (Work.AbVar.ProjectiveLine.X_mem_stdG i) (by norm_num)
  have hrange_snd : Set.range
        (pullback.snd (chartObjHom k i) (pullback.fst (Work.AbVar.P1 k).hom (gmHom k)))
      = ↑(pullback.fst (Work.AbVar.P1 k).hom (gmHom k) ⁻¹ᵁ
          Proj.basicOpen (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i)) := by
    rw [IsOpenImmersion.range_pullbackSnd, haw]
  -- the first component of `hι` is an isomorphism, hence surjective
  have hrange_ι : Set.range (srcChartι k i)
      = Set.range (pullback.snd (chartObjHom k i) (pullback.fst (Work.AbVar.P1 k).hom (gmHom k))) := by
    rw [hι]
    show Set.range (⇑(pullback.snd (chartObjHom k i) (pullback.fst (Work.AbVar.P1 k).hom (gmHom k)))
      ∘ ⇑((srcChartIso k i).inv ≫ (pullbackRightPullbackFstIso (Work.AbVar.P1 k).hom (gmHom k)
          (chartObjHom k i)).inv))
      = Set.range ⇑(pullback.snd (chartObjHom k i) (pullback.fst (Work.AbVar.P1 k).hom (gmHom k)))
    rw [Function.Surjective.range_comp _ _]
    exact (Scheme.homeoOfIso ((srcChartIso k i).symm ≪≫
      (pullbackRightPullbackFstIso (Work.AbVar.P1 k).hom (gmHom k) (chartObjHom k i)).symm)).surjective
  exact TopologicalSpace.Opens.ext (hrange_ι.trans hrange_snd)

/-- The two standard charts `D₊(X₀)`, `D₊(X₁)` cover `ℙ¹ = Proj k[X₀,X₁]`. -/
private lemma srcChart_cover_proj (k : Type*) [Field k] :
    (⨆ i : Fin 2, Proj.basicOpen (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · intro i
    exact ⟨1, Work.AbVar.ProjectiveLine.X_mem_stdG i⟩
  · rw [eq_top_iff]
    intro p hp
    clear hp
    induction p using MvPolynomial.induction_on with
    | C a =>
        have hmem : (MvPolynomial.C a : MvPolynomial (Fin 2) k) ∈
            Work.AbVar.ProjectiveLine.StdG k 0 :=
          (MvPolynomial.mem_homogeneousSubmodule 0 _).mpr (MvPolynomial.isHomogeneous_C (Fin 2) a)
        have hmap : (MvPolynomial.C a : MvPolynomial (Fin 2) k) =
            algebraMap (↥(Work.AbVar.ProjectiveLine.StdG k 0)) (MvPolynomial (Fin 2) k)
              ⟨MvPolynomial.C a, hmem⟩ :=
          (SetLike.GradeZero.algebraMap_apply (A := Work.AbVar.ProjectiveLine.StdG k)
            ⟨MvPolynomial.C a, hmem⟩).symm
        rw [hmap]
        exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => exact add_mem hp hq
    | mul_X p n hp => exact mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self n))

theorem srcChart_cover (k : Type*) [Field k] :
    iSup (fun i : Fin 2 => (Work.AbVar.P1Action.srcChartι k i).opensRange) = ⊤ := by
  have hrange : ∀ i : Fin 2, (srcChartι k i).opensRange
      = pullback.fst (Work.AbVar.P1 k).hom (gmHom k) ⁻¹ᵁ
          (Proj.basicOpen (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i)) :=
    fun i => srcChart_cover_range k i
  calc iSup (fun i : Fin 2 => (srcChartι k i).opensRange)
      = iSup (fun i : Fin 2 => pullback.fst (Work.AbVar.P1 k).hom (gmHom k) ⁻¹ᵁ
          (Proj.basicOpen (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i))) :=
        iSup_congr hrange
    _ = pullback.fst (Work.AbVar.P1 k).hom (gmHom k) ⁻¹ᵁ
          (⨆ i : Fin 2, Proj.basicOpen (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i)) :=
        (Scheme.Hom.preimage_iSup _ _).symm
    _ = pullback.fst (Work.AbVar.P1 k).hom (gmHom k) ⁻¹ᵁ ⊤ := by
        rw [show (⨆ i : Fin 2, Proj.basicOpen (Work.AbVar.ProjectiveLine.StdG k)
              (MvPolynomial.X i) : ((Work.AbVar.P1 k).left).Opens) = ⊤ from
          srcChart_cover_proj k]
    _ = ⊤ := Scheme.Hom.preimage_top _

end

end Work.AbVar.P1Action
