import Mathlib
import Submission.Work.Agree.Basic
import Submission.Work.Agree.presentation_independence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## 1. The chain rule for conjugation by a continuous linear equivalence -/

/-- The derivative of `z ↦ L (g (L.symm z))` at `L u` is `L ∘ fderiv g u ∘ L.symm`. -/
lemma fderiv_cle_conj {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (L : E ≃L[ℝ] E') (g : E → E) (u : E) :
    fderiv ℝ (fun z => L (g (L.symm z))) (L u) =
      (L : E →L[ℝ] E').comp ((fderiv ℝ g u).comp (L.symm : E' →L[ℝ] E)) := by
  by_cases h : DifferentiableAt ℝ g u
  · have hg : HasFDerivAt g (fderiv ℝ g u) (L.symm (L u)) := by
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact h.hasFDerivAt
    have hinner : HasFDerivAt (fun z : E' => g (L.symm z))
        ((fderiv ℝ g u).comp (L.symm : E' →L[ℝ] E)) (L u) :=
      HasFDerivAt.comp (L u) hg (L.symm.hasFDerivAt)
    have houter : HasFDerivAt (fun z : E' => L (g (L.symm z)))
        ((L : E →L[ℝ] E').comp ((fderiv ℝ g u).comp (L.symm : E' →L[ℝ] E))) (L u) :=
      HasFDerivAt.comp (L u) (L.hasFDerivAt) hinner
    exact houter.fderiv
  · have h0 : fderiv ℝ g u = 0 := fderiv_zero_of_not_differentiableAt h
    have hz : fderiv ℝ (fun z : E' => L (g (L.symm z))) (L u) = 0 := by
      refine fderiv_zero_of_not_differentiableAt (fun hd => h ?_)
      have h1 : DifferentiableAt ℝ (fun w : E => L (g w)) u := by
        have h2 := (ContinuousLinearEquiv.comp_right_differentiableAt_iff (iso := L.symm)
          (f := fun w : E => L (g w)) (x := L u)).mp hd
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using h2
      exact (ContinuousLinearEquiv.comp_differentiableAt_iff (iso := L) (f := g) (x := u)).mp h1
    rw [h0, hz, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]

/-! ## 2. Model transfer for the tangent bundle -/

section Push

variable {E H M E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [ChartedSpace H M]

/-- The chart of the pushed-forward atlas corresponding to a chart of the original atlas. -/
noncomputable def pushAtlasIndex (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (L : E ≃L[ℝ] E') (i : atlas H M) :
    @atlas E' _ M _ (Work.Morse.pushChartedSpace (Work.Morse.modelHomeo I L)) :=
  ⟨Work.Morse.pushChart (Work.Morse.modelHomeo I L) i.1, by
    rw [Work.Morse.pushChartedSpace_atlas]
    exact ⟨i.1, i.2, rfl⟩⟩

@[simp] theorem pushAtlasIndex_coe (L : E ≃L[ℝ] E') (i : atlas H M) :
    (pushAtlasIndex (I := I) L i).1 = Work.Morse.pushChart (Work.Morse.modelHomeo I L) i.1 :=
  rfl

/-- The extended pushed chart is the old extended chart followed by `L`. -/
lemma coe_extend_pushChart (L : E ≃L[ℝ] E') (a : OpenPartialHomeomorph M H) :
    ⇑((Work.Morse.pushChart (Work.Morse.modelHomeo I L) a).extend (𝓘(ℝ, E')))
      = fun x => (L : E →L[ℝ] E') (⇑(a.extend I) x) := by
  funext x
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe, Work.Morse.pushChart_apply,
    Work.Morse.modelHomeo_apply, modelWithCornersSelf_coe, id_eq]
  rfl

/-- The inverse of the extended pushed chart is the inverse of the old extended chart after
`L.symm`. -/
lemma coe_symm_extend_pushChart (L : E ≃L[ℝ] E') (a : OpenPartialHomeomorph M H) :
    ⇑(((Work.Morse.pushChart (Work.Morse.modelHomeo I L) a).extend (𝓘(ℝ, E'))).symm)
      = fun y => ⇑((a.extend I).symm) ((L.symm : E' →L[ℝ] E) y) := by
  funext y
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe_symm, Work.Morse.pushChart,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_apply,
    Homeomorph.toOpenPartialHomeomorph_symm_apply, Work.Morse.modelHomeo_symm_apply,
    modelWithCornersSelf_coe_symm, id_eq]
  rfl

/-- The coordinate change of the tangent bundle, in terms of extended charts. -/
lemma tangentBundle_coordChange_eq [IsManifold I 1 M] (i j : atlas H M) (x : M) :
    (Work.TangentClasses.tangentBundle I M).coordChange i j x
      = fderivWithin ℝ (⇑(j.1.extend I) ∘ ⇑((i.1.extend I).symm)) (Set.range I)
          (⇑(i.1.extend I) x) := rfl

/-- **Model transfer.** If the atlas of `M` is pushed forward along the model change
`modelHomeo I L : H ≃ₜ E'`, the tangent bundle of `M` in the new charting is the `L`-change of
fibre of the tangent bundle in the old charting. -/
theorem tangentBundle_pushChartedSpace [IsManifold I 1 M] [IsManifold I ∞ M]
    (L : E ≃L[ℝ] E') :
    letI : ChartedSpace E' M := Work.Morse.pushChartedSpace (Work.Morse.modelHomeo I L)
    letI : IsManifold (𝓘(ℝ, E')) 1 M :=
      (Work.Morse.push_isManifold (M := M) (I := I) L).of_le (by simp)
    Nonempty (Work.Thom.BundleIso
      ((Work.TangentClasses.tangentBundle I M).mapFibre L)
      (Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M)) := by
  letI : ChartedSpace E' M := Work.Morse.pushChartedSpace (Work.Morse.modelHomeo I L)
  letI : IsManifold (𝓘(ℝ, E')) 1 M :=
    (Work.Morse.push_isManifold (M := M) (I := I) L).of_le (by simp)
  let c : atlas H M → atlas E' M := fun i => pushAtlasIndex (I := I) L i
  have hc : ∀ i : atlas H M, (c i).1 = Work.Morse.pushChart (Work.Morse.modelHomeo I L) i.1 :=
    fun i => by simp only [c, pushAtlasIndex_coe]
  have hZ : ∀ (i j : atlas H M) (x : M),
      ((Work.TangentClasses.tangentBundle I M).mapFibre L).coordChange i j x
        = (Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).coordChange (c i) (c j) x := by
    intro i j x
    ext v
    rw [Work.TangentClasses.RealBundle.mapFibre_coordChange]
    simp only [ContinuousLinearMap.comp_apply]
    have hfun : (⇑((c j).1.extend (𝓘(ℝ, E'))) ∘ ⇑(((c i).1.extend (𝓘(ℝ, E'))).symm))
        = fun z : E' => (L : E →L[ℝ] E')
            ((⇑(j.1.extend I) ∘ ⇑((i.1.extend I).symm)) ((L.symm : E' →L[ℝ] E) z)) := by
      funext z
      simp only [Function.comp_apply, hc, coe_extend_pushChart, coe_symm_extend_pushChart]
    have hpt : ⇑((c i).1.extend (𝓘(ℝ, E'))) x = (L : E →L[ℝ] E') (⇑(i.1.extend I) x) := by
      rw [hc i, coe_extend_pushChart]
    rw [show (Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).coordChange (c i) (c j) x
        = fderivWithin ℝ (⇑((c j).1.extend (𝓘(ℝ, E'))) ∘ ⇑(((c i).1.extend (𝓘(ℝ, E'))).symm))
            (Set.range (𝓘(ℝ, E'))) (⇑((c i).1.extend (𝓘(ℝ, E'))) x) from rfl]
    rw [show (Work.TangentClasses.tangentBundle I M).coordChange i j x
        = fderivWithin ℝ (⇑(j.1.extend I) ∘ ⇑((i.1.extend I).symm)) (Set.range I)
            (⇑(i.1.extend I) x) from rfl]
    rw [hfun, hpt]
    rw [ModelWithCorners.range_eq_univ (𝓘(ℝ, E')), ModelWithCorners.range_eq_univ I]
    rw [fderivWithin_univ, fderivWithin_univ]
    have hchain := congrArg (fun A : E' →L[ℝ] E' => A v)
      (fderiv_cle_conj L (⇑(j.1.extend I) ∘ ⇑((i.1.extend I).symm)) (⇑(i.1.extend I) x))
    simp only [ContinuousLinearMap.comp_apply] at hchain
    exact hchain.symm
  have hZ' : ∀ (i j : atlas E' M) (x : M),
      (Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).coordChange i j x
        = (Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).coordChange (id i) (id j) x :=
    fun i j x => rfl
  have hcont : ∀ (i : atlas H M) (i' : atlas E' M),
      ContinuousOn (fun x : M =>
        ((Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).coordChange
          ((Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).indexAt x) i' x).comp
        (((Work.TangentClasses.tangentBundle I M).mapFibre L).coordChange
          i (((Work.TangentClasses.tangentBundle I M).mapFibre L).indexAt x) x))
      (((Work.TangentClasses.tangentBundle I M).mapFibre L).baseSet i ∩
        (Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).baseSet i') := by
    intro i i'
    obtain ⟨j', hj'⟩ : ∃ j : atlas H M, (c j).1 = i'.1 := by
      have hmem : i'.1 ∈ Work.Morse.pushChart (Work.Morse.modelHomeo I L) '' atlas H M := by
        simpa only [Work.Morse.pushChartedSpace_atlas] using i'.2
      obtain ⟨e, he, hfe⟩ := hmem
      exact ⟨⟨e, he⟩, by simpa only [c, pushAtlasIndex_coe] using hfe⟩
    have hbase : (Work.TangentClasses.tangentBundle I M).baseSet j'
        = (Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).baseSet i' := by
      rw [Work.TangentClasses.tangentBundle_baseSet, Work.TangentClasses.tangentBundle_baseSet,
        ← hj']
      simp only [c, pushAtlasIndex_coe, Work.Morse.pushChart_source]
    have hbaseZ : ((Work.TangentClasses.tangentBundle I M).mapFibre L).baseSet i
        ∩ (Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).baseSet i'
        = (Work.TangentClasses.tangentBundle I M).baseSet i
          ∩ (Work.TangentClasses.tangentBundle I M).baseSet j' := by
      rw [Work.TangentClasses.RealBundle.mapFibre_baseSet, hbase]
    have hkey : ∀ x ∈ ((Work.TangentClasses.tangentBundle I M).mapFibre L).baseSet i
        ∩ (Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).baseSet i',
        ((Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).coordChange
            ((Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).indexAt x) i' x).comp
          (((Work.TangentClasses.tangentBundle I M).mapFibre L).coordChange
            i (((Work.TangentClasses.tangentBundle I M).mapFibre L).indexAt x) x)
        = (L : E →L[ℝ] E').comp
            (((Work.TangentClasses.tangentBundle I M).coordChange i j' x).comp
              (L.symm : E' →L[ℝ] E)) := by
      intro x hx
      have h1 : (Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).coordChange
            ((Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).indexAt x) i' x
          = (Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).coordChange
            ((Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).indexAt x) (c j') x := by
        rw [← Subtype.ext hj']
      have h2 : ((Work.TangentClasses.tangentBundle I M).mapFibre L).coordChange
            i (((Work.TangentClasses.tangentBundle I M).mapFibre L).indexAt x) x
          = (L : E →L[ℝ] E').comp
              (((Work.TangentClasses.tangentBundle I M).coordChange i
                ((Work.TangentClasses.tangentBundle I M).indexAt x) x).comp
                (L.symm : E' →L[ℝ] E)) := by
        rw [Work.TangentClasses.RealBundle.mapFibre_coordChange,
          Work.TangentClasses.RealBundle.mapFibre_indexAt]
      have h3 : (Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).coordChange
            ((Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).indexAt x) (c j') x
          = (L : E →L[ℝ] E').comp
              (((Work.TangentClasses.tangentBundle I M).coordChange
                ((Work.TangentClasses.tangentBundle I M).indexAt x) j' x).comp
                (L.symm : E' →L[ℝ] E)) := by
        have h := hZ ((Work.TangentClasses.tangentBundle I M).indexAt x) j' x
        have hchart : c ((Work.TangentClasses.tangentBundle I M).indexAt x)
            = (Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M).indexAt x := by
          apply Subtype.ext
          simp only [c, pushAtlasIndex_coe, Work.TangentClasses.tangentBundle,
            tangentBundleCore_indexAt, coe_achart, Work.Morse.pushChartedSpace_chartAt]
        rw [← hchart, ← h, Work.TangentClasses.RealBundle.mapFibre_coordChange]
      have hmem : x ∈ (Work.TangentClasses.tangentBundle I M).baseSet i
          ∩ (Work.TangentClasses.tangentBundle I M).baseSet
              ((Work.TangentClasses.tangentBundle I M).indexAt x)
          ∩ (Work.TangentClasses.tangentBundle I M).baseSet j' := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · simpa only [Work.TangentClasses.RealBundle.mapFibre_baseSet] using hx.1
        · exact (Work.TangentClasses.tangentBundle I M).mem_baseSet_at x
        · rw [hbase]
          simpa only [Work.TangentClasses.RealBundle.mapFibre_baseSet] using hx.2
      have hcyc := (Work.TangentClasses.tangentBundle I M).coordChange_comp i
        ((Work.TangentClasses.tangentBundle I M).indexAt x) j' x hmem
      rw [h1, h3, h2]
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply]
      exact congrArg L (hcyc (L.symm v))
    refine ContinuousOn.congr ?_ hkey
    rw [hbaseZ]
    exact ((continuous_const : Continuous fun _ : M => (L : E →L[ℝ] E')).continuousOn).clm_comp
      (((Work.TangentClasses.tangentBundle I M).continuousOn_coordChange i j').clm_comp
        continuousOn_const)
  exact presentation_independence (I := (𝓘(ℝ, E') : ModelWithCorners ℝ E' E'))
    (E := E') (H := E') (M := M) (ι := atlas H M) (ι' := atlas E' M)
    ((Work.TangentClasses.tangentBundle I M).mapFibre L)
    (Work.TangentClasses.tangentBundle (𝓘(ℝ, E')) M) c id hZ hZ' hcont

end Push

theorem modelTransfer (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) : Work.Agree.ModelTransfer F hF := by
  exact tangentBundle_pushChartedSpace (I := Work.Milnor.mMSpace8)
    (E := Submission.Milnor.MSpace8) (H := Submission.Milnor.MSpace8)
    (E' := EuclideanSpace ℝ (Fin 8))
    (M := Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))
    Work.Milnor.vkModelIso

end

end Work.Agree
