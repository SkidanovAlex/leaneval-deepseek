import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Gen.EulerToolkit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The Whitney sum of isomorphic bundles is isomorphic

This module proves **congruence of the Whitney sum** for the gluing-data model of real vector
bundles: if `Z ≅ Z'` and `W ≅ W'` are bundle isomorphisms, then the direct sums
`Z ⊕ W ≅ Z' ⊕ W'` are isomorphic (`Work.Agree.whitneySumRCongr`, the requested lemma), and more
generally for the sum glued along arbitrary splittings `F₁ × F₂ ≃L F`, `F₁' × F₂' ≃L F'`
(`Work.Agree.nonempty_bundleIso_sumCore_congr`).

Nothing here is specific to the fibres being Euclidean spaces: the summands are arbitrary
finite-dimensional `𝕜`-vector bundles and the two sums are allowed to have *different* model fibres
(which is exactly what happens for `Wh`, whose summands `Z ≅ Z'` have fibres `ℝ^{k₁}`, `ℝ^{k₂}`).

## The proof, in one line

For a bundle isomorphism `e : Z → Z'` the fibrewise map is a linear map `e.hom b : F₁ → F₁'`, only
continuous a posteriori; the sum isomorphism is *defined* by conjugating the block-diagonal map
`e.hom b × e'.hom b` by the two splittings.  The inverse laws are then immediate, and the
continuity of the induced map of total spaces is the chart-by-chart computation of
`Work.Thom.continuous_totalSpaceMap_clm_gen`, whose input is the trivial

`(SF' ∘ (A₁ × A₂) ∘ SF'⁻¹) ∘ (SF' ∘ (e × e') ∘ SF⁻¹) ∘ (SF ∘ (C₁ × C₂) ∘ SF⁻¹)
  = SF' ∘ ((A₁ ∘ e ∘ C₁) × (A₂ ∘ e' ∘ C₂)) ∘ SF⁻¹`

(`Work.Agree.sumCore_conj_identity`): the outer splittings cancel and the block-diagonal maps
compose componentwise.  The chart expressions `A₁ ∘ e ∘ C₁` and `A₂ ∘ e' ∘ C₂` are exactly the ones
whose continuity is `Work.Thom.continuousOn_chartExpressionCLM_gen`.

## What is here

* `Work.Agree.prodMap_comp_prodMap` — the block-diagonal maps compose componentwise;
* `Work.Agree.sumCore_conj_identity` — the conjugation identity above;
* `Work.Agree.nonempty_bundleIso_sumCore_congr` — the general congruence;
* `Work.Agree.whitneySumRCongr` — the real Whitney sum `whitneySumR` of congruent summands is
  isomorphic (the requested statement).
-/

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## Block-diagonal maps compose componentwise -/

/-- **The product of two continuous linear maps composes componentwise**:
`(f × g) ∘ (f' × g') = (f ∘ f') × (g ∘ g')`. -/
theorem prodMap_comp_prodMap {𝕜 : Type*} [Semiring 𝕜]
    {M₁ M₂ M₃ M₄ M₅ M₆ : Type*}
    [TopologicalSpace M₁] [AddCommMonoid M₁] [Module 𝕜 M₁]
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module 𝕜 M₂]
    [TopologicalSpace M₃] [AddCommMonoid M₃] [Module 𝕜 M₃]
    [TopologicalSpace M₄] [AddCommMonoid M₄] [Module 𝕜 M₄]
    [TopologicalSpace M₅] [AddCommMonoid M₅] [Module 𝕜 M₅]
    [TopologicalSpace M₆] [AddCommMonoid M₆] [Module 𝕜 M₆]
    (f : M₁ →L[𝕜] M₂) (g : M₃ →L[𝕜] M₄) (f' : M₅ →L[𝕜] M₁) (g' : M₆ →L[𝕜] M₃) :
    (f.prodMap g).comp (f'.prodMap g') = (f.comp f').prodMap (g.comp g') := by
  apply ContinuousLinearMap.ext
  rintro ⟨a, b⟩
  simp [ContinuousLinearMap.coe_prodMap']

/-! ## The conjugation identity -/

/-- **The conjugation identity of the sum.**  The three transition-function expressions of the sum
(target chart, gauge, source chart), conjugated by the two splittings `SF`, `SF'`, collapse to the
block-diagonal of the individual chart expressions: the middle `SF'⁻¹` cancels the outer `SF'` and
the middle `SF⁻¹` cancels the outer `SF`, leaving `SF' ∘ ((A₁ ∘ B₁ ∘ C₁) × (A₂ ∘ B₂ ∘ C₂)) ∘ SF⁻¹`.

The statement is field-general and involves only continuous linear maps on product types. -/
theorem sumCore_conj_identity {𝕜 : Type*} [Semiring 𝕜]
    {F₁ F₂ F F₁' F₂' F' : Type*}
    [TopologicalSpace F₁] [AddCommMonoid F₁] [Module 𝕜 F₁]
    [TopologicalSpace F₂] [AddCommMonoid F₂] [Module 𝕜 F₂]
    [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜 F]
    [TopologicalSpace F₁'] [AddCommMonoid F₁'] [Module 𝕜 F₁']
    [TopologicalSpace F₂'] [AddCommMonoid F₂'] [Module 𝕜 F₂']
    [TopologicalSpace F'] [AddCommMonoid F'] [Module 𝕜 F']
    (SF : (F₁ × F₂) ≃L[𝕜] F) (SF' : (F₁' × F₂') ≃L[𝕜] F')
    (A₁ : F₁' →L[𝕜] F₁') (A₂ : F₂' →L[𝕜] F₂')
    (B₁ : F₁ →L[𝕜] F₁') (B₂ : F₂ →L[𝕜] F₂')
    (C₁ : F₁ →L[𝕜] F₁) (C₂ : F₂ →L[𝕜] F₂) :
    ((SF' : (F₁' × F₂') →L[𝕜] F').comp
        ((A₁.prodMap A₂).comp (SF'.symm : F' →L[𝕜] (F₁' × F₂')))).comp
      (((SF' : (F₁' × F₂') →L[𝕜] F').comp
          ((B₁.prodMap B₂).comp (SF.symm : F →L[𝕜] (F₁ × F₂)))).comp
        ((SF : (F₁ × F₂) →L[𝕜] F).comp
          ((C₁.prodMap C₂).comp (SF.symm : F →L[𝕜] (F₁ × F₂)))))
    = (SF' : (F₁' × F₂') →L[𝕜] F').comp
        (((A₁.comp (B₁.comp C₁)).prodMap (A₂.comp (B₂.comp C₂))).comp
          (SF.symm : F →L[𝕜] (F₁ × F₂))) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap',
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  -- pointwise, both sides are `SF'` applied to the block-diagonal of `Aᵢ ∘ Bᵢ ∘ Cᵢ` at `SF⁻¹ v`
  congr 1

/-! ## The congruence of the sum -/

/-- **Congruence of the direct sum of two gluing data.**  Two bundle isomorphisms
`e : Z ≅ Z'`, `e' : W ≅ W'` (with possibly different model fibres!) induce an isomorphism of the
sums glued along arbitrary splittings `SF`, `SF'` of the summand fibres into the sum fibres. -/
theorem nonempty_bundleIso_sumCore_congr {𝕜 : Type*} [RCLike 𝕜]
    {B : Type} [TopologicalSpace B]
    {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
      [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {F₁' F₂' : Type*} [NormedAddCommGroup F₁'] [NormedSpace 𝕜 F₁'] [FiniteDimensional 𝕜 F₁']
      [NormedAddCommGroup F₂'] [NormedSpace 𝕜 F₂'] [FiniteDimensional 𝕜 F₂']
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    {ι₁ ι₂ ι₁' ι₂' : Type}
    (SF : (F₁ × F₂) ≃L[𝕜] F) (SF' : (F₁' × F₂') ≃L[𝕜] F')
    (Z : VectorBundleCore 𝕜 B F₁ ι₁) (Z' : VectorBundleCore 𝕜 B F₁' ι₁')
    (W : VectorBundleCore 𝕜 B F₂ ι₂) (W' : VectorBundleCore 𝕜 B F₂' ι₂')
    (e : Work.Thom.BundleIso Z Z') (e' : Work.Thom.BundleIso W W') :
    Nonempty (Work.Thom.BundleIso (Work.Whitney.sumCore SF Z W)
      (Work.Whitney.sumCore SF' Z' W')) := by
  -- the fibrewise block-diagonal maps of the sum and of its inverse, as continuous linear maps
  let T : B → F →L[𝕜] F' := fun b =>
    (SF' : (F₁' × F₂') →L[𝕜] F').comp
      (((e.clmGen b).prodMap (e'.clmGen b)).comp (SF.symm : F →L[𝕜] (F₁ × F₂)))
  let S : B → F' →L[𝕜] F := fun b =>
    (SF : (F₁ × F₂) →L[𝕜] F).comp
      ((((Work.Thom.BundleIso.symm e).clmGen b).prodMap
        ((Work.Thom.BundleIso.symm e').clmGen b)).comp (SF'.symm : F' →L[𝕜] (F₁' × F₂')))
  -- the clm's of an isomorphism and of its inverse are mutually inverse
  have hleft : ∀ b (x : F), (S b) ((T b) x) = x := by
    intro b x
    have hZc : ⇑((Work.Thom.BundleIso.symm e).clmGen b) ∘ ⇑(e.clmGen b) = id := by
      funext z
      change (Work.Thom.BundleIso.symm e).clmGen b (e.clmGen b z) = z
      rw [Work.Thom.BundleIso.clmGen_apply, Work.Thom.BundleIso.clmGen_apply]
      exact e.left_inv b z
    have hWc : ⇑((Work.Thom.BundleIso.symm e').clmGen b) ∘ ⇑(e'.clmGen b) = id := by
      funext z
      change (Work.Thom.BundleIso.symm e').clmGen b (e'.clmGen b z) = z
      rw [Work.Thom.BundleIso.clmGen_apply, Work.Thom.BundleIso.clmGen_apply]
      exact e'.left_inv b z
    simp only [S, T, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap',
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply, Prod.map_map]
    rw [hZc, hWc]
    simp [ContinuousLinearEquiv.apply_symm_apply]
  have hright : ∀ b (y : F'), (T b) ((S b) y) = y := by
    intro b y
    have hZc : ⇑(e.clmGen b) ∘ ⇑((Work.Thom.BundleIso.symm e).clmGen b) = id := by
      funext z
      change e.clmGen b ((Work.Thom.BundleIso.symm e).clmGen b z) = z
      rw [Work.Thom.BundleIso.clmGen_apply, Work.Thom.BundleIso.clmGen_apply]
      exact e.right_inv b z
    have hWc : ⇑(e'.clmGen b) ∘ ⇑((Work.Thom.BundleIso.symm e').clmGen b) = id := by
      funext z
      change e'.clmGen b ((Work.Thom.BundleIso.symm e').clmGen b z) = z
      rw [Work.Thom.BundleIso.clmGen_apply, Work.Thom.BundleIso.clmGen_apply]
      exact e'.right_inv b z
    simp only [T, S, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap',
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply, Prod.map_map]
    rw [hZc, hWc]
    simp [ContinuousLinearEquiv.apply_symm_apply]
  -- continuity of the total-space map of the sum, chart by chart
  have hT : ∀ (i₁ : ι₁ × ι₂) (i₂ : ι₁' × ι₂'), ContinuousOn (fun b : B =>
      ((Work.Whitney.sumCore SF' Z' W').coordChange
        ((Work.Whitney.sumCore SF' Z' W').indexAt b) i₂ b).comp
        ((T b).comp
          ((Work.Whitney.sumCore SF Z W).coordChange
            i₁ ((Work.Whitney.sumCore SF Z W).indexAt b) b)))
      ((Work.Whitney.sumCore SF Z W).baseSet i₁ ∩
        (Work.Whitney.sumCore SF' Z' W').baseSet i₂) := by
    intro i₁ i₂
    obtain ⟨i₁a, i₁b⟩ := i₁
    obtain ⟨i₂a, i₂b⟩ := i₂
    simp only [Work.Whitney.sumCore_baseSet, Work.Whitney.sumCore_indexAt]
    have hZ' : ContinuousOn (fun b : B =>
        (Z'.coordChange (Z'.indexAt b) i₂a b).comp
          ((e.clmGen b).comp (Z.coordChange i₁a (Z.indexAt b) b)))
        ((Z.baseSet i₁a ∩ W.baseSet i₁b) ∩ (Z'.baseSet i₂a ∩ W'.baseSet i₂b)) :=
      (Work.Thom.continuousOn_chartExpressionCLM_gen Z Z' e i₁a i₂a).mono
        (fun b hb => ⟨hb.1.1, hb.2.1⟩)
    have hW' : ContinuousOn (fun b : B =>
        (W'.coordChange (W'.indexAt b) i₂b b).comp
          ((e'.clmGen b).comp (W.coordChange i₁b (W.indexAt b) b)))
        ((Z.baseSet i₁a ∩ W.baseSet i₁b) ∩ (Z'.baseSet i₂a ∩ W'.baseSet i₂b)) :=
      (Work.Thom.continuousOn_chartExpressionCLM_gen W W' e' i₁b i₂b).mono
        (fun b hb => ⟨hb.1.2, hb.2.2⟩)
    have hprod := hZ'.prod_mapL 𝕜 hW'
    refine ContinuousOn.congr (f := fun b : B =>
      (SF' : (F₁' × F₂') →L[𝕜] F').comp
        ((((Z'.coordChange (Z'.indexAt b) i₂a b).comp
            ((e.clmGen b).comp (Z.coordChange i₁a (Z.indexAt b) b))).prodMap
          ((W'.coordChange (W'.indexAt b) i₂b b).comp
            ((e'.clmGen b).comp (W.coordChange i₁b (W.indexAt b) b)))).comp
          (SF.symm : F →L[𝕜] (F₁ × F₂)))) ?_ ?_
    · exact ContinuousOn.clm_comp continuousOn_const
        (ContinuousOn.clm_comp hprod continuousOn_const)
    · intro b hb
      simpa only [Work.Whitney.sumCore_coordChange, Work.Whitney.sumCore_indexAt, T] using
        sumCore_conj_identity SF SF'
          (Z'.coordChange (Z'.indexAt b) i₂a b) (W'.coordChange (W'.indexAt b) i₂b b)
          (e.clmGen b) (e'.clmGen b)
          (Z.coordChange i₁a (Z.indexAt b) b) (W.coordChange i₁b (W.indexAt b) b)
  have hS : ∀ (i₂ : ι₁' × ι₂') (i₁ : ι₁ × ι₂), ContinuousOn (fun b : B =>
      ((Work.Whitney.sumCore SF Z W).coordChange
        ((Work.Whitney.sumCore SF Z W).indexAt b) i₁ b).comp
        ((S b).comp
          ((Work.Whitney.sumCore SF' Z' W').coordChange
            i₂ ((Work.Whitney.sumCore SF' Z' W').indexAt b) b)))
      ((Work.Whitney.sumCore SF' Z' W').baseSet i₂ ∩
        (Work.Whitney.sumCore SF Z W).baseSet i₁) := by
    intro i₂ i₁
    obtain ⟨i₂a, i₂b⟩ := i₂
    obtain ⟨i₁a, i₁b⟩ := i₁
    simp only [Work.Whitney.sumCore_baseSet, Work.Whitney.sumCore_indexAt]
    have hZ' : ContinuousOn (fun b : B =>
        (Z.coordChange (Z.indexAt b) i₁a b).comp
          (((Work.Thom.BundleIso.symm e).clmGen b).comp
            (Z'.coordChange i₂a (Z'.indexAt b) b)))
        ((Z'.baseSet i₂a ∩ W'.baseSet i₂b) ∩ (Z.baseSet i₁a ∩ W.baseSet i₁b)) :=
      (Work.Thom.continuousOn_chartExpressionCLM_gen Z' Z (Work.Thom.BundleIso.symm e)
        i₂a i₁a).mono (fun b hb => ⟨hb.1.1, hb.2.1⟩)
    have hW' : ContinuousOn (fun b : B =>
        (W.coordChange (W.indexAt b) i₁b b).comp
          (((Work.Thom.BundleIso.symm e').clmGen b).comp
            (W'.coordChange i₂b (W'.indexAt b) b)))
        ((Z'.baseSet i₂a ∩ W'.baseSet i₂b) ∩ (Z.baseSet i₁a ∩ W.baseSet i₁b)) :=
      (Work.Thom.continuousOn_chartExpressionCLM_gen W' W (Work.Thom.BundleIso.symm e')
        i₂b i₁b).mono (fun b hb => ⟨hb.1.2, hb.2.2⟩)
    have hprod := hZ'.prod_mapL 𝕜 hW'
    refine ContinuousOn.congr (f := fun b : B =>
      (SF : (F₁ × F₂) →L[𝕜] F).comp
        ((((Z.coordChange (Z.indexAt b) i₁a b).comp
            (((Work.Thom.BundleIso.symm e).clmGen b).comp
              (Z'.coordChange i₂a (Z'.indexAt b) b))).prodMap
          ((W.coordChange (W.indexAt b) i₁b b).comp
            (((Work.Thom.BundleIso.symm e').clmGen b).comp
              (W'.coordChange i₂b (W'.indexAt b) b)))).comp
          (SF'.symm : F' →L[𝕜] (F₁' × F₂')))) ?_ ?_
    · exact ContinuousOn.clm_comp continuousOn_const
        (ContinuousOn.clm_comp hprod continuousOn_const)
    · intro b hb
      simpa only [Work.Whitney.sumCore_coordChange, Work.Whitney.sumCore_indexAt, S] using
        sumCore_conj_identity SF' SF
          (Z.coordChange (Z.indexAt b) i₁a b) (W.coordChange (W.indexAt b) i₁b b)
          ((Work.Thom.BundleIso.symm e).clmGen b) ((Work.Thom.BundleIso.symm e').clmGen b)
          (Z'.coordChange i₂a (Z'.indexAt b) b) (W'.coordChange i₂b (W'.indexAt b) b)
  have hts : Continuous (fun p : (Work.Whitney.sumCore SF Z W).TotalSpace =>
      (⟨p.1, T p.1 p.2⟩ : (Work.Whitney.sumCore SF' Z' W').TotalSpace)) :=
    Work.Thom.continuous_totalSpaceMap_clm_gen (Work.Whitney.sumCore SF Z W)
      (Work.Whitney.sumCore SF' Z' W') (ContinuousMap.id B) T
      (by
        intro i₁ i₂
        simpa only [ContinuousMap.coe_id, ContinuousMap.id_apply, Set.preimage_id] using hT i₁ i₂)
  have hsi : Continuous (fun p : (Work.Whitney.sumCore SF' Z' W').TotalSpace =>
      (⟨p.1, S p.1 p.2⟩ : (Work.Whitney.sumCore SF Z W).TotalSpace)) :=
    Work.Thom.continuous_totalSpaceMap_clm_gen (Work.Whitney.sumCore SF' Z' W')
      (Work.Whitney.sumCore SF Z W) (ContinuousMap.id B) S
      (by
        intro i₂ i₁
        simpa only [ContinuousMap.coe_id, ContinuousMap.id_apply, Set.preimage_id] using hS i₂ i₁)
  exact ⟨{ hom := fun b => (T b).toLinearMap
           inv := fun b => (S b).toLinearMap
           left_inv := fun b x => hleft b x
           right_inv := fun b y => hright b y
           continuous_hom := hts.congr (fun p => by
             apply Bundle.TotalSpace.ext
             · rfl
             · exact heq_of_eq rfl)
           continuous_inv := hsi.congr (fun p => by
             apply Bundle.TotalSpace.ext
             · rfl
             · exact heq_of_eq rfl) }⟩

/-! ## The requested lemma -/

/-- **The real Whitney sum of congruent bundles is congruent.**  Isomorphic summands have
isomorphic Whitney sums: this is the `E ⊕ F = E' ⊕ F'` step of the splitting arguments. -/
theorem whitneySumRCongr {B : Type} [TopologicalSpace B] {k₁ k₂ l₁ l₂ : ℕ}
    {ι₁ ι₁' ι₂ ι₂' : Type}
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k₁)) ι₁)
    (Z' : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k₂)) ι₁')
    (W : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin l₁)) ι₂)
    (W' : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin l₂)) ι₂')
    (hZ : Nonempty (Work.Thom.BundleIso Z Z')) (hW : Nonempty (Work.Thom.BundleIso W W')) :
    Nonempty (Work.Thom.BundleIso (Work.Whitney.whitneySumR Z W)
      (Work.Whitney.whitneySumR Z' W')) := by
  obtain ⟨e⟩ := hZ
  obtain ⟨e'⟩ := hW
  exact nonempty_bundleIso_sumCore_congr (Work.Whitney.sumFibreR k₁ l₁)
    (Work.Whitney.sumFibreR k₂ l₂) Z Z' W W' e e'

end

end Work.Agree
