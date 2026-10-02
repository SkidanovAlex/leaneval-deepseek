import Mathlib
import Submission.Work.Agree.crux
import Submission.Work.Thom.BundleIso_comap_exists

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `mapFibre` is a functor on bundles; isomorphism of fibres is natural

`Work.Agree.mapFibre_mapFibre`: `mapFibre` is functorial in the change of fibre, and
`Work.Agree.nonempty_bundleIso_mapFibre_of_iso`: a bundle isomorphism is preserved by changing the
fibre on both sides along a common fibre.

These two tools live here (rather than in `Submission/Work/Agree/geomSplitting.lean`) so that
modules *below* `geomSplitting` — such as `Submission/Work/Agree/plumbChain.lean` — may use them.
-/

open scoped Manifold ContDiff Topology

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## Auxiliary: `mapFibre` is a functor on bundles -/

/-- `mapFibre` is functorial in the fibre. -/
theorem mapFibre_mapFibre {B : Type} [TopologicalSpace B] {F F' F'' : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [NormedAddCommGroup F''] [NormedSpace ℝ F''] {ι : Type}
    (Z : RealBundle B F ι) (e : F ≃L[ℝ] F') (e' : F' ≃L[ℝ] F'') :
    RealBundle.mapFibre e' (RealBundle.mapFibre e Z) = RealBundle.mapFibre (e.trans e') Z := by
  refine RealBundle.ext ?_ ?_ ?_
  · funext i; rfl
  · funext x; rfl
  · intro i j x
    rw [RealBundle.mapFibre_coordChange, RealBundle.mapFibre_coordChange,
      RealBundle.mapFibre_coordChange]
    ext v
    rfl

/-- A bundle isomorphism is preserved by a change of fibre on both sides. -/
theorem nonempty_bundleIso_mapFibre_of_iso {B : Type} [TopologicalSpace B] {F F' W : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {ι ι' : Type}
    (Z : RealBundle B F ι) (Z' : RealBundle B F' ι')
    (e : F ≃L[ℝ] W) (e' : F' ≃L[ℝ] W)
    (h : Nonempty (Work.Thom.BundleIso Z Z')) :
    Nonempty (Work.Thom.BundleIso (Z.mapFibre e) (Z'.mapFibre e')) := by
  obtain ⟨φ⟩ := h
  set T : B → (W →L[ℝ] W) := fun b =>
    (e' : F' →L[ℝ] W).comp ((φ.clmGen b).comp ((e.symm : W →L[ℝ] F))) with hTdef
  set T' : B → (W →L[ℝ] W) := fun b =>
    (e : F →L[ℝ] W).comp
      (((Work.Thom.BundleIso.symm φ).clmGen b).comp ((e'.symm : W →L[ℝ] F'))) with hT'def
  have hcont : ∀ (i₁ : ι) (i₂ : ι'), ContinuousOn (fun b : B =>
      ((Z'.mapFibre e').coordChange ((Z'.mapFibre e').indexAt b) i₂ b).comp
        ((T b).comp ((Z.mapFibre e).coordChange i₁ ((Z.mapFibre e).indexAt b) b)))
      ((Z.mapFibre e).baseSet i₁ ∩ (Z'.mapFibre e').baseSet i₂) := by
    intro i₁ i₂
    refine ContinuousOn.congr (f := fun b : B =>
      (e' : F' →L[ℝ] W).comp
        (((Z'.coordChange (Z'.indexAt b) i₂ b).comp
          ((φ.clmGen b).comp (Z.coordChange i₁ (Z.indexAt b) b))).comp
            ((e.symm : W →L[ℝ] F)))) ?_ ?_
    · exact continuousOn_const.clm_comp
        ((Work.Thom.continuousOn_chartExpressionCLM_gen Z Z' φ i₁ i₂).clm_comp
          continuousOn_const)
    · intro b hb
      refine ContinuousLinearMap.ext (fun v => ?_)
      simp only [hTdef, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        RealBundle.mapFibre_coordChange, RealBundle.mapFibre_indexAt,
        ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hcont' : ∀ (i₁ : ι') (i₂ : ι), ContinuousOn (fun b : B =>
      ((Z.mapFibre e).coordChange ((Z.mapFibre e).indexAt b) i₂ b).comp
        ((T' b).comp ((Z'.mapFibre e').coordChange i₁ ((Z'.mapFibre e').indexAt b) b)))
      ((Z'.mapFibre e').baseSet i₁ ∩ (Z.mapFibre e).baseSet i₂) := by
    intro i₁ i₂
    refine ContinuousOn.congr (f := fun b : B =>
      (e : F →L[ℝ] W).comp
        (((Z.coordChange (Z.indexAt b) i₂ b).comp
          (((Work.Thom.BundleIso.symm φ).clmGen b).comp
            (Z'.coordChange i₁ (Z'.indexAt b) b))).comp
              ((e'.symm : W →L[ℝ] F')))) ?_ ?_
    · exact continuousOn_const.clm_comp
        ((Work.Thom.continuousOn_chartExpressionCLM_gen Z' Z (Work.Thom.BundleIso.symm φ)
          i₁ i₂).clm_comp continuousOn_const)
    · intro b hb
      refine ContinuousLinearMap.ext (fun v => ?_)
      simp only [hT'def, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        RealBundle.mapFibre_coordChange, RealBundle.mapFibre_indexAt,
        ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨{ hom := fun b => (T b).toLinearMap
            inv := fun b => (T' b).toLinearMap
            left_inv := ?_
            right_inv := ?_
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · intro b x
    show (e : F →L[ℝ] W) ((φ.inv b) ((e'.symm : W →L[ℝ] F') ((e' : F' →L[ℝ] W)
      ((φ.hom b) ((e.symm : W →L[ℝ] F) x))))) = x
    have h1 : (e'.symm : W →L[ℝ] F') ((e' : F' →L[ℝ] W) ((φ.hom b) ((e.symm : W →L[ℝ] F) x)))
        = (φ.hom b) ((e.symm : W →L[ℝ] F) x) :=
      ContinuousLinearEquiv.symm_apply_apply e' _
    rw [h1]
    have h2 : (φ.inv b) ((φ.hom b) ((e.symm : W →L[ℝ] F) x)) = (e.symm : W →L[ℝ] F) x :=
      φ.left_inv b _
    rw [h2]
    exact ContinuousLinearEquiv.apply_symm_apply e x
  · intro b x
    show (e' : F' →L[ℝ] W) ((φ.hom b) ((e.symm : W →L[ℝ] F) ((e : F →L[ℝ] W)
      ((φ.inv b) ((e'.symm : W →L[ℝ] F') x))))) = x
    have h1 : (e.symm : W →L[ℝ] F) ((e : F →L[ℝ] W) ((φ.inv b) ((e'.symm : W →L[ℝ] F') x)))
        = (φ.inv b) ((e'.symm : W →L[ℝ] F') x) :=
      ContinuousLinearEquiv.symm_apply_apply e _
    rw [h1]
    have h2 : (φ.hom b) ((φ.inv b) ((e'.symm : W →L[ℝ] F') x)) = (e'.symm : W →L[ℝ] F') x :=
      φ.right_inv b _
    rw [h2]
    exact ContinuousLinearEquiv.apply_symm_apply e' x
  · exact Work.Thom.continuous_totalSpaceMap_clm_gen (Z.mapFibre e) (Z'.mapFibre e')
      (ContinuousMap.id B) T (fun i₁ i₂ => by
        rw [show (ContinuousMap.id B) ⁻¹' (Z'.mapFibre e').baseSet i₂
          = (Z'.mapFibre e').baseSet i₂ from Set.preimage_id]
        exact hcont i₁ i₂)
  · exact Work.Thom.continuous_totalSpaceMap_clm_gen (Z'.mapFibre e') (Z.mapFibre e)
      (ContinuousMap.id B) T' (fun i₁ i₂ => by
        rw [show (ContinuousMap.id B) ⁻¹' (Z.mapFibre e).baseSet i₂
          = (Z.mapFibre e).baseSet i₂ from Set.preimage_id]
        exact hcont' i₁ i₂)


end

end Work.Agree
