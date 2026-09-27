import Mathlib
import Submission.Work.Drive.Morse

/-!
# The manifold derivative of a function restricted to an open subset

For an open subset `U` of a manifold `M`, the tangent space to `U` at a point `x : U` is
canonically identified with the tangent space to `M` at `x`, and the derivative of the
restriction `f|_U` is the derivative of `f`. This file records this fact, in the form needed for
the `n = 2` (Morse theoretic) branch of the Whitney embedding theorem.

The mathematical content is that the preferred chart of the open submanifold `U` at `x` is the
restriction of the preferred chart of `M` at `x`, so the function `f|_U` written in the charts
coincides, near the chart point, with the function `f` written in the charts of `M`.

## Main results

* `Work.Drive.N2.subtype_val_extChartAt_symm_eventuallyEq`: inverse charts of `U` and of `M`
  agree near the base point.
* `Work.Drive.N2.writtenInExtChartAt_comp_subtype_val`: the chart representations of `f|_U` and
  of `f` agree near the chart point.
* `Work.Drive.N2.mfderiv_subtype_val`: the derivative of the inclusion of an open subset is the
  identity in the canonical identification of tangent spaces.
* `Work.Drive.N2.mfderiv_restrict_opens_general`: `mfderiv I I' (f ∘ Subtype.val) x = mfderiv I I' f x`.
* `Work.Drive.N2.mfderiv_restrict_opens`: the `n = 2` Euclidean instance of the above.
-/

namespace Work.Drive.N2

open scoped Manifold Topology
open TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]

/-- The preferred chart of an open subset `U ⊆ M` at a point `x : U` has, near the base point,
the same inverse as the preferred chart of `M` at `x`: both are the inverse of the chart of `M`
at `x`, restricted.  This is the chart-level identity behind the fact that the inclusion
`U → M` is a local diffeomorphism which is the identity in charts. -/
theorem subtype_val_extChartAt_symm_eventuallyEq (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (U : TopologicalSpace.Opens M) (x : U) :
    (fun y : E => Subtype.val ((extChartAt I x).symm y))
      =ᶠ[𝓝[Set.range I] (extChartAt I x x)] (extChartAt I (x : M)).symm := by
  have hzT : chartAt H (x : M) (x : M) ∈ ((chartAt H (x : M)).subtypeRestr ⟨x⟩).target :=
    OpenPartialHomeomorph.map_subtype_source _ ⟨x⟩ (mem_chart_source H (x : M))
  have hTn : ((chartAt H (x : M)).subtypeRestr ⟨x⟩).target ∈ 𝓝 (chartAt H (x : M) (x : M)) :=
    ((chartAt H (x : M)).subtypeRestr ⟨x⟩).open_target.mem_nhds hzT
  have hpre : I.symm ⁻¹' ((chartAt H (x : M)).subtypeRestr ⟨x⟩).target
      ∈ 𝓝 (extChartAt I x x) := by
    refine (I.continuous_symm.continuousAt).preimage_mem_nhds ?_
    rw [show I.symm (extChartAt I x x) = chartAt H (x : M) (x : M) from by
      simp only [extChartAt_coe, Function.comp_apply, TopologicalSpace.Opens.chartAt_eq,
        OpenPartialHomeomorph.subtypeRestr_coe, Set.domRestrict, ModelWithCorners.left_inv]]
    exact hTn
  refine Filter.eventuallyEq_of_mem (nhdsWithin_le_nhds hpre) ?_
  intro y hyT
  show Subtype.val ((extChartAt I x).symm y) = (extChartAt I (x : M)).symm y
  have hA : Subtype.val (((chartAt H (x : M)).subtypeRestr ⟨x⟩).symm (I.symm y))
      = (chartAt H (x : M)).symm (I.symm y) :=
    OpenPartialHomeomorph.subtypeRestr_symm_apply (chartAt H (x : M)) ⟨x⟩ hyT
  rw [extChartAt_coe_symm, Function.comp_apply, TopologicalSpace.Opens.chartAt_eq, hA]
  rfl

/-- The chart representation of the restriction `f|_U` of `f : M → M'` to an open subset `U`
agrees, near the base chart point, with the chart representation of `f`. -/
theorem writtenInExtChartAt_comp_subtype_val (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    (f : M → M') (U : TopologicalSpace.Opens M) (x : U) :
    writtenInExtChartAt I I' x (fun y : U => f y)
      =ᶠ[𝓝[Set.range I] (extChartAt I x x)] writtenInExtChartAt I I' (x : M) f := by
  obtain ⟨s, hs, hEq⟩ :=
    Filter.eventuallyEq_iff_exists_mem.mp (subtype_val_extChartAt_symm_eventuallyEq I U x)
  refine Filter.eventuallyEq_of_mem hs ?_
  intro y hy
  simp only [writtenInExtChartAt, Function.comp_apply]
  exact congrArg (fun z => extChartAt I' (f (x : M)) (f z)) (hEq hy)

/-- The chart representation of the inclusion of an open subset `U ⊆ M` is the identity near the
base chart point: for `y ∈ range I`, `y ∈ (chartAt H x).target` with `I.symm y` in the target of
the chart of `M` at `x`, one has `writtenInExtChartAt I I x Subtype.val y = y`. -/
theorem writtenInExtChartAt_subtype_val_apply (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (U : TopologicalSpace.Opens M) (x : U) (y : E)
    (hyT : I.symm y ∈ ((chartAt H (x : M)).subtypeRestr ⟨x⟩).target)
    (hyr : y ∈ Set.range I) :
    writtenInExtChartAt I I x (Subtype.val : U → M) y = y := by
  have hA : Subtype.val (((chartAt H (x : M)).subtypeRestr ⟨x⟩).symm (I.symm y))
      = (chartAt H (x : M)).symm (I.symm y) :=
    OpenPartialHomeomorph.subtypeRestr_symm_apply (chartAt H (x : M)) ⟨x⟩ hyT
  simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe, extChartAt_coe_symm,
    TopologicalSpace.Opens.chartAt_eq]
  rw [hA]
  rw [OpenPartialHomeomorph.right_inv _
    ((chartAt H (x : M)).subtypeRestr_target_subset ⟨x⟩ hyT)]
  exact I.right_inv hyr

/-- The manifold derivative of the inclusion of an open subset is the identity (in the canonical
identification of the tangent spaces). -/
theorem mfderiv_subtype_val (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (U : TopologicalSpace.Opens M) (x : U) :
    mfderiv I I (Subtype.val : U → M) x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  have hzT : chartAt H (x : M) (x : M) ∈ ((chartAt H (x : M)).subtypeRestr ⟨x⟩).target :=
    OpenPartialHomeomorph.map_subtype_source _ ⟨x⟩ (mem_chart_source H (x : M))
  have hTn : ((chartAt H (x : M)).subtypeRestr ⟨x⟩).target ∈ 𝓝 (chartAt H (x : M) (x : M)) :=
    ((chartAt H (x : M)).subtypeRestr ⟨x⟩).open_target.mem_nhds hzT
  have hsymmI : I.symm (extChartAt I x x) = chartAt H (x : M) (x : M) := by
    simp only [extChartAt_coe, Function.comp_apply, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_coe, Set.domRestrict, ModelWithCorners.left_inv]
  have hmem : extChartAt I x x ∈ Set.range I := by
    rw [show extChartAt I x x = I (chartAt H (x : M) (x : M)) from by
      simp only [extChartAt_coe, Function.comp_apply, TopologicalSpace.Opens.chartAt_eq,
        OpenPartialHomeomorph.subtypeRestr_coe, Set.domRestrict]]
    exact Set.mem_range_self _
  have hpre : I.symm ⁻¹' ((chartAt H (x : M)).subtypeRestr ⟨x⟩).target
      ∈ 𝓝 (extChartAt I x x) := by
    refine (I.continuous_symm.continuousAt).preimage_mem_nhds ?_
    rw [hsymmI]
    exact hTn
  have hww : writtenInExtChartAt I I x (Subtype.val : U → M)
      =ᶠ[𝓝[Set.range I] (extChartAt I x x)] (id : E → E) :=
    Filter.eventuallyEq_of_mem
      (Filter.inter_mem (nhdsWithin_le_nhds hpre) self_mem_nhdsWithin)
      (fun y hy => writtenInExtChartAt_subtype_val_apply I U x y hy.1 hy.2)
  have hpt : writtenInExtChartAt I I x (Subtype.val : U → M) (extChartAt I x x)
      = extChartAt I x x :=
    writtenInExtChartAt_subtype_val_apply I U x (extChartAt I x x) (by rw [hsymmI]; exact hzT) hmem
  have hderiv : HasFDerivWithinAt (writtenInExtChartAt I I x (Subtype.val : U → M))
      (ContinuousLinearMap.id 𝕜 E) (Set.range I) (extChartAt I x x) :=
    (hasFDerivWithinAt_id _ _).congr_of_eventuallyEq hww (by simpa using hpt)
  have hmf : HasMFDerivAt I I (Subtype.val : U → M) x (ContinuousLinearMap.id 𝕜 E) :=
    ⟨continuous_subtype_val.continuousAt, hderiv⟩
  exact hmf.mfderiv

/-- **The derivative of a restriction to an open subset.**  For a map `f : M → M'` between
manifolds and an open subset `U ⊆ M`, the derivative of `f|_U` at `x : U` is the derivative of
`f` at `x`, under the canonical identification of the tangent spaces. -/
theorem mfderiv_restrict_opens_general (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    (f : M → M') (U : TopologicalSpace.Opens M) (x : U) (v : TangentSpace I x) :
    mfderiv I I' (fun y : U => f y) x v = mfderiv I I' f (x : M) v := by
  have hiff := (differentiableWithinAt_localInvariantProp (I := I) (I' := I')).liftPropAt_iff_comp_subtype_val f x
  by_cases hf : MDifferentiableAt I I' f (x : M)
  · have hg : MDifferentiableAt I I' (fun y : U => f y) x := hiff.mp hf
    rw [hf.mfderiv, hg.mfderiv]
    have hpt : writtenInExtChartAt I I' x (fun y : U => f y) (extChartAt I x x)
        = writtenInExtChartAt I I' (x : M) f (extChartAt I x x) := by
      have h1 : (extChartAt I x).symm (extChartAt I x x) = x :=
        (extChartAt I x).left_inv (mem_extChartAt_source x)
      have h2 : (extChartAt I (x : M)).symm (extChartAt I x x) = (x : M) :=
        (extChartAt I (x : M)).left_inv (mem_extChartAt_source (x : M))
      simp only [writtenInExtChartAt, Function.comp_apply, h1, h2]
    rw [Filter.EventuallyEq.fderivWithin_eq (writtenInExtChartAt_comp_subtype_val I f U x) hpt]
    rfl
  · have hg : ¬ MDifferentiableAt I I' (fun y : U => f y) x := fun h => hf (hiff.mpr h)
    rw [mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt hg]
    rfl

/-- The manifold derivative of a function restricted to an open subset of a surface agrees with
the derivative of the function itself, under the canonical identification of the tangent spaces.
(This is the `n = 2` Euclidean instance of `mfderiv_restrict_opens_general`.) -/
theorem mfderiv_restrict_opens {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → ℝ) (U : TopologicalSpace.Opens M) (x : U)
    (v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) x) :
    mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ)
        (fun y : U => f y) x v
      = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ)
        f (x : M) v :=
  mfderiv_restrict_opens_general (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) f U x v

end Work.Drive.N2
