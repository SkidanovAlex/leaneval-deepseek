import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.BoxShrink.Core.Defs
import Submission.Work.CoreTopology.Basic
import Submission.Work.BoxShrink.PinchOff.TangentData.Basic
import Submission.Work.BoxShrink.PinchOff.tangent_sphereSet_not_containsEssentialLoop
import Submission.Work.BoxShrink.PinchOff.tangent_sliceRegion_span_eq_bot

namespace Work.BoxShrink.PinchOff

noncomputable section

open LeanEval.KnotTheory.PardonDistortion

/-! ## The three pieces of the box region

The region of the standard torus inside the box `PBox (13/10) (1,0,0) (0 1 2)` contains two
circles with independent winding vectors:

* the **meridian** `{u = 0}`, i.e. `φ ↦ ((2 + cos φ), 0, sin φ)`, of winding vector `(0,1)`, and
* the **innermost longitude** `{v = π}`, i.e. `u ↦ (cos u, sin u, 0)`, of winding vector `(1,0)`.

Both lie in the box because the `z`-coordinate is bounded by `1 < (13/10)·2^{1/3}` and the
`x`-coordinate is within `2 < (13/10)·2^{2/3}` of the centre. -/

/-- The meridian circle `{u = 0}` lies in the box region of the tangent configuration. -/
theorem tangent_meridian_mem_boxRegion :
    ∀ t : ℝ, (Work.CoreTopology.meridianCurve Work.CoreTopology.standard 0) t ∈
      Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard tangentRad tangentCtr
        tangentCyc3 := by
  intro t
  refine ⟨(Work.CoreTopology.meridianCurve Work.CoreTopology.standard 0).mem t, ?_⟩
  rw [mem_PBox_tangent]
  have h0 : (Work.CoreTopology.meridianCurve Work.CoreTopology.standard 0) t 0
      = 2 + Real.cos t := by
    rw [Work.CoreTopology.meridianCurve_apply, Work.CoreTopology.standard_psi,
      Work.CoreTopology.torusMap_apply_zero, Real.cos_zero, mul_one]
  have h1 : (Work.CoreTopology.meridianCurve Work.CoreTopology.standard 0) t 1 = 0 := by
    rw [Work.CoreTopology.meridianCurve_apply, Work.CoreTopology.standard_psi,
      Work.CoreTopology.torusMap_apply_one, Real.sin_zero, mul_zero]
  have h2 : (Work.CoreTopology.meridianCurve Work.CoreTopology.standard 0) t 2
      = Real.sin t := by
    rw [Work.CoreTopology.meridianCurve_apply, Work.CoreTopology.standard_psi,
      Work.CoreTopology.torusMap_apply_two]
  rw [h0, h1, h2]
  refine ⟨by norm_num [tangentRad], ?_, ?_⟩
  · rw [abs_lt]
    have h := one_lt_rpow_one_third_mul
    constructor <;> nlinarith [Real.neg_one_le_sin t, Real.sin_le_one t]
  · rw [abs_lt]
    have h := two_lt_rpow_two_thirds_mul
    constructor <;> nlinarith [Real.neg_one_le_cos t, Real.cos_le_one t]

/-- The innermost longitude circle `{v = π}` lies in the box region of the tangent
configuration. -/
theorem tangent_longitude_mem_boxRegion :
    ∀ t : ℝ, (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi) t ∈
      Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard tangentRad tangentCtr
        tangentCyc3 := by
  intro t
  refine ⟨(Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi).mem t, ?_⟩
  rw [mem_PBox_tangent]
  have h0 : (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi) t 0
      = Real.cos t := by
    rw [Work.CoreTopology.longitudeCurve_apply, Work.CoreTopology.standard_psi,
      Work.CoreTopology.torusMap_apply_zero, Real.cos_pi]
    ring
  have h1 : (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi) t 1
      = Real.sin t := by
    rw [Work.CoreTopology.longitudeCurve_apply, Work.CoreTopology.standard_psi,
      Work.CoreTopology.torusMap_apply_one, Real.cos_pi]
    ring
  have h2 : (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi) t 2 = 0 := by
    rw [Work.CoreTopology.longitudeCurve_apply, Work.CoreTopology.standard_psi,
      Work.CoreTopology.torusMap_apply_two, Real.sin_pi]
  rw [h0, h1, h2]
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_lt]
    have h : (1 : ℝ) < tangentRad := by norm_num [tangentRad]
    constructor <;> nlinarith [Real.neg_one_le_sin t, Real.sin_le_one t]
  · rw [abs_zero]
    have h1 : (0 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) := by positivity
    have h2 := tangent_rad_pos
    nlinarith
  · rw [abs_lt]
    have h := two_lt_rpow_two_thirds_mul
    constructor <;> nlinarith [Real.neg_one_le_cos t, Real.cos_le_one t]

/-- **The winding span of the box region of the tangent configuration is everything**: the
meridian `(0,1)` and the innermost longitude `(1,0)` are both realised inside the box and are
independent. -/
theorem tangent_boxRegion_span_eq_top_aux :
    Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard tangentRad tangentCtr
        tangentCyc3) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  have hM : ((((0 : ℤ) : ℚ), ((1 : ℤ) : ℚ)) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
        (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard tangentRad tangentCtr
          tangentCyc3) := by
    apply Submodule.subset_span
    refine ⟨Work.CoreTopology.meridianCurve Work.CoreTopology.standard 0,
      tangent_meridian_mem_boxRegion, ?_⟩
    rw [Work.SurgeryInvariance.windingOf_eq _ _ (Work.CoreTopology.meridianLift _ _),
      Work.CoreTopology.meridianLift_winding]
  have hL : ((((1 : ℤ) : ℚ), ((0 : ℤ) : ℚ)) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
        (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard tangentRad tangentCtr
          tangentCyc3) := by
    apply Submodule.subset_span
    refine ⟨Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi,
      tangent_longitude_mem_boxRegion, ?_⟩
    rw [Work.SurgeryInvariance.windingOf_eq _ _ (Work.CoreTopology.longitudeLift _ _),
      Work.CoreTopology.longitudeLift_winding]
  have hv : v = v.1 • ((((1 : ℤ) : ℚ), ((0 : ℤ) : ℚ)) : ℚ × ℚ) +
      v.2 • ((((0 : ℤ) : ℚ), ((1 : ℤ) : ℚ)) : ℚ × ℚ) := by
    ext <;> simp
  rw [hv]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hL) (Submodule.smul_mem _ _ hM)

/-! ## The two half-regions carry no essential loop -/

/-- The upper half-region of the tangent configuration spans nothing. -/
theorem tangent_upperRegion_span_eq_bot_aux :
    Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard tangentRad tangentCtr
        tangentCyc3 0) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, ⟨L, hL⟩, hγ⟩
  have hshape : ∀ t : ℝ, 0 < Real.cos (L.Θ t) ∧
      ∀ k : ℤ, L.Φ t ≠ Real.pi + (k : ℝ) * (2 * Real.pi) := fun t => by
    have hmem : Work.Core.torusMap (L.Θ t) (L.Φ t) ∈
        Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard tangentRad tangentCtr
          tangentCyc3 0 := by
      have h := hγ t
      rwa [← L.lifts t] at h
    exact upperRegion_shape hmem
  have h1 : (L.winding).1 = 0 := by
    apply int_eq_zero_of_cos_gt (f := L.Θ) (c := 0) (m := (L.winding).1) L.contΘ
      (by norm_num) (by norm_num) (fun t => (hshape t).1)
    linarith [L.winding_spec.1]
  have h2 : (L.winding).2 = 0 := by
    apply int_eq_zero_of_notMem_lattice (f := L.Φ) (a := Real.pi) (m := (L.winding).2)
      L.contΦ (fun t k => (hshape t).2 k)
    linarith [L.winding_spec.2]
  exact hL (Prod.ext h1 h2)

/-- The lower half-region of the tangent configuration spans nothing. -/
theorem tangent_lowerRegion_span_eq_bot_aux :
    Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard tangentRad tangentCtr
        tangentCyc3 0) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, ⟨L, hL⟩, hγ⟩
  have hshape : ∀ t : ℝ, 0 < Real.cos (L.Φ t - Real.pi) ∧
      ∀ k : ℤ, L.Θ t ≠ (k : ℝ) * (2 * Real.pi) := fun t => by
    have hmem : Work.Core.torusMap (L.Θ t) (L.Φ t) ∈
        Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard tangentRad tangentCtr
          tangentCyc3 0 := by
      have h := hγ t
      rwa [← L.lifts t] at h
    exact lowerRegion_shape hmem
  have h1 : (L.winding).2 = 0 := by
    apply int_eq_zero_of_cos_gt (f := fun t => L.Φ t - Real.pi) (c := 0) (m := (L.winding).2)
      (L.contΦ.sub continuous_const) (by norm_num) (by norm_num) (fun t => (hshape t).1)
    show L.Φ (2 * Real.pi) - Real.pi - (L.Φ 0 - Real.pi) = (L.winding.2 : ℝ) * (2 * Real.pi)
    linarith [L.winding_spec.2]
  have h2 : (L.winding).1 = 0 := by
    apply int_eq_zero_of_notMem_lattice (f := L.Θ) (a := 0) (m := (L.winding).1) L.contΘ
      (fun t k => by simpa using (hshape t).2 k)
    linarith [L.winding_spec.1]
  exact hL (Prod.ext h2 h1)

/-- **The two half-regions of the tangent configuration span nothing.** -/
theorem tangent_halfRegions_span_eq_bot_aux :
    Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (((Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard tangentRad tangentCtr tangentCyc3 0 ∪ Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard tangentRad tangentCtr tangentCyc3 0))) = ⊥ := by
  have hunion : Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard tangentRad tangentCtr
          tangentCyc3 0 ∪
        Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard tangentRad tangentCtr
          tangentCyc3 0) = ⊥ := by
    rw [Work.SurgeryInvariance.Span.union_eq_sup
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion _ _ _ _ _)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion _ _ _ _ _)
      (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion _ _ _ _ _)]
    rw [tangent_upperRegion_span_eq_bot_aux, tangent_lowerRegion_span_eq_bot_aux, sup_bot_eq]
  exact hunion

theorem tangent_trace_counterexample_data :
    ¬ (Work.CoreTopology.standard).ContainsEssentialLoop
        (Work.BoxShrink.Core.sphereSet (WithLp.toLp 2 (![1, 0, 0] : Fin 3 → ℝ))
          (Equiv.swap 0 1 * Equiv.swap 1 2) (13 / 10 : ℝ)) ∧
      Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
        (Work.BoxShrink.Core.sliceRegion Work.CoreTopology.standard (13 / 10 : ℝ)
          (WithLp.toLp 2 (![1, 0, 0] : Fin 3 → ℝ))
          (Equiv.swap 0 1 * Equiv.swap 1 2) 0) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
        (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard (13 / 10 : ℝ)
          (WithLp.toLp 2 (![1, 0, 0] : Fin 3 → ℝ))
          (Equiv.swap 0 1 * Equiv.swap 1 2)) = ⊤ ∧
      Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
        (((Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (13 / 10 : ℝ) (WithLp.toLp 2 (![1, 0, 0] : Fin 3 → ℝ)) (Equiv.swap 0 1 * Equiv.swap 1 2) 0 ∪ Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (13 / 10 : ℝ) (WithLp.toLp 2 (![1, 0, 0] : Fin 3 → ℝ)) (Equiv.swap 0 1 * Equiv.swap 1 2) 0))) = ⊥ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact tangent_sphereSet_not_containsEssentialLoop
  · exact tangent_sliceRegion_span_eq_bot
  · exact tangent_boxRegion_span_eq_top_aux
  · exact tangent_halfRegions_span_eq_bot_aux

end

end Work.BoxShrink.PinchOff
