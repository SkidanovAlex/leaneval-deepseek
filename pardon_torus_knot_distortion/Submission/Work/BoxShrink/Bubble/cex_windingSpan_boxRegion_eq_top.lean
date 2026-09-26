import Mathlib
import Submission.Work.BoxShrink.Bubble.standard_counterexample
import Submission.Work.BoxShrink.Bubble.cex_upperRegion_essential

namespace Work.BoxShrink.Bubble

noncomputable section

open LeanEval.KnotTheory.PardonDistortion

/-- The box of the counterexample is `B = boxRegion standard (5/2) 0 (swap 1 2)`. -/
abbrev cexBox : Set R3 :=
  Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2)

/-- The meridian circle `{θ = π/2}`, of winding vector `(0, 1)`, lies in the counterexample
box: its `x`-coordinate is `0`, its `z`-coordinate is `sin t` (bounded by `1`) and its
`y`-coordinate is `2 + cos t` (bounded by `3`), all well inside the box of size `5/2`. -/
lemma cex_meridianCurve_mem :
    ∀ t : ℝ,
      (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)) t ∈ cexBox := by
  intro t
  refine ⟨(Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)).mem t, ?_⟩
  rw [cex_mem_PBox]
  have hx : (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)) t 0
      = 0 := by
    rw [Work.CoreTopology.meridianCurve_apply, Work.CoreTopology.standard_psi,
      Work.Core.torusMap_apply_zero, Real.cos_pi_div_two, mul_zero]
  have hy : (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)) t 1
      = 2 + Real.cos t := by
    rw [Work.CoreTopology.meridianCurve_apply, Work.CoreTopology.standard_psi,
      Work.Core.torusMap_apply_one, Real.sin_pi_div_two, mul_one]
  have hz : (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)) t 2
      = Real.sin t := by
    rw [Work.CoreTopology.meridianCurve_apply, Work.CoreTopology.standard_psi,
      Work.Core.torusMap_apply_two]
  rw [hx, hy, hz]
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [abs_lt]
    constructor
    · nlinarith [Real.neg_one_le_sin t, Submission.one_le_rpow_third]
    · nlinarith [Real.sin_le_one t, Submission.one_le_rpow_third]
  · rw [abs_lt]
    constructor
    · nlinarith [Real.neg_one_le_cos t, cex_rpow_two_thirds_gt]
    · nlinarith [Real.cos_le_one t, cex_rpow_two_thirds_gt]

/-- The meridian circle `{θ = π/2}` has winding vector `(0, 1)`. -/
lemma cex_windingOf_meridianCurve :
    Work.SurgeryInvariance.windingOf Work.CoreTopology.standard
      (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)) = (0, 1) := by
  rw [Work.SurgeryInvariance.windingOf_eq _ _ (Work.CoreTopology.meridianLift _ _),
    Work.CoreTopology.meridianLift_winding]

/-- The `x`-coordinate of a point of the standard torus is `(2 + cos φ) cos θ`. -/
lemma cex_torusMap_zero (θ φ : ℝ) :
    (Work.Core.torusMap θ φ) 0 = (2 + Real.cos φ) * Real.cos θ :=
  Work.CoreTopology.torusMap_apply_zero θ φ

/-- The `y`-coordinate of a point of the standard torus is `(2 + cos φ) sin θ`. -/
lemma cex_torusMap_one (θ φ : ℝ) :
    (Work.Core.torusMap θ φ) 1 = (2 + Real.cos φ) * Real.sin θ :=
  Work.CoreTopology.torusMap_apply_one θ φ

/-- The `z`-coordinate of a point of the standard torus is `sin φ`. -/
lemma cex_torusMap_two (θ φ : ℝ) :
    (Work.Core.torusMap θ φ) 2 = Real.sin φ :=
  Work.CoreTopology.torusMap_apply_two θ φ

/-- **The winding span of the counterexample box is everything.**  The box contains

* the longitude circle `{z = -1}`, whose winding vector is `(1, 0)`
  (`cex_longitudeCurve_mem`, `cex_windingOf_longitudeCurve`), and
* the meridian circle `{θ = π/2}`, whose winding vector is `(0, 1)`
  (`cex_meridianCurve_mem`, `cex_windingOf_meridianCurve`).

Those two vectors generate `ℚ² = H₁(T²; ℚ)`, so the span is the whole of `ℚ²`. -/
theorem cex_windingSpan_boxRegion_eq_top :
    Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard (5 / 2) 0
        (Equiv.swap (1 : Fin 3) 2)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  -- the longitude circle realises `(1, 0)`
  have hL : ((((1 : ℤ) : ℚ), ((0 : ℤ) : ℚ)) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard cexBox := by
    apply Submodule.subset_span
    refine ⟨Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (3 * Real.pi / 2),
      fun t => cex_longitudeCurve_mem t, ?_⟩
    rw [cex_windingOf_longitudeCurve]
  -- the meridian circle realises `(0, 1)`
  have hM : ((((0 : ℤ) : ℚ), ((1 : ℤ) : ℚ)) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard cexBox := by
    apply Submodule.subset_span
    refine ⟨Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2),
      fun t => cex_meridianCurve_mem t, ?_⟩
    rw [cex_windingOf_meridianCurve]
  -- every vector of `ℚ²` is a combination of the two
  have hv : v = v.1 • ((((1 : ℤ) : ℚ), ((0 : ℤ) : ℚ)) : ℚ × ℚ) +
      v.2 • ((((0 : ℤ) : ℚ), ((1 : ℤ) : ℚ)) : ℚ × ℚ) := by
    ext <;> simp
  rw [hv]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hL) (Submodule.smul_mem _ _ hM)

end

end Work.BoxShrink.Bubble
