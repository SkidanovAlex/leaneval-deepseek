import Mathlib
import Submission.Work.WilE7.fibreAnalyticChartDefs

set_option linter.unusedVariables false

namespace Work.WilE7

open scoped Topology

/-- The scalar profile `y ↦ c * y / (1 + y^2)` is real analytic everywhere. -/
lemma analyticAt_coordProfile (c : ℝ) (y : ℝ) :
    AnalyticAt ℝ (fun t : ℝ => c * t / (1 + t ^ 2)) y := by
  have hnum : AnalyticAt ℝ (fun t : ℝ => c * t) y :=
    (analyticAt_id (z := y)).const_smul (c := c)
  have hden : AnalyticAt ℝ (fun t : ℝ => 1 + t ^ 2) y :=
    (analyticAt_const (v := (1 : ℝ))).add ((analyticAt_id (z := y)).pow 2)
  exact hnum.div hden (by positivity)

/-- The scalar profile has derivative `c` at `0`. -/
lemma hasDerivAt_coordProfile (c : ℝ) :
    HasDerivAt (fun t : ℝ => c * t / (1 + t ^ 2)) c 0 := by
  have hN : HasDerivAt (fun t : ℝ => c * t) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ))
  have hD : HasDerivAt (fun t : ℝ => 1 + t ^ 2) 0 0 := hsq.const_add 1
  have hND := hN.div hD (by norm_num)
  rw [show (c * (1 + (0 : ℝ) ^ 2) - c * 0 * 0) / (1 + (0 : ℝ) ^ 2) ^ 2 = c by ring]
    at hND
  exact hND

/-- The scalar profile, viewed as a continuous linear map derivative at `0`, is `c` times the
identity of `ℝ`. -/
lemma hasFDerivAt_coordProfile (c : ℝ) :
    HasFDerivAt (fun t : ℝ => c * t / (1 + t ^ 2)) (ContinuousLinearMap.toSpanSingleton ℝ c) 0 :=
  (hasDerivAt_coordProfile c).hasFDerivAt

/-- A single coordinate of `coordShrink m c` has derivative `c • proj l` at `0`. -/
lemma hasFDerivAt_coordShrink_apply (m : ℕ) (c : ℝ) (l : Fin m) :
    HasFDerivAt (fun v : Fin m → ℝ => c * v l / (1 + (v l) ^ 2))
      (c • (ContinuousLinearMap.proj l : (Fin m → ℝ) →L[ℝ] ℝ)) 0 := by
  have h1 : HasFDerivAt (fun v : Fin m → ℝ => v l)
      (ContinuousLinearMap.proj l : (Fin m → ℝ) →L[ℝ] ℝ) 0 := hasFDerivAt_apply l 0
  have h3 := (hasFDerivAt_coordProfile c).comp (0 : Fin m → ℝ) h1
  convert h3 using 1
  · funext v; rfl
  · ext v
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.proj_apply]
    ring

/-- The derivative of `coordShrink m c` at the origin is `c` times the identity. -/
lemma hasFDerivAt_coordShrink (m : ℕ) (c : ℝ) :
    HasFDerivAt (coordShrink m c)
      (c • (1 : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ))) 0 := by
  rw [show c • (1 : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) =
      ContinuousLinearMap.pi
        (fun l : Fin m => c • (ContinuousLinearMap.proj l : (Fin m → ℝ) →L[ℝ] ℝ)) by
    ext v l
    simp [ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]]
  unfold coordShrink
  rw [hasFDerivAt_pi]
  exact fun l => hasFDerivAt_coordShrink_apply m c l

/-- **Calculus of the coordinate-wise shrinking self-map.**  `coordShrink m c` fixes `0`, is real
analytic everywhere, and its derivative at `0` is `c` times the identity. -/
theorem coordShrink_calculus (m : ℕ) (c : ℝ) (hc : 0 < c) :
    coordShrink m c 0 = 0 ∧
      (∀ s : Fin m → ℝ, AnalyticAt ℝ (coordShrink m c) s) ∧
      fderiv ℝ (coordShrink m c) (0 : Fin m → ℝ) =
        c • (1 : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · funext l
    simp [coordShrink]
  · intro s
    unfold coordShrink
    rw [analyticAt_pi_iff]
    intro l
    have hproj : AnalyticAt ℝ (fun x : Fin m → ℝ => x l) s := by
      have h := ContinuousLinearMap.analyticAt
        (ContinuousLinearMap.proj l : (Fin m → ℝ) →L[ℝ] ℝ) s
      refine h.congr ?_
      filter_upwards with x
      exact ContinuousLinearMap.proj_apply l x
    exact (analyticAt_coordProfile c (s l)).comp (x := s)
      (f := fun x : Fin m → ℝ => x l) hproj
  · exact (hasFDerivAt_coordShrink m c).fderiv

end Work.WilE7
