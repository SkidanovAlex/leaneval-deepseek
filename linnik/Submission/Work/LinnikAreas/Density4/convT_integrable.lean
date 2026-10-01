import Mathlib
import Submission.Work.LinnikAreas.Density4.TestFun

namespace Work.LinnikAreas.Density4

/-! ## Integrability of the convolution `gT ⋆ gT`

The test function `gT θ lam` is the indicator of the compact interval `[-γ, γ]`
(`γ = gammaT θ lam`) of the *continuous* function
`t ↦ λ̂ (1+tan²θ) (cos(ζt) - cos θ)` (`ζ = zetaT θ lam`).  Hence it is integrable, and so
is its convolution with itself — which is exactly the parametrised integral
`v ↦ ∫ s, gT θ lam s * gT θ lam (v - s)` appearing in `convT_integrable`.

These two facts are proved here: `gT_integrable_aux` (integrability of `gT`) and the target
`convT_integrable` (integrability of the convolution), the latter via Mathlib's
`Integrable.integrable_convolution` (Young's inequality for `L¹`). -/

/-- `gT θ lam` is (the indicator of the compact interval `[-γ,γ]` of) a continuous function,
hence integrable.  No hypothesis on `θ` or `lam` is needed. -/
lemma gT_integrable_aux (θ lam : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ => gT θ lam t) := by
  have hA : Continuous (fun t : ℝ => lam * (1 + Real.tan θ ^ 2) *
      (Real.cos (zetaT θ lam * t) - Real.cos θ)) := by fun_prop
  have heq : (fun t : ℝ => gT θ lam t)
      = Set.indicator (Set.Icc (-(gammaT θ lam)) (gammaT θ lam))
          (fun t : ℝ => lam * (1 + Real.tan θ ^ 2)
            * (Real.cos (zetaT θ lam * t) - Real.cos θ)) := by
    funext t
    simp only [gT, Set.indicator_apply, Set.mem_Icc, abs_le]
  rw [heq]
  exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr hA.integrableOn_Icc

/-- **Integrability of the convolution `gT ⊛ gT`.**  Since `gT θ lam` is integrable (indeed
bounded with compact support), `L¹ ⋆ L¹ ⊆ L¹` (Young's inequality,
`MeasureTheory.Integrable.integrable_convolution`) gives directly that
`v ↦ ∫ s, gT θ lam s * gT θ lam (v - s)` is integrable. -/
theorem convT_integrable {θ lam : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam) :
    MeasureTheory.Integrable (fun v : ℝ => ∫ s : ℝ, gT θ lam s * gT θ lam (v - s)) := by
  have hG : MeasureTheory.Integrable (fun t : ℝ => gT θ lam t) := gT_integrable_aux θ lam
  have h := MeasureTheory.Integrable.integrable_convolution
    (f := fun t : ℝ => gT θ lam t) (g := fun t : ℝ => gT θ lam t)
    (L := ContinuousLinearMap.mul ℝ ℝ) (μ := MeasureTheory.volume) hG hG
  have heq : MeasureTheory.convolution (fun t : ℝ => gT θ lam t) (fun t : ℝ => gT θ lam t)
      (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume
      = fun v : ℝ => ∫ s : ℝ, gT θ lam s * gT θ lam (v - s) := by
    funext v
    rw [MeasureTheory.convolution_mul]
  rwa [heq] at h

end Work.LinnikAreas.Density4
