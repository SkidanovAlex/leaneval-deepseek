import Mathlib
import Submission.Work.FatouL1.lintegral_interval_le
import Submission.Work.FatouL1.epsLineMass
import Submission.Work.FatouL1.norm_vertEps_sub_le
import Submission.Work.FatouL1.strip_in_Qreg

namespace Work.FatouL1

open MeasureTheory Set

/-- **The shift mass bound.**  For `x` in the interior strip `(x₀ - 1, x₀ + 2)` the `L¹` mass of
the increment `ε (x + 1 + iy) - ε (x + iy)` of the displacement `ε = F - id` is again at most
`1/64`.  The increment is controlled by the horizontal integral of `‖F' - 1‖` on the segment
`[x, x+1] × {y}` (`norm_vertEps_sub_le`), and Tonelli plus the `L¹` hypothesis `NearTranslationL1`
on the two boundary lines of the big strip `(x₀ - 1, x₀ + 3)` gives the bound
`∫⁻_y ‖∫_x^{x+1} ‖F' (ξ + iy) - 1‖ dξ‖ ≤ (x + 1 - x) · 1/64 = 1/64`.

This is the "shifted line mass" input of the Fatou perturbation layer (`fatouMassMBound`). -/
theorem shiftEpsMass {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 2),
      ∫⁻ y : ℝ, ENNReal.ofReal
        ‖(F ((x : ℂ) + 1 + y * Complex.I) - ((x : ℂ) + 1 + y * Complex.I) - 1)
          - (F ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I) - 1)‖
        ≤ ENNReal.ofReal (1 / 64) := by
  intro t ht
  rw [Set.mem_Ioo] at ht
  -- ### Step 1: pointwise bound by the horizontal integral of the derivative defect.
  have hbound : ∀ y : ℝ,
      ‖(F ((t : ℂ) + 1 + y * Complex.I) - ((t : ℂ) + 1 + y * Complex.I) - 1)
        - (F ((t : ℂ) + y * Complex.I) - ((t : ℂ) + y * Complex.I) - 1)‖
      ≤ ∫ s in t..(t + 1), ‖vertDefect F s y‖ := by
    intro y
    have hsub := norm_vertEps_sub_le hF h₁ h₂ (x := t + 1) (x' := t)
      (by linarith [ht.1]) (by linarith [ht.2]) (by linarith [ht.1]) (by linarith [ht.2]) y
    rw [min_eq_right (by linarith : t ≤ t + 1), max_eq_left (by linarith : t ≤ t + 1)] at hsub
    have harg : ((t : ℂ) + 1 + y * Complex.I) = (((t + 1 : ℝ)) : ℂ) + y * Complex.I := by
      push_cast; ring
    have heq : ‖(F ((t : ℂ) + 1 + y * Complex.I) - ((t : ℂ) + 1 + y * Complex.I) - 1)
        - (F ((t : ℂ) + y * Complex.I) - ((t : ℂ) + y * Complex.I) - 1)‖
        = ‖vertEps F (t + 1) y - vertEps F t y‖ := by
      simp only [vertEps]
      rw [harg]
      congr 1
      ring
    rw [heq]
    exact hsub
  -- ### Step 2: integrate the pointwise bound.
  have hstep : ∫⁻ y : ℝ, ENNReal.ofReal
        ‖(F ((t : ℂ) + 1 + y * Complex.I) - ((t : ℂ) + 1 + y * Complex.I) - 1)
          - (F ((t : ℂ) + y * Complex.I) - ((t : ℂ) + y * Complex.I) - 1)‖
      ≤ ∫⁻ y : ℝ, ENNReal.ofReal (∫ s in t..(t + 1), ‖vertDefect F s y‖) :=
    lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hbound y)
  -- ### Step 3: continuity of the uncurried integrand on `ℝ × [t, t+1]`.
  have hcont : ContinuousOn (Function.uncurry fun y s : ℝ => ‖vertDefect F s y‖)
      ((Set.univ : Set ℝ) ×ˢ Set.Icc t (t + 1)) := by
    have hgc : Continuous fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) + ((p.1 : ℝ) : ℂ) * Complex.I := by
      fun_prop
    have hmap : MapsTo (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) + ((p.1 : ℝ) : ℂ) * Complex.I)
        ((Set.univ : Set ℝ) ×ˢ Set.Icc t (t + 1)) (MandelDim.Qreg b₁ b₂) :=
      fun p hp => mem_openStrip_Qreg (b₁ := b₁) (b₂ := b₂) h₁ h₂
        (x := p.2) (by have h := hp.2.1; linarith) (by have h := hp.2.2; linarith) p.1
    have h2 : ContinuousOn (fun p : ℝ × ℝ =>
        ‖deriv F (((p.2 : ℝ) : ℂ) + ((p.1 : ℝ) : ℂ) * Complex.I) - 1‖)
        ((Set.univ : Set ℝ) ×ˢ Set.Icc t (t + 1)) :=
      (((continuousOn_deriv_Qreg hF).comp' hgc.continuousOn hmap).sub
        continuousOn_const).norm
    simpa only [Function.uncurry_def, vertDefect] using h2
  -- ### Step 4: the `L¹` bound of `NearTranslationL1` on each line of `[t, t+1]`.
  have hinner : ∀ s ∈ Set.Icc t (t + 1),
      ∫⁻ y : ℝ, ENNReal.ofReal ‖vertDefect F s y‖ ≤ ENNReal.ofReal (1 / 64) := by
    intro s hs
    have hs1 : x₀ - 1 < s := lt_of_lt_of_le ht.1 hs.1
    have hs2 : s < x₀ + 3 := lt_of_le_of_lt hs.2 (by linarith [ht.2])
    simpa only [vertDefect] using
      hF.2 s (fun y => mem_openStrip_Qreg (b₁ := b₁) (b₂ := b₂) h₁ h₂ hs1 hs2 y)
  -- ### Step 5: Tonelli and integrate the constant bound.
  calc ∫⁻ y : ℝ, ENNReal.ofReal
        ‖(F ((t : ℂ) + 1 + y * Complex.I) - ((t : ℂ) + 1 + y * Complex.I) - 1)
          - (F ((t : ℂ) + y * Complex.I) - ((t : ℂ) + y * Complex.I) - 1)‖
      ≤ ∫⁻ y : ℝ, ENNReal.ofReal (∫ s in t..(t + 1), ‖vertDefect F s y‖) := hstep
    _ ≤ ∫⁻ s in Set.Icc t (t + 1), ∫⁻ y : ℝ, ENNReal.ofReal ‖vertDefect F s y‖ :=
        lintegral_interval_le (h := fun y s : ℝ => ‖vertDefect F s y‖)
          (a := t) (b := t + 1) (by linarith) hcont (fun y s => norm_nonneg _)
    _ ≤ ∫⁻ _s in Set.Icc t (t + 1), ENNReal.ofReal (1 / 64) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact hinner s hs
    _ = ENNReal.ofReal (1 / 64) := by
        have h1 : (t + 1 : ℝ) - t = 1 := by ring
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, h1,
          ENNReal.ofReal_one, mul_one]

end Work.FatouL1
