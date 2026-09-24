import Mathlib

namespace Work.GM.Energy.EnergyCore

/-- **Change of variables `u = 1/v` on `[1/2,1]`** (`v ↦ 1/v` maps `[1/2,1]` onto `[1,2]`):
`∫_{1/2}^{1} K (1/v) dv = ∫_{1}^{2} K u / u² du` for `K` continuous on `[1/2,2]`.
(Route: `intervalIntegral.integral_comp_mul_deriv'` with `f v = 1/v`, `f' v = -1/v²`,
`g u = -K u / u²`: `∫_{1/2}^{1} (g ∘ f) * f' = ∫_{2}^{1} g = -∫_{1}^{2} g = ∫_{1}^{2} K u / u²`.) -/
theorem integral_comp_inv_half_one {K : ℝ → ℝ} (hK : ContinuousOn K (Set.Icc (1 / 2 : ℝ) 2)) :
    ∫ v in (1 / 2 : ℝ)..1, K (1 / v) = ∫ u in (1 : ℝ)..2, K u / u ^ 2 := by
  have hle : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hpos : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < x :=
    fun x hx => lt_of_lt_of_le (by norm_num) hx.1
  have hne : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, x ≠ 0 := fun x hx => ne_of_gt (hpos x hx)
  have hne' : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 1, x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    exact hne x ⟨hx.1, le_trans hx.2 (by norm_num)⟩
  -- the substitution `v ↦ 1/v` is differentiable on the interval with derivative `-1/v²`
  have hderiv : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 1,
      HasDerivAt (fun v : ℝ => 1 / v) (-(x ^ 2)⁻¹) x := by
    intro x hx
    simpa only [one_div] using hasDerivAt_inv (hne' x hx)
  have hcontf' : ContinuousOn (fun x : ℝ => -(x ^ 2)⁻¹) (Set.uIcc (1 / 2 : ℝ) 1) := by
    refine ContinuousOn.neg ?_
    exact ContinuousOn.inv₀ (continuousOn_id.pow 2) (fun x hx => pow_ne_zero 2 (hne' x hx))
  -- `1/v` maps `[1/2,1]` into `[1/2,2]`
  have himage : ((fun v : ℝ => 1 / v) '' Set.uIcc (1 / 2 : ℝ) 1) ⊆ Set.Icc (1 / 2 : ℝ) 2 := by
    rintro y ⟨x, hx, rfl⟩
    rw [Set.uIcc_of_le hle] at hx
    have hx0 : (0 : ℝ) < x := hpos x ⟨hx.1, le_trans hx.2 (by norm_num)⟩
    rw [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · have h := one_div_le_one_div_of_le hx0 hx.2
      have : (1 : ℝ) / 1 = 1 := by norm_num
      rw [this] at h
      linarith
    · have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hx.1
      have h2 : (1 : ℝ) / (1 / 2) = 2 := by norm_num
      rw [h2] at h
      exact h
  -- the auxiliary function `g u = -K u / u²` is continuous on `[1/2,2]`, hence on the image
  have hcontg : ContinuousOn (fun u : ℝ => -(K u / u ^ 2)) (Set.Icc (1 / 2 : ℝ) 2) :=
    (ContinuousOn.div hK (continuousOn_id.pow 2)
      (fun u hu => pow_ne_zero 2 (hne u hu))).neg
  have hcontg' : ContinuousOn (fun u : ℝ => -(K u / u ^ 2))
      ((fun v : ℝ => 1 / v) '' Set.uIcc (1 / 2 : ℝ) 1) := hcontg.mono himage
  -- change of variables
  have hmain := intervalIntegral.integral_comp_mul_deriv'
    (a := (1 / 2 : ℝ)) (b := 1)
    (f := fun v : ℝ => 1 / v) (f' := fun x : ℝ => -(x ^ 2)⁻¹)
    (g := fun u : ℝ => -(K u / u ^ 2))
    hderiv hcontf' hcontg'
  calc ∫ v in (1 / 2 : ℝ)..1, K (1 / v)
      = ∫ x in (1 / 2 : ℝ)..1,
          ((fun u : ℝ => -(K u / u ^ 2)) ∘ (fun v : ℝ => 1 / v)) x * (-(x ^ 2)⁻¹) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx0 : x ≠ 0 := hne' x hx
        simp only [Function.comp_apply]
        field_simp
    _ = ∫ x in (2 : ℝ)..1, -(K x / x ^ 2) := by
        simpa only [one_div_one_div, div_one] using hmain
    _ = -∫ x in (1 : ℝ)..2, -(K x / x ^ 2) := intervalIntegral.integral_symm 1 2
    _ = ∫ x in (1 : ℝ)..2, -(-(K x / x ^ 2)) :=
        (intervalIntegral.integral_neg (f := fun x : ℝ => -(K x / x ^ 2))).symm
    _ = ∫ u in (1 : ℝ)..2, K u / u ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring

end Work.GM.Energy.EnergyCore
