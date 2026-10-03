import Mathlib

namespace Work.FIArea4.Vflip.Vfd

open MeasureTheory Filter

/-- The improper integral `∫_{t}^{∞} u^{-2} du = t^{-1}` for `t > 0`. -/
lemma integral_inv_sq_Ioi (t : ℝ) (ht : 0 < t) : ∫ u in Set.Ioi t, ((u:ℝ)^2)⁻¹ = t⁻¹ := by
  have h := integral_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) ht
  rw [show (-2:ℝ)+1 = -1 by norm_num] at h
  rw [Real.rpow_neg_one] at h
  rw [show (-t⁻¹)/(-1) = t⁻¹ by ring] at h
  rw [← h]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  have hu0 : 0 ≤ u := le_of_lt (lt_trans ht hu)
  rw [Real.rpow_neg hu0 2, Real.rpow_two]

/-- The improper integral `∫_{-∞}^{-t} u^{-2} du = t^{-1}` for `t > 0`. -/
lemma integral_inv_sq_Iic (t : ℝ) (ht : 0 < t) : ∫ u in Set.Iic (-t), ((u:ℝ)^2)⁻¹ = t⁻¹ := by
  have hsym := integral_comp_neg_Ioi (c := t) (f := fun x : ℝ => ((x:ℝ)^2)⁻¹)
  simp only [neg_sq] at hsym
  rw [integral_inv_sq_Ioi t ht] at hsym
  exact hsym.symm

/-- A function on `ℝ` is bounded by `4 √(A B)` in `L¹` as soon as it is bounded by `A`
everywhere and by `B / u ^ 2` away from the origin.  The proof splits the integral at
`t = √(B / A)`: on `[-t, t]` the bound `A` gives `2 t A`, while on the two tails the bound
`B / u^2` gives `2 B / t`; since `A t^2 = B` both pieces equal `2 √(A B)`. -/
theorem fourier_l1_sqrt (f : ℝ → ℂ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h1 : ∀ u : ℝ, ‖FourierTransform.fourier f u‖ ≤ A)
    (h2 : ∀ u : ℝ, u ≠ 0 → ‖FourierTransform.fourier f u‖ ≤ B / u ^ 2) :
    ∫ u : ℝ, ‖FourierTransform.fourier f u‖ ≤ 4 * Real.sqrt (A * B) := by
  classical
  by_cases hA0 : A = 0
  · -- `A = 0`: the transform vanishes identically.
    have hzero : ∀ u : ℝ, ‖FourierTransform.fourier f u‖ = 0 := by
      intro u
      have hle := h1 u
      rw [hA0] at hle
      exact le_antisymm hle (norm_nonneg _)
    have heq : (fun u : ℝ => ‖FourierTransform.fourier f u‖) = fun _ => (0:ℝ) := funext hzero
    rw [heq, MeasureTheory.integral_zero, hA0]
    simp
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    by_cases hB0 : B = 0
    · -- `B = 0`: the transform vanishes almost everywhere.
      have hzero : ∀ᵐ u ∂(volume : Measure ℝ), ‖FourierTransform.fourier f u‖ = 0 := by
        have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 0 := by
          rw [MeasureTheory.ae_iff]; simp
        filter_upwards [hne] with u hu
        have hle := h2 u hu
        rw [hB0, zero_div] at hle
        exact le_antisymm hle (norm_nonneg _)
      have heq : (∫ u : ℝ, ‖FourierTransform.fourier f u‖) = ∫ _ : ℝ, (0:ℝ) :=
        MeasureTheory.integral_congr_ae hzero
      rw [heq, MeasureTheory.integral_zero, hB0]
      simp
    · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
      have hABpos : 0 < B / A := div_pos hBpos hApos
      -- the cut-off scale
      set t : ℝ := Real.sqrt (B / A) with ht_def
      have htpos : 0 < t := Real.sqrt_pos.mpr hABpos
      have ht_nonneg : 0 ≤ t := le_of_lt htpos
      have ht_sq : t ^ 2 = B / A := by
        rw [ht_def]; exact Real.sq_sqrt (le_of_lt hABpos)
      have hAt2 : A * t ^ 2 = B := by
        rw [ht_sq]; exact mul_div_cancel₀ B hA0
      -- the dominating majorant
      set g : ℝ → ℝ := fun u => if |u| ≤ t then A else B / u ^ 2 with hg_def
      have hg_nonneg : ∀ u, 0 ≤ g u := by
        intro u
        simp only [hg_def]
        by_cases hu : |u| ≤ t
        · rw [if_pos hu]; exact hA
        · rw [if_neg hu]; exact div_nonneg hB (sq_nonneg u)
      have hg_le : ∀ u, g u ≤ (A + B) * (1 + u ^ 2)⁻¹ := by
        intro u
        simp only [hg_def]
        have hpos : (0:ℝ) < 1 + u ^ 2 := by positivity
        by_cases hu : |u| ≤ t
        · rw [if_pos hu]
          have hu2 : u ^ 2 ≤ t ^ 2 := by
            have h := pow_le_pow_left₀ (abs_nonneg u) hu 2
            rwa [sq_abs] at h
          have hAu2 : A * u ^ 2 ≤ B := by
            have h := mul_le_mul_of_nonneg_left hu2 (le_of_lt hApos)
            rwa [hAt2] at h
          rw [← div_eq_mul_inv, le_div_iff₀ hpos]
          nlinarith
        · rw [if_neg hu]
          have hu2 : t ^ 2 < u ^ 2 := by
            have h := pow_lt_pow_left₀ (not_le.mp hu) ht_nonneg (by norm_num : (2:ℕ) ≠ 0)
            rwa [sq_abs] at h
          have hAu2 : B < A * u ^ 2 := by
            have h := mul_lt_mul_of_pos_left hu2 hApos
            rwa [hAt2] at h
          have hupos : (0:ℝ) < u ^ 2 := lt_of_le_of_lt (sq_nonneg t) hu2
          rw [← div_eq_mul_inv, div_le_iff₀ hupos, div_mul_eq_mul_div, le_div_iff₀ hpos]
          nlinarith
      have hg_meas : Measurable g := by
        rw [hg_def]
        exact Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_const
          (measurable_const.div (measurable_id.pow_const 2))
      have hg_int : Integrable g := by
        refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (A+B))
          hg_meas.aestronglyMeasurable ?_
        filter_upwards with u
        rw [Real.norm_of_nonneg (hg_nonneg u)]
        exact hg_le u
      have hfg : ∀ u, ‖FourierTransform.fourier f u‖ ≤ g u := by
        intro u
        simp only [hg_def]
        by_cases hu : |u| ≤ t
        · rw [if_pos hu]; exact h1 u
        · rw [if_neg hu]
          have hu0 : u ≠ 0 := by
            intro h; subst h; simp at hu; linarith
          exact h2 u hu0
      -- the three pieces of the majorant
      have hIic : ∫ u in Set.Iic (-t), g u = B * t⁻¹ := by
        have hcongr : ∫ u in Set.Iic (-t), g u = ∫ u in Set.Iic (-t), B / u ^ 2 := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Iic (fun u hu => ?_)
          simp only [hg_def]
          by_cases hle : |u| ≤ t
          · rw [if_pos hle]
            rw [abs_le] at hle
            have hue : u = -t := le_antisymm hu (by linarith [hle.1])
            subst hue
            rw [neg_sq, ← hAt2, mul_div_cancel_right₀ A (pow_ne_zero 2 (ne_of_gt htpos))]
          · rw [if_neg hle]
        rw [hcongr]
        have hcm : ∫ u in Set.Iic (-t), B / u ^ 2 = B * ∫ u in Set.Iic (-t), ((u:ℝ)^2)⁻¹ := by
          rw [show (fun u : ℝ => B / u^2) = fun u => B * (u^2)⁻¹ from by
            funext u; rw [div_eq_mul_inv]]
          exact MeasureTheory.integral_const_mul B _
        rw [hcm, integral_inv_sq_Iic t htpos]
      have hIoc : ∫ u in Set.Ioc (-t) t, g u = 2 * t * A := by
        have hcongr : ∫ u in Set.Ioc (-t) t, g u = ∫ u in Set.Ioc (-t) t, A := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
          simp only [hg_def]
          rw [if_pos]
          rw [abs_le]; exact ⟨le_of_lt hu.1, hu.2⟩
        rw [hcongr, MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le (by linarith),
          smul_eq_mul]
        ring
      have hIoi : ∫ u in Set.Ioi t, g u = B * t⁻¹ := by
        have hcongr : ∫ u in Set.Ioi t, g u = ∫ u in Set.Ioi t, B / u ^ 2 := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
          simp only [hg_def]
          rw [if_neg]
          intro hle
          rw [abs_le] at hle
          have hu' : t < u := hu
          linarith [hle.2, hu']
        rw [hcongr]
        have hcm : ∫ u in Set.Ioi t, B / u ^ 2 = B * ∫ u in Set.Ioi t, ((u:ℝ)^2)⁻¹ := by
          rw [show (fun u : ℝ => B / u^2) = fun u => B * (u^2)⁻¹ from by
            funext u; rw [div_eq_mul_inv]]
          exact MeasureTheory.integral_const_mul B _
        rw [hcm, integral_inv_sq_Ioi t htpos]
      -- assemble the integral of the majorant
      have h1c : (∫ u in Set.Iic (-t), g u) + (∫ u in Set.Ioi (-t), g u) = ∫ u, g u := by
        rw [← MeasureTheory.integral_add_compl (μ := volume) (s := Set.Iic (-t)) measurableSet_Iic
          hg_int, Set.compl_Iic]
      have hunion : Set.Ioc (-t) t ∪ Set.Ioi t = Set.Ioi (-t) := by
        have hmax : max (-t) t = t := max_eq_right (by linarith)
        have hmin : min (-t) t = -t := min_eq_left (by linarith)
        rw [Set.Ioc_union_Ioi (a := -t) (b := t) (c := t) (by rw [hmax]), hmin]
      have h2c : ∫ u in Set.Ioi (-t), g u
          = (∫ u in Set.Ioc (-t) t, g u) + (∫ u in Set.Ioi t, g u) := by
        rw [← hunion]
        exact MeasureTheory.setIntegral_union (s := Set.Ioc (-t) t) (t := Set.Ioi t)
          (Set.Ioc_disjoint_Ioi (a := -t) (b := t) (c := t) le_rfl) measurableSet_Ioi
          hg_int.integrableOn hg_int.integrableOn
      have hint : ∫ u, g u = 4 * Real.sqrt (A * B) := by
        have hBt : B * t⁻¹ = A * t := by rw [← hAt2]; field_simp
        have hsq : Real.sqrt (A * B) = A * t := by
          have h1' : A * B = (A * t)^2 := by rw [← hAt2]; ring
          rw [h1', Real.sqrt_sq (mul_nonneg hA ht_nonneg)]
        calc ∫ u, g u = (∫ u in Set.Iic (-t), g u) + (∫ u in Set.Ioi (-t), g u) := h1c.symm
          _ = B * t⁻¹ + (∫ u in Set.Ioi (-t), g u) := by rw [hIic]
          _ = B * t⁻¹ + ((∫ u in Set.Ioc (-t) t, g u) + (∫ u in Set.Ioi t, g u)) := by
                rw [h2c]
          _ = B * t⁻¹ + (2 * t * A + B * t⁻¹) := by rw [hIoc, hIoi]
          _ = 4 * Real.sqrt (A * B) := by rw [hBt, hsq]; ring
      calc ∫ u : ℝ, ‖FourierTransform.fourier f u‖ ≤ ∫ u, g u :=
            MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall (fun u => norm_nonneg _))
              hg_int (Eventually.of_forall hfg)
        _ = 4 * Real.sqrt (A * B) := hint

end Work.FIArea4.Vflip.Vfd
