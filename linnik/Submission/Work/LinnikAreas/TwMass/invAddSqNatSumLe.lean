import Mathlib

namespace Work.LinnikAreas.TwMass

open MeasureTheory Set Filter

theorem invAddSqNatSumLe : ∀ (A h : ℝ), 0 < A → 0 < h →
    Summable (fun j : ℕ => (1 : ℝ) / (A + ((j : ℝ) * h) ^ 2)) ∧
    (∑' j : ℕ, (1 : ℝ) / (A + ((j : ℝ) * h) ^ 2))
      ≤ 3 * (1 / A + 1 / (h * Real.sqrt A)) := by
  intro A h hA hh
  set s : ℝ := Real.sqrt A with hs
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hA
  have hs2 : s ^ 2 = A := by rw [hs]; exact Real.sq_sqrt hA.le
  have hnonneg : ∀ t ∈ Set.Ioi (0:ℝ), 0 ≤ (1:ℝ)/(A + (t*h)^2) := by
    intro t ht; positivity
  -- Monotonicity of the summand on [0,∞)
  have hanti : AntitoneOn (fun x : ℝ => (1:ℝ)/(A + (x*h)^2)) (Set.Ici 0) := by
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    have hxn : 0 ≤ x*h := by positivity
    have hle : x*h ≤ y*h := by nlinarith
    have h1 : (x*h)^2 ≤ (y*h)^2 := pow_le_pow_left₀ hxn hle 2
    have h2 : 0 < A + (x*h)^2 := by positivity
    exact one_div_le_one_div_of_le h2 (by linarith)
  -- Integrability on (0,∞) by comparison with `1/(1+x^2)`
  have hint : IntegrableOn (fun x : ℝ => (1:ℝ)/(A + (x*h)^2)) (Set.Ioi 0) := by
    have hm : 0 < min A (h^2) := lt_min hA (pow_pos hh 2)
    have hcont : Continuous (fun x : ℝ => (1:ℝ)/(A + (x*h)^2)) := by
      apply Continuous.div continuous_const _ (fun x => by positivity)
      fun_prop
    have hintg : Integrable (fun x : ℝ => (1/min A (h^2)) * ((1:ℝ)+x^2)⁻¹) volume :=
      integrable_inv_one_add_sq.const_mul (1/min A (h^2))
    have hbound : ∀ x : ℝ, (1:ℝ)/(A + (x*h)^2) ≤ (1/min A (h^2)) * ((1:ℝ)+x^2)⁻¹ := by
      intro x
      have hxh : (x*h)^2 = h^2 * x^2 := by ring
      rw [hxh]
      have hm1 : min A (h^2) ≤ A := min_le_left _ _
      have hm2 : min A (h^2) ≤ h^2 := min_le_right _ _
      have hden : min A (h^2) * (1 + x^2) ≤ A + h^2 * x^2 := by
        nlinarith [hm1, hm2, sq_nonneg x]
      have hpos : 0 < min A (h^2) * (1+x^2) := by positivity
      have hle := one_div_le_one_div_of_le hpos hden
      simpa [one_div, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hle
    have hnorm : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0:ℝ))),
        ‖(1:ℝ)/(A + (x*h)^2)‖ ≤ (1/min A (h^2)) * ((1:ℝ)+x^2)⁻¹ :=
      ae_restrict_of_forall_mem measurableSet_Ioi (fun x _ => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact hbound x)
    exact Integrable.mono' hintg.integrableOn hcont.aestronglyMeasurable.restrict hnorm
  -- Bound on the improper integral
  have hbd : (∫ x in Set.Ioi 0, (1:ℝ)/(A + (x*h)^2)) ≤ 2/(h*s) := by
    set c : ℝ := h / s with hc
    have hcpos : 0 < c := by rw [hc]; positivity
    have hderiv : ∀ x ∈ Set.Ici (0:ℝ),
        HasDerivAt (fun y : ℝ => (1/(h*s)) * Real.arctan (c*y)) ((1:ℝ)/(A + (x*h)^2)) x := by
      intro x hx
      have hinner : HasDerivAt (fun y : ℝ => c*y) c x := by
        simpa using (hasDerivAt_id x).const_mul c
      have h1 : HasDerivAt (Real.arctan ∘ fun y : ℝ => c*y) ((1 + (c*x)^2)⁻¹ * c) x :=
        (Real.hasDerivAt_arctan' (c*x)).comp x hinner
      have h2 : HasDerivAt (fun y : ℝ => (1/(h*s)) * Real.arctan (c*y))
          ((1/(h*s)) * ((1 + (c*x)^2)⁻¹ * c)) x := h1.const_mul (1/(h*s))
      refine h2.congr_deriv ?_
      rw [hc, ← hs2]
      field_simp
    have hlim : Tendsto (fun y : ℝ => (1/(h*s)) * Real.arctan (c*y)) atTop
        (nhds ((1/(h*s))*(Real.pi/2))) := by
      have h1 : Tendsto (fun y : ℝ => c*y) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hcpos tendsto_id
      have h2 : Tendsto Real.arctan atTop (nhds (Real.pi/2)) :=
        tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop
      exact (h2.comp h1).const_mul (1/(h*s))
    have hmain : (∫ x in Set.Ioi 0, (1:ℝ)/(A + (x*h)^2)) = (1/(h*s))*(Real.pi/2) := by
      have := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
      simpa using this
    rw [hmain]
    have hpi : Real.pi/2 ≤ 2 := by linarith [Real.pi_lt_four]
    have h2' : (2:ℝ)/(h*s) = (1/(h*s))*2 := by ring
    rw [h2']
    exact mul_le_mul_of_nonneg_left hpi (by positivity)
  refine ⟨hanti.summable_of_integrableOn_Ioi_zero hint hnonneg, ?_⟩
  have htsum := hanti.tsum_le_integral hint hnonneg
  calc (∑' j : ℕ, (1:ℝ)/(A + ((j:ℝ)*h)^2))
      = ∑' n : ℕ, (fun x : ℝ => (1:ℝ)/(A + (x*h)^2)) n := rfl
    _ ≤ (fun x : ℝ => (1:ℝ)/(A + (x*h)^2)) 0
          + ∫ x in Set.Ioi 0, (1:ℝ)/(A + (x*h)^2) := htsum
    _ ≤ 1/A + 2/(h*s) := by
        have h0 : (fun x : ℝ => (1:ℝ)/(A + (x*h)^2)) 0 = 1/A := by simp
        rw [h0]; linarith [hbd]
    _ ≤ 3*(1/A + 1/(h*Real.sqrt A)) := by
        rw [hs]
        have hsnn : 0 ≤ h * Real.sqrt A := by positivity
        rw [show 3*(1/A + 1/(h*Real.sqrt A)) = 3/A + 3/(h*Real.sqrt A) by ring]
        exact add_le_add (div_le_div_of_nonneg_right (by norm_num) hA.le)
                         (div_le_div_of_nonneg_right (by norm_num) hsnn)

end Work.LinnikAreas.TwMass
