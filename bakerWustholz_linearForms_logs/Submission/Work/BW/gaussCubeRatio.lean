import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Filter MeasureTheory

/-- Auxiliary lemma: for a continuous function `f : ℝ → ℝ`, the symmetric average
`δ ↦ δ⁻¹ ∫_{[-δ/2, δ/2]} f` tends to `f 0` as `δ → 0⁺`. -/
lemma gaussAux (f : ℝ → ℝ) (hf : Continuous f) :
    Tendsto (fun δ : ℝ => (1 / δ) * ∫ t in Set.Icc (-(δ/2)) (δ/2), f t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 0)) := by
  have hg : Continuous (fun t : ℝ => f (-t) + f t) := (hf.comp continuous_neg).add hf
  have hfneg : Continuous (fun t : ℝ => f (-t)) := hf.comp continuous_neg
  -- The symmetric integral equals the interval integral of `t ↦ f (-t) + f t` over `[0, δ/2]`.
  have key : ∀ δ : ℝ, 0 < δ →
      (∫ t in Set.Icc (-(δ/2)) (δ/2), f t) = ∫ s in (0:ℝ)..(δ/2), (f (-s) + f s) := by
    intro δ hδ
    have hle : -(δ/2) ≤ δ/2 := by linarith
    have h3 : (∫ t in (-(δ/2))..(0:ℝ), f t) = ∫ s in (0:ℝ)..(δ/2), f (-s) := by
      simp
    rw [show (∫ t in Set.Icc (-(δ/2)) (δ/2), f t) = ∫ t in (-(δ/2))..(δ/2), f t from
      (MeasureTheory.integral_Icc_eq_integral_Ioc).trans
        (intervalIntegral.integral_of_le hle).symm]
    have hab : IntervalIntegrable f volume (-(δ/2)) (0:ℝ) := hf.intervalIntegrable _ _
    have hbc : IntervalIntegrable f volume (0:ℝ) (δ/2) := hf.intervalIntegrable _ _
    have ha : IntervalIntegrable (fun s : ℝ => f (-s)) volume (0:ℝ) (δ/2) :=
      hfneg.intervalIntegrable _ _
    calc ∫ t in (-(δ/2))..(δ/2), f t
        = (∫ t in (-(δ/2))..(0:ℝ), f t) + (∫ t in (0:ℝ)..(δ/2), f t) :=
          (intervalIntegral.integral_add_adjacent_intervals hab hbc).symm
      _ = (∫ s in (0:ℝ)..(δ/2), f (-s)) + (∫ s in (0:ℝ)..(δ/2), f s) := by rw [h3]
      _ = ∫ s in (0:ℝ)..(δ/2), (f (-s) + f s) :=
          (intervalIntegral.integral_add ha hbc).symm
  -- Rescaling `δ ↦ δ/2` and the coefficient identity.
  have key2 : ∀ δ : ℝ, 0 < δ →
      (1/δ) * (∫ s in (0:ℝ)..(δ/2), (f (-s) + f s))
        = (1/2) * (δ/2)⁻¹ * (∫ s in (0:ℝ)..(δ/2), (f (-s) + f s)) := by
    intro δ hδ
    simp only [one_div]
    rw [inv_div]
    ring
  -- Fundamental theorem of calculus: derivative of the primitive at `0`.
  have hderiv : HasDerivAt (fun x : ℝ => ∫ s in (0:ℝ)..x, (f (-s) + f s)) (f 0 + f 0) 0 := by
    have h := intervalIntegral.integral_hasDerivAt_right (a := (0:ℝ)) (b := (0:ℝ))
      (f := fun s : ℝ => f (-s) + f s) (hg.intervalIntegrable 0 0)
      (hg.stronglyMeasurableAtFilter volume (nhds 0)) hg.continuousAt
    simpa using h
  have hH : Tendsto (fun x : ℝ => x⁻¹ * ∫ s in (0:ℝ)..x, (f (-s) + f s))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 0 + f 0)) := by
    have h := hderiv.tendsto_slope_zero_right
    simpa [intervalIntegral.integral_same] using h
  have hcont2 : Continuous (fun δ : ℝ => δ/2) := continuous_id.div_const 2
  have hdiv : Tendsto (fun δ : ℝ => δ/2) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using (hcont2.tendsto 0).mono_left
        (nhdsWithin_le_nhds : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ nhds 0)
    · filter_upwards [eventually_mem_nhdsWithin] with δ hδ
      simp only [Set.mem_Ioi] at hδ ⊢
      linarith
  have hlim : Tendsto
      (fun δ : ℝ => (1/2) * (δ/2)⁻¹ * (∫ s in (0:ℝ)..(δ/2), (f (-s) + f s)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 0)) := by
    have h := (hH.comp hdiv).const_mul ((1:ℝ)/2)
    have hc : (1/2 : ℝ) * (f 0 + f 0) = f 0 := by ring
    rw [hc] at h
    refine h.congr' ?_
    filter_upwards with δ
    simp only [Function.comp_apply]
    ring
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_mem_nhdsWithin] with δ hδ
  rw [key δ hδ, key2 δ hδ]

theorem gaussCubeRatio (m : ℕ) :
    Filter.Tendsto
      (fun δ : ℝ => ∏ _ : Fin m, (1 / δ) * ∫ t in Set.Icc (-(δ/2)) (δ/2), Real.exp (- Real.pi * t ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hF : Tendsto
      (fun δ : ℝ => (1 / δ) * ∫ t in Set.Icc (-(δ/2)) (δ/2), Real.exp (- Real.pi * t ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h := gaussAux (fun t : ℝ => Real.exp (- Real.pi * t ^ 2)) (by fun_prop)
    simpa using h
  have hpow : Tendsto
      (fun δ : ℝ => ((1 / δ) * ∫ t in Set.Icc (-(δ/2)) (δ/2), Real.exp (- Real.pi * t ^ 2)) ^ m)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using hF.pow m
  have hprod : Tendsto
      (fun δ : ℝ => ∏ _ : Fin m,
        ((1 / δ) * ∫ t in Set.Icc (-(δ/2)) (δ/2), Real.exp (- Real.pi * t ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    refine hpow.congr ?_
    intro δ
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact hprod

end Work.BW
