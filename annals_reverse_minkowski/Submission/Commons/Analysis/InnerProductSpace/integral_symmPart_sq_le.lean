import Mathlib.MeasureTheory.Function.L2Space

namespace Commons.Analysis.InnerProductSpace

open MeasureTheory Real

/-- If a measure `μ` is invariant under `x ↦ -x`, then `x ↦ -x` is almost everywhere
measurable. -/
theorem aemeasurable_neg_of_map_neg_eq_self {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (h : Measure.map (fun x : G => -x) μ = μ) :
    AEMeasurable (fun x : G => -x) μ := by
  by_contra hcon
  rw [Measure.map_of_not_aemeasurable hcon] at h
  rw [← h] at hcon
  exact hcon aemeasurable_zero_measure

/-- Change of variables `x ↦ -x` for the Bochner integral against a measure invariant under
negation.  Unlike `MeasureTheory.integral_neg_eq_self` this requires no measurability of
negation, only the invariance of the measure. -/
theorem integral_neg_comp_eq_self {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) [μ.IsNegInvariant] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : G → E} (hf : AEStronglyMeasurable f μ) :
    ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ := by
  have hneg : AEMeasurable (fun x : G => -x) μ :=
    aemeasurable_neg_of_map_neg_eq_self μ (Measure.map_neg_eq_self μ)
  have h1 : ∫ y, f y ∂(Measure.map (fun x : G => -x) μ) = ∫ x, f (-x) ∂μ :=
    integral_map hneg (by rw [Measure.map_neg_eq_self μ]; exact hf)
  rw [Measure.map_neg_eq_self μ] at h1
  exact h1.symm

/-- For a measure invariant under `x ↦ -x` and an even function `h`, replacing a function `w` by
its symmetric part `(w x + w (-x))/2` does not increase the `L²` distance to `h`. -/
theorem integral_symmPart_sq_le {G : Type*} [AddCommGroup G] [MeasurableSpace G] (μ : Measure G)
    [μ.IsNegInvariant] [IsFiniteMeasure μ] {h w : G → ℝ}
    (hh : ∀ x, h (-x) = h x) (hw : MemLp w 2 μ) (hh2 : MemLp h 2 μ) :
    ∫ x, (h x - (w x + w (-x)) / 2) ^ 2 ∂μ ≤ ∫ x, (h x - w x) ^ 2 ∂μ := by
  set s : G → ℝ := fun x => (w x + w (-x)) / 2 with hs_def
  have hneg : AEMeasurable (fun x : G => -x) μ :=
    aemeasurable_neg_of_map_neg_eq_self μ (Measure.map_neg_eq_self μ)
  -- `w (-·)` is again in `L²`
  have hw_neg : MemLp (fun x => w (-x)) 2 μ := by
    have h' : MemLp w 2 (Measure.map (fun x : G => -x) μ) := by
      rw [Measure.map_neg_eq_self μ]; exact hw
    exact MemLp.comp_of_map h' hneg
  -- the symmetric part is in `L²`
  have hs_mem : MemLp s 2 μ := by
    rw [hs_def]
    have hsum : MemLp (fun x => w x + w (-x)) 2 μ := hw.add hw_neg
    have := hsum.const_mul ((1 : ℝ) / 2)
    simpa [div_eq_mul_inv, mul_comm] using this
  have hws_mem : MemLp (fun x => h x - s x) 2 μ := hh2.sub hs_mem
  have hsw_mem : MemLp (fun x => s x - w x) 2 μ := hs_mem.sub hw
  have hhw_mem : MemLp (fun x => h x - w x) 2 μ := hh2.sub hw
  -- integrability of the squared terms
  have hAhw_int : Integrable (fun x => (h x - w x) ^ 2) μ := hhw_mem.integrable_sq
  have hAhs_int : Integrable (fun x => (h x - s x) ^ 2) μ := hws_mem.integrable_sq
  have hsw_sq_int : Integrable (fun x => (s x - w x) ^ 2) μ := hsw_mem.integrable_sq
  -- the symmetric part is even, the difference `s - w` is odd
  have hs_even : ∀ x, s (-x) = s x := by
    intro x
    simp only [hs_def, neg_neg]
    ring
  have hs_odd : ∀ x, s (-x) - w (-x) = -(s x - w x) := by
    intro x
    simp only [hs_def, neg_neg]
    ring
  -- cross term
  set c : G → ℝ := fun x => 2 * ((h x - s x) * (s x - w x)) with hc_def
  have hc_mem : MemLp c 1 μ := by
    rw [hc_def]
    have hφ : MemLp (fun x => 2 * (h x - s x)) 2 μ := hws_mem.const_mul 2
    have h' : MemLp ((fun x => 2 * (h x - s x)) * (fun x => s x - w x)) 1 μ :=
      hsw_mem.mul hφ
    refine h'.ae_eq ?_
    filter_upwards with x
    simp only [Pi.mul_apply]
    ring
  have hc_int : Integrable c μ := MemLp.integrable (q := 1) (le_refl 1) hc_mem
  have hc_odd : ∀ x, c (-x) = -c x := by
    intro x
    simp only [hc_def]
    have h1 : h (-x) = h x := hh x
    have h2 : s (-x) = s x := hs_even x
    have h3 : s (-x) - w (-x) = -(s x - w x) := hs_odd x
    rw [h1, h3, h2]
    ring
  have hc_zero : ∫ x, c x ∂μ = 0 := by
    have hsub : ∫ x, c (-x) ∂μ = ∫ x, c x ∂μ :=
      integral_neg_comp_eq_self μ hc_int.aestronglyMeasurable
    have hodd_int : ∫ x, c (-x) ∂μ = - ∫ x, c x ∂μ := by
      have hfun : (fun x => c (-x)) = fun x => -c x := funext hc_odd
      rw [hfun, integral_neg]
    linarith
  -- the algebraic identity
  have hkey : ∫ x, (h x - w x) ^ 2 ∂μ - ∫ x, (h x - s x) ^ 2 ∂μ
      = ∫ x, ((s x - w x) ^ 2 + c x) ∂μ := by
    rw [← integral_sub hAhw_int hAhs_int]
    apply integral_congr_ae
    filter_upwards with x
    simp only [hc_def]
    ring
  have hsplit : ∫ x, ((s x - w x) ^ 2 + c x) ∂μ
      = ∫ x, (s x - w x) ^ 2 ∂μ + ∫ x, c x ∂μ :=
    integral_add hsw_sq_int hc_int
  have hnonneg : 0 ≤ ∫ x, (s x - w x) ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg _)
  have : 0 ≤ ∫ x, (h x - w x) ^ 2 ∂μ - ∫ x, (h x - s x) ^ 2 ∂μ := by
    rw [hkey, hsplit, hc_zero, add_zero]
    exact hnonneg
  linarith

end Commons.Analysis.InnerProductSpace