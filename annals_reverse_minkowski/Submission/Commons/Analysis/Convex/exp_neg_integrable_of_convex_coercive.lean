import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Topology.Separation.CompletelyRegular

namespace Commons.Analysis.Convex

open MeasureTheory Set Filter
open scoped Real Topology

/-- `x ↦ exp (c * x)` is integrable on `(-∞, a]` whenever `c > 0`. -/
lemma integrableOn_Iic_exp_mul (a c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => Real.exp (c * x)) (Iic a) volume := by
  rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
  rw [measurableEmbedding_neg.integrableOn_map_iff]
  simp only [neg_preimage, neg_Iic]
  change IntegrableOn (fun x : ℝ => Real.exp (c * (-x))) (Ici (-a)) volume
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-c * x)) (Ici (-a)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi
        (f := fun x : ℝ => Real.exp (-c * x)) (b := -a)).mpr
      (exp_neg_integrableOn_Ioi (-a) hc)
  simpa only [mul_neg, neg_mul] using h2

/-- If `V : ℝ → ℝ` is convex and coercive (`V → ∞` at both ends), then `x ↦ exp (-(V x))` is
integrable with respect to Lebesgue measure. -/
theorem exp_neg_integrable_of_convex_coercive (V : ℝ → ℝ) (hV : ConvexOn ℝ Set.univ V)
    (hVtop : Filter.Tendsto V Filter.atTop Filter.atTop)
    (hVbot : Filter.Tendsto V Filter.atBot Filter.atTop) :
    MeasureTheory.Integrable (fun x => Real.exp (-(V x))) MeasureTheory.volume := by
  have hVcont : Continuous V :=
    continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hV)
  have hfcont : Continuous (fun x : ℝ => Real.exp (-(V x))) :=
    Real.continuous_exp.comp hVcont.neg
  -- Find a point `a < 0` with `V 0 < V a`, and a point `b > 0` with `V 0 < V b`.
  obtain ⟨a0, ha0⟩ := Filter.eventually_atBot.mp
    (hVbot.eventually (Filter.eventually_gt_atTop (V 0)))
  set a : ℝ := min a0 (-1) with ha
  have ha_le : a ≤ a0 := by rw [ha]; exact min_le_left _ _
  have ha_lt : a < 0 := by
    rw [ha]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hVa : V 0 < V a := ha0 a ha_le
  obtain ⟨b0, hb0⟩ := Filter.eventually_atTop.mp
    (hVtop.eventually (Filter.eventually_gt_atTop (V 0)))
  set b : ℝ := max b0 1 with hb
  have hb_ge : b0 ≤ b := by rw [hb]; exact le_max_left _ _
  have hb_gt : 0 < b := by
    rw [hb]; exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hVb : V 0 < V b := hb0 b hb_ge
  -- Slopes of the two relevant chords.
  set cL : ℝ := (V a - V 0) / (0 - a) with hcL
  set cR : ℝ := (V b - V 0) / (b - 0) with hcR
  have ha_pos : (0 : ℝ) - a > 0 := by linarith
  have hb_pos : b - 0 > 0 := by linarith
  have hcL_pos : 0 < cL := by rw [hcL]; exact div_pos (by linarith) ha_pos
  have hcR_pos : 0 < cR := by rw [hcR]; exact div_pos (by linarith) hb_pos
  -- Chord lower bounds for `V` outside the two intervals.
  have hchordL : ∀ z : ℝ, z ≤ a → V a - cL * (z - a) ≤ V z := by
    intro z hz
    rcases lt_or_eq_of_le hz with hzlt | hzeq
    · have hsec := hV.secant_mono_aux1 (x := z) (y := a) (z := 0)
        (Set.mem_univ z) (Set.mem_univ 0) hzlt ha_lt
      have key : V a - cL * (z - a) = ((0 - z) * V a - (a - z) * V 0) / (0 - a) := by
        rw [hcL]; field_simp; ring
      rw [key, div_le_iff₀ ha_pos]
      linarith [hsec]
    · rw [hzeq]; simp
  have hchordR : ∀ z : ℝ, b ≤ z → V 0 + cR * z ≤ V z := by
    intro z hz
    rcases lt_or_eq_of_le hz with hzlt | hzeq
    · have hsec := hV.secant_mono_aux1 (x := 0) (y := b) (z := z)
        (Set.mem_univ 0) (Set.mem_univ z) hb_gt hzlt
      have key : V 0 + cR * z = ((z - 0) * V b - (z - b) * V 0) / (b - 0) := by
        rw [hcR]; field_simp; ring
      rw [key, div_le_iff₀ hb_pos]
      linarith [hsec]
    · rw [← hzeq]
      have : cR * b = V b - V 0 := by rw [hcR]; field_simp; ring
      linarith [this]
  -- Exponential bounds.
  set CL : ℝ := Real.exp (-(V a) - cL * a) with hCL
  set CR : ℝ := Real.exp (-(V 0)) with hCR
  have hboundL : ∀ z : ℝ, z ≤ a →
      Real.exp (-(V z)) ≤ CL * Real.exp (cL * z) := by
    intro z hz
    have h1 : -(V z) ≤ (-(V a) - cL * a) + cL * z := by
      have := hchordL z hz; linarith
    calc Real.exp (-(V z)) ≤ Real.exp ((-(V a) - cL * a) + cL * z) := Real.exp_le_exp.mpr h1
      _ = CL * Real.exp (cL * z) := by rw [Real.exp_add, hCL]
  have hboundR : ∀ z : ℝ, b ≤ z →
      Real.exp (-(V z)) ≤ CR * Real.exp (-cR * z) := by
    intro z hz
    have h1 : -(V z) ≤ -(V 0) + (-cR * z) := by
      have := hchordR z hz; linarith
    calc Real.exp (-(V z)) ≤ Real.exp (-(V 0) + -cR * z) := Real.exp_le_exp.mpr h1
      _ = CR * Real.exp (-cR * z) := by rw [Real.exp_add, hCR]
  -- Integrability on the two tails.
  have hintL : IntegrableOn (fun z : ℝ => Real.exp (cL * z)) (Iic a) volume :=
    integrableOn_Iic_exp_mul a cL hcL_pos
  have hL : IntegrableOn (fun z : ℝ => Real.exp (-(V z))) (Iic a) volume := by
    refine Integrable.mono' (hintL.const_mul CL) (hfcont.aestronglyMeasurable) ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Iic]
    refine Filter.Eventually.of_forall (fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hboundL z hz
  have hintR : IntegrableOn (fun z : ℝ => Real.exp (-cR * z)) (Ici b) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi
        (f := fun z : ℝ => Real.exp (-cR * z)) (b := b)).mpr
      (exp_neg_integrableOn_Ioi b hcR_pos)
  have hR : IntegrableOn (fun z : ℝ => Real.exp (-(V z))) (Ici b) volume := by
    refine Integrable.mono' (hintR.const_mul CR) (hfcont.aestronglyMeasurable) ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    refine Filter.Eventually.of_forall (fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hboundR z hz
  -- Integrability on the middle compact interval.
  have hM : IntegrableOn (fun z : ℝ => Real.exp (-(V z))) (Icc a b) volume :=
    ContinuousOn.integrableOn_compact isCompact_Icc hfcont.continuousOn
  -- Glue the three pieces together.
  have hab : a ≤ b := by linarith
  have h1 : IntegrableOn (fun z : ℝ => Real.exp (-(V z))) (Iic b) volume := by
    have hu := hL.union hM
    rw [Iic_union_Icc_eq_Iic hab] at hu
    exact hu
  have h2 : IntegrableOn (fun z : ℝ => Real.exp (-(V z))) univ volume := by
    have hu := h1.union hR
    rw [Iic_union_Ici] at hu
    exact hu
  exact integrableOn_univ.mp h2

end Commons.Analysis.Convex