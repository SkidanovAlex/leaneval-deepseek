import Mathlib

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Work.Holonomy3

/-- If `g ≥ 0` is measurable, `log (g+1) ≤ C` and for a sequence `e n ↓ 0` the smoothed
logs `log (g + e n)` have integrals bounded below by `L`, then `log g` is integrable.
The proof compares `log (g + e n)` with `log g` through Fatou's lemma applied to the
negative parts. -/
theorem integrable_of_smoothed_lower_bound {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} [MeasureTheory.IsProbabilityMeasure μ]
    {g : X → ℝ} (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x) {C L : ℝ} (hC : 0 ≤ C)
    (hgC : ∀ x, Real.log (g x + 1) ≤ C)
    {e : ℕ → ℝ} (he0 : ∀ n, 0 < e n) (he1 : ∀ n, e n ≤ 1)
    (het : Filter.Tendsto e Filter.atTop (nhds 0))
    (hlow : ∀ n, L ≤ ∫ x, Real.log (g x + e n) ∂μ) :
    MeasureTheory.Integrable (fun x => Real.log (g x)) μ := by
  -- The smoothed logs are bounded above by `C`.
  have hfn_le_C : ∀ n x, Real.log (g x + e n) ≤ C := by
    intro n x
    refine le_trans (Real.log_le_log (by linarith [hg0 x, he0 n]) (by linarith [he1 n])) (hgC x)
  -- hence each of them is integrable (bounded above by `C` and below by `log (e n)`).
  have hfn_int : ∀ n, Integrable (fun x => Real.log (g x + e n)) μ := by
    intro n
    refine Integrable.of_bound ((hgm.add_const (e n)).log).aestronglyMeasurable
      (max |Real.log (e n)| |C|) ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_le]
    have ha : Real.log (e n) ≤ Real.log (g x + e n) :=
      Real.log_le_log (he0 n) (by linarith [hg0 x])
    have hb : Real.log (g x + e n) ≤ C := hfn_le_C n x
    constructor
    · linarith [neg_le_abs (Real.log (e n)), le_max_left |Real.log (e n)| |C|]
    · linarith [le_abs_self C, le_max_right |Real.log (e n)| |C|]
  -- upper bound on the integral of the positive part.
  have hA : ∀ n, ∫⁻ x, ENNReal.ofReal (Real.log (g x + e n)) ∂μ ≤ ENNReal.ofReal C := by
    intro n
    calc ∫⁻ x, ENNReal.ofReal (Real.log (g x + e n)) ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal C ∂μ :=
          lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hfn_le_C n x))
      _ = ENNReal.ofReal C * μ Set.univ := lintegral_const _
      _ = ENNReal.ofReal C := by rw [measure_univ, mul_one]
  -- the negative part of `log (g + e n)` has lintegral bounded by `ofReal (C - L)`.
  have key : ∀ n, ∫⁻ x, ENNReal.ofReal (-(Real.log (g x + e n))) ∂μ
      ≤ ENNReal.ofReal (C - L) := by
    intro n
    have hpi := integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hfn_int n)
    have hA' : (∫⁻ x, ENNReal.ofReal (Real.log (g x + e n)) ∂μ).toReal ≤ C := by
      have h1 := ENNReal.toReal_mono (a := ∫⁻ x, ENNReal.ofReal (Real.log (g x + e n)) ∂μ)
        (b := ENNReal.ofReal C) ENNReal.ofReal_ne_top (hA n)
      rwa [ENNReal.toReal_ofReal hC] at h1
    have hB' : (∫⁻ x, ENNReal.ofReal (-(Real.log (g x + e n))) ∂μ).toReal ≤ C - L := by
      linarith [hlow n, hA', hpi]
    have hfin : (∫⁻ x, ENNReal.ofReal (-(Real.log (g x + e n))) ∂μ) < ∞ := by
      have hfi : HasFiniteIntegral (fun x => Real.log (g x + e n)) μ := (hfn_int n).2
      rw [hasFiniteIntegral_iff_enorm] at hfi
      refine lt_of_le_of_lt (lintegral_mono ?_) hfi
      intro x
      show ENNReal.ofReal (-(Real.log (g x + e n))) ≤ ‖Real.log (g x + e n)‖ₑ
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
    rw [← ENNReal.ofReal_toReal (ne_top_of_lt hfin)]
    exact ENNReal.ofReal_le_ofReal hB'
  -- pointwise: the negative part of `log g` is dominated by the liminf of the negative parts.
  have hpt : ∀ x, ENNReal.ofReal (-(Real.log (g x))) ≤
      liminf (fun n => ENNReal.ofReal (-(Real.log (g x + e n)))) atTop := by
    intro x
    rcases eq_or_lt_of_le (hg0 x) with h0 | hpos
    · rw [← h0, Real.log_zero, neg_zero, ENNReal.ofReal_zero]
      exact zero_le
    · have ht1 : Tendsto (fun n : ℕ => g x + e n) atTop (nhds (g x)) := by
        simpa using (tendsto_const_nhds (x := g x) (f := atTop)).add het
      have hsl : Tendsto (fun n : ℕ => Real.log (g x + e n)) atTop (nhds (Real.log (g x))) :=
        (Real.continuousAt_log (ne_of_gt hpos)).tendsto.comp ht1
      have ht3 : Tendsto (fun n : ℕ => -(Real.log (g x + e n))) atTop
          (nhds (-(Real.log (g x)))) := hsl.neg
      have ht4 : Tendsto (fun n : ℕ => ENNReal.ofReal (-(Real.log (g x + e n)))) atTop
          (nhds (ENNReal.ofReal (-(Real.log (g x))))) :=
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht3
      exact le_of_eq (Tendsto.liminf_eq ht4).symm
  -- Fatou's lemma.
  have hFatou : ∫⁻ x, liminf (fun n => ENNReal.ofReal (-(Real.log (g x + e n)))) atTop ∂μ
      ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (-(Real.log (g x + e n))) ∂μ) atTop :=
    lintegral_liminf_le (fun n => ENNReal.measurable_ofReal.comp ((hgm.add_const (e n)).log).neg)
  have hlim : liminf (fun n => ∫⁻ x, ENNReal.ofReal (-(Real.log (g x + e n))) ∂μ) atTop
      ≤ ENNReal.ofReal (C - L) := by
    rw [liminf_eq_iSup_iInf_of_nat]
    refine iSup_le fun n => ?_
    refine le_trans (iInf_le (fun i => ⨅ (_ : i ≥ n),
      ∫⁻ x, ENNReal.ofReal (-(Real.log (g x + e i))) ∂μ) n) ?_
    refine le_trans (iInf_le (fun _ : n ≥ n =>
      ∫⁻ x, ENNReal.ofReal (-(Real.log (g x + e n))) ∂μ) le_rfl) ?_
    exact key n
  have hneg : ∫⁻ x, ENNReal.ofReal (-(Real.log (g x))) ∂μ ≤ ENNReal.ofReal (C - L) :=
    le_trans (lintegral_mono hpt) (le_trans hFatou hlim)
  -- upper bound on the integral of the positive part of `log g`.
  have hlog_le_C : ∀ x, Real.log (g x) ≤ C := by
    intro x
    rcases eq_or_lt_of_le (hg0 x) with h0 | hpos
    · rw [← h0, Real.log_zero]; exact hC
    · exact le_trans (Real.log_le_log hpos (by linarith)) (hgC x)
  have hposb : ∫⁻ x, ENNReal.ofReal (Real.log (g x)) ∂μ ≤ ENNReal.ofReal C := by
    calc ∫⁻ x, ENNReal.ofReal (Real.log (g x)) ∂μ ≤ ∫⁻ x, ENNReal.ofReal C ∂μ :=
          lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hlog_le_C x))
      _ = ENNReal.ofReal C := by rw [lintegral_const, measure_univ, mul_one]
  -- both one-sided parts are finite, hence `log g` is integrable.
  refine ⟨hgm.log.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hm1 : Measurable (fun x => ENNReal.ofReal (Real.log (g x))) :=
    ENNReal.measurable_ofReal.comp hgm.log
  have hle : ∀ x, ‖Real.log (g x)‖ₑ ≤
      ENNReal.ofReal (Real.log (g x)) + ENNReal.ofReal (-(Real.log (g x))) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs]
    by_cases hx : 0 ≤ Real.log (g x)
    · rw [abs_of_nonneg hx]; exact le_add_of_nonneg_right zero_le
    · rw [abs_of_neg (lt_of_not_ge hx)]; exact le_add_of_nonneg_left zero_le
  calc ∫⁻ x, ‖Real.log (g x)‖ₑ ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal (Real.log (g x)) + ENNReal.ofReal (-(Real.log (g x)))) ∂μ :=
        lintegral_mono hle
    _ = ∫⁻ x, ENNReal.ofReal (Real.log (g x)) ∂μ
        + ∫⁻ x, ENNReal.ofReal (-(Real.log (g x))) ∂μ := lintegral_add_left hm1 _
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal (C - L) := add_le_add hposb hneg
    _ < ∞ := by rw [ENNReal.add_lt_top]; exact ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

end Work.Holonomy3
