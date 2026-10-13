import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux.MismatchBad

/-! ### Implementation note

The limit `∫_{(0,r)} ‖ψ'‖ → 0` as `r → 0⁺` is obtained here from the absolute continuity of the
integral of an integrable function (`MeasureTheory.Integrable.tendsto_setIntegral_nhds_zero`)
applied to the indicator of `Ioi 0`, the measure of `Ioc 0 r` being `r`; this replaces the
mention of `Antitone.tendsto_setIntegral` in the docstring below.  The divergence of `z ↦ c/z`
near `0⁺` is used in the concrete form `intervalIntegrable_inv_iff`. -/

/-- `z ↦ c/z` (`c > 0`) is not integrable on `(0,r)`: after multiplying by `c⁻¹` this is the
non-integrability of `z ↦ z⁻¹` on the interval `0..r`, which follows from
`intervalIntegrable_inv_iff` because `0` belongs to `[[0, r]]`. -/
private lemma not_integrableOn_Ioo_const_mul_inv {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    ¬ IntegrableOn (fun z : ℝ => c * z⁻¹) (Set.Ioo (0 : ℝ) r) := by
  intro h
  have hInt : IntervalIntegrable (fun z : ℝ => c * z⁻¹) volume 0 r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le).2 h
  have h2 := IntervalIntegrable.const_mul hInt c⁻¹
  have h2' : IntervalIntegrable (fun z : ℝ => z⁻¹) volume 0 r :=
    h2.congr_ae (Filter.Eventually.of_forall fun z => by
      simp only [inv_mul_cancel_left₀ (ne_of_gt hc)])
  rw [intervalIntegrable_inv_iff] at h2'
  rcases h2' with h2' | h2'
  · exact absurd h2' (ne_of_lt hr)
  · exact h2' (by rw [Set.uIcc_of_le hr.le]; exact ⟨le_rfl, hr.le⟩)

/-- Boundary vanishing at `0⁺` for the weighted `z`-integration by parts: if `ψ` is
differentiable on `(0,∞)` with integrable derivative `ψ'` and `|ψ z| ≤ C·z·G(z)²` on `z ≥ 0`
with `C > 0` and `G² ∈ L¹(0,∞)`, then `ψ z → 0` as `z → 0⁺`.

Route: identical to the `atTop` case, with `R → ∞` replaced by `r → 0⁺`:
`hderiv`+`hint` give `|ψ z - ψ z₀| ≤ ∫_{min}^{max}|ψ'|` (FTC,
`intervalIntegral.integral_eq_sub_of_hasDerivAt`), and `∫_{(0,r)}|ψ'| → 0` as `r → 0⁺`
(`Antitone.tendsto_setIntegral` with `s n = Ioo 0 (1/(n+1))`).  Assume for contradiction
that `¬(ψ → 0)`; then for every `r > 0` there is `z₀ ∈ (0,r)` with `|ψ z₀| ≥ ε`; with `r` so
small that `∫_{(0,r)}|ψ'| < ε/2` the oscillation bound gives `|ψ z| ≥ ε/2` for all
`z ∈ (0,r)`, hence `G(z)² ≥ (ε/(2C))/z` on `(0,r)`, contradicting `hG` since `z ↦ c/z`
is not integrable near `0⁺` (via
`not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter` with `l = 𝓝[>] 0`,
`f = Real.log`, `k = Ioo 0 r` — cf. `Work.FTS.H2.not_integrableOn_Ici_of_le_inv_nearZero`
in `Submission/Work/FTS/H2/ZibpLimit.lean`). -/
theorem zibp_lim_nearZero {ψ ψ' G : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt ψ (ψ' z) z)
    (hint : MeasureTheory.IntegrableOn ψ' (Set.Ioi (0 : ℝ)))
    (hbd : ∀ z, 0 ≤ z → |ψ z| ≤ C * (z * (G z) ^ 2))
    (hG : MeasureTheory.IntegrableOn (fun z => (G z) ^ 2) (Set.Ioi (0 : ℝ))) :
    Filter.Tendsto ψ (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0) := by
  -- `A r = ∫_{(0,r)} ‖ψ'‖` tends to `0` as `r → 0⁺`.
  have hA : Filter.Tendsto (fun r : ℝ => ∫ x in (0 : ℝ)..r, |ψ' x|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hInt : MeasureTheory.Integrable (fun x => |ψ' x|)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
      simpa only [Real.norm_eq_abs] using hint.norm
    have hInd : MeasureTheory.Integrable
        ((Set.Ioi (0 : ℝ)).indicator (fun x => |ψ' x|)) MeasureTheory.volume :=
      (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).2 hInt
    have hμ : Filter.Tendsto (fun r : ℝ => MeasureTheory.volume (Set.Ioc (0 : ℝ) r))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h1 : ∀ r : ℝ, MeasureTheory.volume (Set.Ioc (0 : ℝ) r) = ENNReal.ofReal r := by
        intro r; rw [Real.volume_Ioc, sub_zero]
      simp_rw [h1]
      simpa using ENNReal.tendsto_ofReal
        ((tendsto_id : Filter.Tendsto (id : ℝ → ℝ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))).mono_right nhdsWithin_le_nhds)
    have h1 := hInd.tendsto_setIntegral_nhds_zero hμ
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [intervalIntegral.integral_of_le hr.le]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x hx => by
      rw [Set.indicator_of_mem (s := Set.Ioi (0 : ℝ)) hx.1])
  by_contra hcon
  rw [Metric.tendsto_nhds] at hcon
  push Not at hcon
  obtain ⟨ε, hε, hfreq⟩ := hcon
  simp only [Real.dist_eq, sub_zero] at hfreq
  -- a small `r` with `A r < ε/2`
  obtain ⟨δ, _hδ, hδsub⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.1
    (hA.eventually (Metric.ball_mem_nhds (0 : ℝ) (by linarith : (0 : ℝ) < ε / 2)))
  set r : ℝ := δ / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hrδ : r < δ := by rw [hrdef]; linarith
  have hAr : (∫ x in (0 : ℝ)..r, |ψ' x|) < ε / 2 := by
    have h := hδsub ⟨hrpos, hrδ⟩
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at h
    linarith [le_abs_self (∫ x in (0 : ℝ)..r, |ψ' x|)]
  -- a point `z₀ ∈ (0,r)` at which `ψ` is large
  have hmem : Set.Ioo (0 : ℝ) r ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    (nhdsGT_basis (0 : ℝ)).mem_iff.2 ⟨r, hrpos, subset_rfl⟩
  obtain ⟨z₀, hz₀big, hz₀mem⟩ := (hfreq.and_eventually hmem).exists
  have hIntAbs : IntegrableOn (fun x => |ψ' x|) (Set.Ioi (0 : ℝ)) := by
    simpa only [Real.norm_eq_abs, IntegrableOn] using hint.norm
  have hfi : IntervalIntegrable (fun x => |ψ' x|) volume 0 r :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hrpos.le).2
      (hIntAbs.mono_set (fun x hx => hx.1))
  -- oscillation bound: `|ψ b - ψ a| ≤ A r` for `0 < a ≤ b < r`
  have hosc : ∀ a b : ℝ, 0 < a → a ≤ b → b < r →
      |ψ b - ψ a| ≤ ∫ x in (0 : ℝ)..r, |ψ' x| := by
    intro a b ha hab hbr
    have hcont : ContinuousOn ψ (Set.Icc a b) := fun x hx =>
      (hderiv x (Set.mem_Ioi.2 (lt_of_lt_of_le ha hx.1))).continuousAt.continuousWithinAt
    have hderiv' : ∀ x ∈ Set.Ioo a b, HasDerivAt ψ (ψ' x) x := fun x hx =>
      hderiv x (Set.mem_Ioi.2 (lt_trans ha hx.1))
    have hint' : IntervalIntegrable ψ' volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
        (hint.mono_set (fun x hx => Set.mem_Ioi.2 (lt_trans ha hx.1)))
    have hFTC : ∫ x in a..b, ψ' x = ψ b - ψ a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv' hint'
    calc |ψ b - ψ a| = |∫ x in a..b, ψ' x| := by rw [hFTC]
      _ ≤ ∫ x in a..b, |ψ' x| := intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ x in (0 : ℝ)..r, |ψ' x| :=
          intervalIntegral.integral_mono_interval ha.le hab hbr.le
            (ae_of_all _ fun x => abs_nonneg _) hfi
  -- consequently `|ψ| ≥ ε/2` on `(0,r)`
  have hkey : ∀ z, 0 < z → z < r → ε / 2 ≤ |ψ z| := by
    intro z hz hzr
    have hdiff : |ψ z - ψ z₀| ≤ ∫ x in (0 : ℝ)..r, |ψ' x| := by
      rcases le_total z z₀ with h | h
      · rw [abs_sub_comm]
        exact hosc z z₀ hz h hz₀mem.2
      · exact hosc z₀ z hz₀mem.1 h hzr
    have h1 : |ψ z₀| ≤ |ψ z| + |ψ z - ψ z₀| := by
      calc |ψ z₀| = |ψ z + (ψ z₀ - ψ z)| := by congr 1; ring
        _ ≤ |ψ z| + |ψ z₀ - ψ z| := abs_add_le _ _
        _ = |ψ z| + |ψ z - ψ z₀| := by rw [abs_sub_comm]
    linarith [hAr, hdiff, hz₀big, h1]
  -- hence `G z² ≥ (ε/(2C))/z` on `(0,r)`, contradicting the integrability of `G²`
  have hle : ∀ z ∈ Set.Ioo (0 : ℝ) r, ε / (2 * C) * z⁻¹ ≤ G z ^ 2 := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have h1 : ε / 2 ≤ C * (z * (G z) ^ 2) := le_trans (hkey z hz0 hz.2) (hbd z hz0.le)
    have h2 : ε ≤ ((2 * C) * z) * (G z) ^ 2 := by nlinarith [h1]
    have h3 : ε / ((2 * C) * z) ≤ (G z) ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [h2]
    rwa [← div_eq_mul_inv, div_div]
  refine (not_integrableOn_Ioo_const_mul_inv (c := ε / (2 * C)) (r := r)
    (by positivity) hrpos) ?_
  have hGint : IntegrableOn (fun z => (G z) ^ 2) (Set.Ioo (0 : ℝ) r) :=
    hG.mono_set (fun x hx => hx.1)
  refine hGint.mono' ?_ ?_
  · exact (measurable_const.mul measurable_inv).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have h := hle z hz
    have hz0 : 0 ≤ ε / (2 * C) * z⁻¹ := mul_nonneg (by positivity) (inv_nonneg.2 hz.1.le)
    rw [Real.norm_eq_abs, abs_of_nonneg hz0]
    exact h

end Work.FTS.H2.Transport3Aux.MismatchBad
