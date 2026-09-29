import Mathlib
import Submission.Work.Holonomy3.mv_lex_general_defs
import Submission.Work.Holonomy3.mv_lex_null_zero
import Submission.Work.Holonomy3.le_integral_log_of_smoothed
import Submission.Work.Holonomy3.mv_lex_trunc_tendsto_integral
import Submission.Work.Holonomy3.mv_lex_measurable_norm_G
import Submission.Work.Holonomy3.mv_lex_trunc_smoothed_ge

namespace Work.Holonomy3

open scoped BigOperators
open MeasureTheory

noncomputable section

/-! ### The per-truncation smoothed step -/

private theorem mv_lex_step_N {d : ℕ} (g : MvPowerSeries (Fin d) ℂ)
    (hpoly : ∀ (c : (Fin d →₀ ℕ) →₀ ℂ) (D : ℕ) (n : Fin d →₀ ℕ),
      (∀ m ∈ c.support, D ≤ m.degree) → n ∈ c.support → n.degree = D →
      (∀ m ∈ c.support, m.degree = D → toLex n ≤ toLex m) →
      Real.log ‖c n‖ ≤ ∫ s : Fin d → ℝ, Real.log ‖pevalF c (tor s)‖ ∂(torMeasure d))
    (hInt : ∀ (c : (Fin d →₀ ℕ) →₀ ℂ), c ≠ 0 →
      MeasureTheory.Integrable (fun s : Fin d → ℝ => Real.log ‖pevalF c (tor s)‖) (torMeasure d))
    {n : Fin d →₀ ℕ} (hn : MvPowerSeries.coeff n g ≠ 0)
    (hmin : ∀ m : Fin d →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m g = 0)
    (hlex : ∀ m : Fin d →₀ ℕ, m.degree = n.degree → MvPowerSeries.coeff m g ≠ 0 →
      m = n ∨ ∃ j : Fin d, (∀ i : Fin d, i < j → m i = n i) ∧ n j < m j)
    (N : ℕ) (hN : n.degree ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    Real.log ‖MvPowerSeries.coeff n g‖ ≤
      ∫ t : Fin d → ℝ,
        Real.log (‖pevalF (truncF (fun m => MvPowerSeries.coeff m g) N) (tor t)‖ + δ)
        ∂(torMeasure d) := by
  have hdeg : ∀ m ∈ (truncF (fun m => MvPowerSeries.coeff m g) N).support,
      n.degree ≤ m.degree := by
    intro m hm
    have hdegN : m.degree ≤ N := mem_degLe.mp (support_truncF_subset _ N hm)
    by_contra hcon
    rw [not_le] at hcon
    rw [Finsupp.mem_support_iff, truncF_apply, if_pos hdegN, hmin m hcon] at hm
    exact hm rfl
  have hmem : n ∈ (truncF (fun m => MvPowerSeries.coeff m g) N).support := by
    rw [Finsupp.mem_support_iff, truncF_apply, if_pos hN]
    exact hn
  have hlex' : ∀ m ∈ (truncF (fun m => MvPowerSeries.coeff m g) N).support,
      m.degree = n.degree → toLex n ≤ toLex m := by
    intro m hm hdegm
    have ham : MvPowerSeries.coeff m g ≠ 0 := by
      have h2 := Finsupp.mem_support_iff.mp hm
      rwa [truncF_apply, if_pos (mem_degLe.mp (support_truncF_subset _ N hm))] at h2
    rcases hlex m hdegm ham with heq | ⟨j, hj, hlt⟩
    · rw [heq]
    · refine le_of_lt ?_
      rw [Finsupp.Lex.lt_iff]
      refine ⟨j, fun i hi => ?_, ?_⟩
      · simpa [eq_comm] using hj i hi
      · simpa using hlt
  have hcN : truncF (fun m => MvPowerSeries.coeff m g) N ≠ 0 := truncF_ne_zero_of hn hN
  have hpolyN := hpoly (truncF (fun m => MvPowerSeries.coeff m g) N) n.degree n hdeg hmem rfl hlex'
  have hcn : truncF (fun m => MvPowerSeries.coeff m g) N n = MvPowerSeries.coeff n g := by
    rw [truncF_apply, if_pos hN]
  rw [hcn] at hpolyN
  have hint : Integrable (fun t : Fin d → ℝ =>
      Real.log ‖pevalF (truncF (fun m => MvPowerSeries.coeff m g) N) (tor t)‖) (torMeasure d) :=
    hInt _ hcN
  have hintδ : Integrable (fun t : Fin d → ℝ =>
      Real.log (‖pevalF (truncF (fun m => MvPowerSeries.coeff m g) N) (tor t)‖ + δ))
      (torMeasure d) := by
    have hcont : Continuous fun t : Fin d → ℝ =>
        Real.log (‖pevalF (truncF (fun m => MvPowerSeries.coeff m g) N) (tor t)‖ + δ) :=
      Continuous.log ((continuous_pevalF_tor_mv_lex_null_zero _).norm.add_const δ) (fun t => ne_of_gt (by positivity))
    refine Integrable.of_bound hcont.aestronglyMeasurable
      (max |Real.log δ| |Real.log ((∑ m ∈ degLe d N, ‖MvPowerSeries.coeff m g‖) + δ)|) ?_
    refine Filter.Eventually.of_forall fun t => ?_
    have hle : ‖pevalF (truncF (fun m => MvPowerSeries.coeff m g) N) (tor t)‖
        ≤ ∑ m ∈ degLe d N, ‖MvPowerSeries.coeff m g‖ := norm_pevalF_truncF_le _ N t
    have hn0 : (0:ℝ) ≤ ‖pevalF (truncF (fun m => MvPowerSeries.coeff m g) N) (tor t)‖ := norm_nonneg _
    have h1 : Real.log δ ≤ Real.log (‖pevalF (truncF (fun m => MvPowerSeries.coeff m g) N) (tor t)‖ + δ) :=
      Real.log_le_log hδ (by linarith)
    have h2 : Real.log (‖pevalF (truncF (fun m => MvPowerSeries.coeff m g) N) (tor t)‖ + δ)
        ≤ Real.log ((∑ m ∈ degLe d N, ‖MvPowerSeries.coeff m g‖) + δ) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h3 := neg_abs_le (Real.log δ)
      have h4 := le_max_left |Real.log δ| |Real.log ((∑ m ∈ degLe d N, ‖MvPowerSeries.coeff m g‖) + δ)|
      linarith
    · have h3 := le_abs_self (Real.log ((∑ m ∈ degLe d N, ‖MvPowerSeries.coeff m g‖) + δ))
      have h4 := le_max_right |Real.log δ| |Real.log ((∑ m ∈ degLe d N, ‖MvPowerSeries.coeff m g‖) + δ)|
      linarith
  have hsm := mv_lex_trunc_smoothed_ge (fun m => MvPowerSeries.coeff m g) N hδ hcN hint hintδ
  linarith

theorem mv_lex_general_case {d : ℕ} (g : MvPowerSeries (Fin d) ℂ) (G : (Fin d → ℂ) → ℂ) {ρ : ℝ} (hρ : 1 < ρ)
    (hG : ∀ z : Fin d → ℂ, (∀ j, ‖z j‖ ≤ ρ) →
      HasSum (fun m : Fin d →₀ ℕ => MvPowerSeries.coeff m g * ∏ j, (z j) ^ (m j)) (G z))
    (hpoly : ∀ (c : (Fin d →₀ ℕ) →₀ ℂ) (D : ℕ) (n : Fin d →₀ ℕ),
      (∀ m ∈ c.support, D ≤ m.degree) → n ∈ c.support → n.degree = D →
      (∀ m ∈ c.support, m.degree = D → toLex n ≤ toLex m) →
      Real.log ‖c n‖ ≤ ∫ s : Fin d → ℝ, Real.log ‖pevalF c (tor s)‖ ∂(torMeasure d))
    (hInt : ∀ (c : (Fin d →₀ ℕ) →₀ ℂ), c ≠ 0 →
      MeasureTheory.Integrable (fun s : Fin d → ℝ => Real.log ‖pevalF c (tor s)‖) (torMeasure d))
    {n : Fin d →₀ ℕ} (hn : MvPowerSeries.coeff n g ≠ 0)
    (hmin : ∀ m : Fin d →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m g = 0)
    (hlex : ∀ m : Fin d →₀ ℕ, m.degree = n.degree → MvPowerSeries.coeff m g ≠ 0 →
      m = n ∨ ∃ j : Fin d, (∀ i : Fin d, i < j → m i = n i) ∧ n j < m j) :
    Real.log ‖MvPowerSeries.coeff n g‖ ≤
      ∫ t : Fin d → ℝ, Real.log ‖G (tor t)‖ ∂(torMeasure d) := by
  have key : ∀ δ : ℝ, 0 < δ → Real.log ‖MvPowerSeries.coeff n g‖ ≤
      ∫ t : Fin d → ℝ, Real.log (‖G (tor t)‖ + δ) ∂(torMeasure d) := by
    intro δ hδ
    have hlim := mv_lex_trunc_tendsto_integral g G hρ hG hδ
    refine ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨n.degree, fun N hN => ?_⟩)
    exact mv_lex_step_N g hpoly hInt hn hmin hlex N hN hδ
  obtain ⟨hmeas, hbound⟩ := mv_lex_measurable_norm_G g G hρ hG
  set B : ℝ := ∑' m : Fin d →₀ ℕ, ‖MvPowerSeries.coeff m g‖ with hB
  have hCg : ∀ t : Fin d → ℝ, Real.log (‖G (tor t)‖ + 1) ≤ max 0 (Real.log (B + 1)) := by
    intro t
    have h1 : ‖G (tor t)‖ ≤ B := by rw [hB]; exact hbound t
    exact le_trans (Real.log_le_log (by positivity) (by linarith)) (le_max_right _ _)
  have hε0 : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hε1 : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := by
    intro k
    have hge : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    calc 1 / ((k : ℝ) + 1) ≤ 1 / 1 := one_div_le_one_div_of_le (by norm_num) hge
      _ = 1 := by norm_num
  have hεt : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hεm : Antitone (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
    refine antitone_nat_of_succ_le fun k => ?_
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
    exact one_div_le_one_div_of_le h1 h2
  have hc : ∀ k : ℕ, Real.log ‖MvPowerSeries.coeff n g‖ ≤
      ∫ t : Fin d → ℝ, Real.log (‖G (tor t)‖ + 1 / ((k : ℝ) + 1)) ∂(torMeasure d) :=
    fun k => key _ (by positivity)
  have hcm : Antitone (fun _ : ℕ => Real.log ‖MvPowerSeries.coeff n g‖) := antitone_const
  have hct : Filter.Tendsto (fun _ : ℕ => Real.log ‖MvPowerSeries.coeff n g‖) Filter.atTop
      (nhds (Real.log ‖MvPowerSeries.coeff n g‖)) := tendsto_const_nhds
  exact le_integral_log_of_smoothed (μ := torMeasure d) (g := fun t : Fin d → ℝ => ‖G (tor t)‖)
    hmeas (fun t => norm_nonneg _) (le_max_left _ _) hCg hε0 hε1 hεt hεm hc hcm hct

end

end Work.Holonomy3
