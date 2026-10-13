import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

open MeasureTheory Set Filter

/-- **An `L²(g dμ)`-Cauchy family with an a.e. limit converges in `L²(g dμ)` to it.**  If the
squared differences of `v` form a Cauchy family in `L¹` (two-variable limit) and `v n → u` almost
everywhere, then `∫ (v n - u)² g → 0`: for fixed `n`, Fatou applied to the a.e. convergence
`v m → u` gives `∫ (v n - u)² g ≤ liminf_m ∫ (v n - v m)² g`, and the right-hand side is `< ε`
for `n ≥ N` by Cauchy-ness. -/
theorem tendsto_sq_sub_of_cauchy_of_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {v : ℕ → α → ℝ} {u : α → ℝ} {g : α → ℝ}
    (hgpos : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hint2 : ∀ n m, Integrable (fun x => (v n x - v m x) ^ 2 * g x) μ)
    (hcauchy : Filter.Tendsto (fun nm : ℕ × ℕ =>
        ∫ x, (v nm.1 x - v nm.2 x) ^ 2 * g x ∂μ)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0))
    (hae : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => v n x) Filter.atTop (nhds (u x))) :
    Filter.Tendsto (fun n => ∫ x, (v n x - u x) ^ 2 * g x ∂μ) Filter.atTop (nhds 0) := by
  have hgnn : 0 ≤ᵐ[μ] g := hgpos
  -- Step 1: unfold the two-variable Cauchy hypothesis into a numerical threshold statement.
  have hthr : ∀ ε > 0, ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫ x, (v n x - v m x) ^ 2 * g x ∂μ < ε := by
    intro ε hε
    have hev := hcauchy.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)
    rw [Filter.eventually_prod_iff] at hev
    obtain ⟨pa, hpa, pb, hpb, hprod⟩ := hev
    rw [Filter.eventually_atTop] at hpa hpb
    obtain ⟨N1, hN1⟩ := hpa
    obtain ⟨N2, hN2⟩ := hpb
    refine ⟨max N1 N2, fun n m hn hm => ?_⟩
    have h1 : pa n := hN1 n (le_trans (le_max_left _ _) hn)
    have h2 : pb m := hN2 m (le_trans (le_max_right _ _) hm)
    have h3 := hprod h1 h2
    rw [dist_zero_right, Real.norm_eq_abs, abs_lt] at h3
    exact h3.2
  -- Step 2: for each `ε > 0`, Fatou gives `∫ (v n - u)² g ≤ ε` eventually in `n`.
  have hbound : ∀ ε > 0, ∀ᶠ n in atTop, ∫ x, (v n x - u x) ^ 2 * g x ∂μ ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hthr ε hε
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hnn_n : 0 ≤ᵐ[μ] fun x => (v n x - u x) ^ 2 * g x :=
      hgnn.mono fun x hx => mul_nonneg (sq_nonneg _) hx
    have hae_n : ∀ᵐ x ∂μ, Tendsto (fun m => (v n x - v m x) ^ 2 * g x) atTop
        (nhds ((v n x - u x) ^ 2 * g x)) :=
      hae.mono fun x hx => ((tendsto_const_nhds.sub hx).pow 2).mul_const (g x)
    have hsm_n : AEStronglyMeasurable (fun x => (v n x - u x) ^ 2 * g x) μ :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun m => (hint2 n m).1) hae_n
    have hpair_nn : ∀ m, 0 ≤ᵐ[μ] fun x => (v n x - v m x) ^ 2 * g x :=
      fun m => hgnn.mono fun x hx => mul_nonneg (sq_nonneg _) hx
    have hliminf_eq : ∀ᵐ x ∂μ,
        liminf (fun m => ENNReal.ofReal ((v n x - v m x) ^ 2 * g x)) atTop
          = ENNReal.ofReal ((v n x - u x) ^ 2 * g x) :=
      hae.mono fun x hx =>
        (ENNReal.tendsto_ofReal (((tendsto_const_nhds.sub hx).pow 2).mul_const (g x))).liminf_eq
    have hfat := lintegral_liminf_le' (μ := μ) (u := atTop)
      (f := fun m x => ENNReal.ofReal ((v n x - v m x) ^ 2 * g x))
      (fun m => (hint2 n m).1.aemeasurable.ennreal_ofReal)
    have key : ∫⁻ x, ENNReal.ofReal ((v n x - u x) ^ 2 * g x) ∂μ ≤ ENNReal.ofReal ε := by
      calc ∫⁻ x, ENNReal.ofReal ((v n x - u x) ^ 2 * g x) ∂μ
          = ∫⁻ x, liminf (fun m => ENNReal.ofReal ((v n x - v m x) ^ 2 * g x)) atTop ∂μ :=
            (lintegral_congr_ae hliminf_eq).symm
        _ ≤ liminf (fun m => ∫⁻ x, ENNReal.ofReal ((v n x - v m x) ^ 2 * g x) ∂μ) atTop := hfat
        _ = liminf (fun m => ENNReal.ofReal (∫ x, (v n x - v m x) ^ 2 * g x ∂μ)) atTop := by
            have h1 : (fun m => ∫⁻ x, ENNReal.ofReal ((v n x - v m x) ^ 2 * g x) ∂μ)
                = (fun m => ENNReal.ofReal (∫ x, (v n x - v m x) ^ 2 * g x ∂μ)) := by
              funext m
              exact (ofReal_integral_eq_lintegral_ofReal (hint2 n m) (hpair_nn m)).symm
            rw [h1]
        _ ≤ ENNReal.ofReal ε := by
            refine liminf_le_of_frequently_le' ?_
            exact (Filter.eventually_atTop.2 ⟨N, fun m hm =>
              ENNReal.ofReal_le_ofReal (le_of_lt (hN n m hn hm))⟩).frequently
    have hd_eq : ∫ x, (v n x - u x) ^ 2 * g x ∂μ
        = (∫⁻ x, ENNReal.ofReal ((v n x - u x) ^ 2 * g x) ∂μ).toReal :=
      integral_eq_lintegral_of_nonneg_ae hnn_n hsm_n
    rw [hd_eq]
    calc (∫⁻ x, ENNReal.ofReal ((v n x - u x) ^ 2 * g x) ∂μ).toReal
        ≤ (ENNReal.ofReal ε).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top key
      _ = ε := ENNReal.toReal_ofReal hε.le
  -- Step 3: the `ε`-eventual bound is exactly the limit statement.
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hbound (ε / 2) (by linarith))
  refine ⟨N, fun n hn => ?_⟩
  have hnn_int : 0 ≤ ∫ x, (v n x - u x) ^ 2 * g x ∂μ :=
    integral_nonneg_of_ae (hgnn.mono fun x hx => mul_nonneg (sq_nonneg _) hx)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn_int]
  linarith [hN n hn]

end Work.FTS.PhiStar.Honesty.SlotsLimit
