import Mathlib
import Submission.Work.Holonomy3.mv_lex_general_defs

/-!
# Convergence of the torus integrals of the degree-truncated evaluations

For a multivariable power series `g` over `ℂ` whose (unordered) evaluation series converges on the
closed polydisc of radius `ρ > 1` — with sum `G` — the integrals over the torus of
`t ↦ log (‖pevalF (truncF a N) (tor t)‖ + δ)` converge, as the degree bound `N → ∞`, to the integral
of `t ↦ log (‖G (tor t)‖ + δ)`.

The proof is the dominated convergence theorem.  The dominating function is the constant
`max |log δ| |log (S + δ)|`, where `S = ∑' m, ‖a m‖ < ∞` is the (finite) total mass of the
coefficient norms: absolute convergence on the polydisc of radius `ρ > 1` gives summability of the
coefficient norms (`Summable` at the boundary point `(ρ, …, ρ)` together with `Summable.norm` and
`ρ ^ m.degree ≥ 1`), the truncated evaluations are partial sums of the full series and hence bounded
by `S` on the torus, and the integrands converge pointwise because the degree truncations
`degLe d N` exhaust the index set `Fin d →₀ ℕ` and the evaluation at the torus point has sum
`G (tor t)`.
-/

namespace Work.Holonomy3

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- The smoothed logarithm of the absolute value of a polynomial on the torus is continuous. -/
lemma continuous_log_norm_pevalF_tor {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun s : Fin d → ℝ => Real.log (‖pevalF c (tor s)‖ + ε)) := by
  have htor : Continuous (fun s : Fin d → ℝ => tor s) := by
    apply continuous_pi
    intro j
    unfold tor
    fun_prop
  have hpev : Continuous (fun s : Fin d → ℝ => pevalF c (tor s)) := by
    unfold pevalF
    refine continuous_finsetSum _ (fun m _ => ?_)
    refine Continuous.mul continuous_const ?_
    refine continuous_finsetProd _ (fun j _ => ?_)
    exact (((continuous_apply j).comp htor).pow _)
  refine Continuous.log (hpev.norm.add_const ε) (fun s => ?_)
  exact ne_of_gt (by have h := norm_nonneg (pevalF c (tor s)); linarith)

/-- **Auxiliary general form** (arbitrary coefficient family `a`).

If the unordered series `∑_m a m · ∏_j z_j^{m_j}` converges on the closed polydisc of radius
`ρ > 1` with sum `G`, then the integrals over the torus of the smoothed logarithms of the
degree-truncated partial sums converge to the smoothed logarithm of `G`. -/
theorem mv_lex_trunc_tendsto_integral_aux {d : ℕ} (a : (Fin d →₀ ℕ) → ℂ)
    (G : (Fin d → ℂ) → ℂ) {ρ : ℝ} (hρ : 1 < ρ)
    (hG : ∀ z : Fin d → ℂ, (∀ j, ‖z j‖ ≤ ρ) →
      HasSum (fun m : Fin d →₀ ℕ => a m * ∏ j, (z j) ^ (m j)) (G z))
    {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun N : ℕ => ∫ t : Fin d → ℝ,
        Real.log (‖pevalF (truncF a N) (tor t)‖ + δ) ∂(torMeasure d))
      Filter.atTop
      (nhds (∫ t : Fin d → ℝ, Real.log (‖G (tor t)‖ + δ) ∂(torMeasure d))) := by
  -- Absolute convergence of the coefficient family on the polydisc of radius `ρ > 1`.
  have hS : Summable (fun m : Fin d →₀ ℕ => ‖a m‖) := by
    have hρpos : 0 < ρ := lt_trans zero_lt_one hρ
    have hsumρ : Summable (fun m : Fin d →₀ ℕ => a m * (ρ : ℂ) ^ m.degree) := by
      have hz : ∀ j : Fin d, ‖((ρ : ℝ) : ℂ)‖ ≤ ρ := fun _ =>
        le_of_eq (Complex.norm_of_nonneg hρpos.le)
      have h := (hG (fun _ : Fin d => ((ρ : ℝ) : ℂ)) hz).summable
      refine h.congr (fun m => ?_)
      rw [prod_pow_degree]
    have hnormρ : Summable (fun m : Fin d →₀ ℕ => ‖a m‖ * ρ ^ m.degree) := by
      have h := hsumρ.norm
      refine h.congr (fun m => ?_)
      rw [norm_mul, norm_pow, Complex.norm_of_nonneg hρpos.le]
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hnormρ
    exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hρ.le)
  have hSnn : (0 : ℝ) ≤ ∑' m : Fin d →₀ ℕ, ‖a m‖ := tsum_nonneg (fun m => norm_nonneg _)
  -- Dominated convergence with the constant bound `max |log δ| |log (S + δ)|`.
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ : Fin d → ℝ => max |Real.log δ| |Real.log ((∑' m : Fin d →₀ ℕ, ‖a m‖) + δ)|)
    ?_ ?_ ?_ ?_
  · intro N
    exact (continuous_log_norm_pevalF_tor (truncF a N) hδ).aestronglyMeasurable
  · exact MeasureTheory.integrable_const _
  · intro N
    refine Filter.Eventually.of_forall (fun t => ?_)
    have hb : ‖pevalF (truncF a N) (tor t)‖ ≤ ∑' m : Fin d →₀ ℕ, ‖a m‖ :=
      le_trans (norm_pevalF_truncF_le a N t)
        (Summable.sum_le_tsum (degLe d N) (fun i _ => norm_nonneg _) hS)
    have hlo : Real.log δ ≤ Real.log (‖pevalF (truncF a N) (tor t)‖ + δ) :=
      Real.log_le_log hδ (by have h0 := norm_nonneg (pevalF (truncF a N) (tor t)); linarith)
    have hhi : Real.log (‖pevalF (truncF a N) (tor t)‖ + δ)
        ≤ Real.log ((∑' m : Fin d →₀ ℕ, ‖a m‖) + δ) :=
      Real.log_le_log
        (by have h0 := norm_nonneg (pevalF (truncF a N) (tor t)); linarith)
        (by linarith)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h1 := neg_abs_le (Real.log δ)
      have h2 := le_max_left |Real.log δ| |Real.log ((∑' m : Fin d →₀ ℕ, ‖a m‖) + δ)|
      linarith
    · have h1 := le_abs_self (Real.log ((∑' m : Fin d →₀ ℕ, ‖a m‖) + δ))
      have h2 := le_max_right |Real.log δ| |Real.log ((∑' m : Fin d →₀ ℕ, ‖a m‖) + δ)|
      linarith
  · -- Pointwise convergence of the integrands.
    refine Filter.Eventually.of_forall (fun t => ?_)
    have hconv : Filter.Tendsto (fun N : ℕ => pevalF (truncF a N) (tor t)) Filter.atTop
        (nhds (G (tor t))) := by
      have hz : ∀ j : Fin d, ‖tor t j‖ ≤ ρ := fun j => by rw [norm_tor_apply]; exact hρ.le
      have h2 := (hG (tor t) hz).comp (tendsto_degLe d)
      simpa [Function.comp_def, pevalF_truncF_tor] using h2
    have h1 : Filter.Tendsto (fun N : ℕ => ‖pevalF (truncF a N) (tor t)‖) Filter.atTop
        (nhds (‖G (tor t)‖)) := hconv.norm
    have h2 := h1.add_const δ
    have hx : ‖G (tor t)‖ + δ ≠ 0 := by
      have h0 := norm_nonneg (G (tor t)); linarith
    exact (Real.continuousAt_log hx).tendsto.comp h2

theorem mv_lex_trunc_tendsto_integral {d : ℕ} (g : MvPowerSeries (Fin d) ℂ) (G : (Fin d → ℂ) → ℂ)
    {ρ : ℝ} (hρ : 1 < ρ)
    (hG : ∀ z : Fin d → ℂ, (∀ j, ‖z j‖ ≤ ρ) →
      HasSum (fun m : Fin d →₀ ℕ => MvPowerSeries.coeff m g * ∏ j, (z j) ^ (m j)) (G z))
    {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun N : ℕ => ∫ t : Fin d → ℝ,
        Real.log (‖pevalF (truncF (fun m => MvPowerSeries.coeff m g) N) (tor t)‖ + δ)
        ∂(torMeasure d))
      Filter.atTop
      (nhds (∫ t : Fin d → ℝ, Real.log (‖G (tor t)‖ + δ) ∂(torMeasure d))) :=
  mv_lex_trunc_tendsto_integral_aux (fun m => MvPowerSeries.coeff m g) G hρ hG hδ

end

end Work.Holonomy3
