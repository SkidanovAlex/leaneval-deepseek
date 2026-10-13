import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory

-- Hint for the prover: `Integrable (f^2)` does NOT give `AEStronglyMeasurable f`, so `MemLp` /
-- `integral_mul_norm_le_Lp_mul_Lq` (Cauchy-Schwarz) is NOT directly applicable. Use instead the
-- pointwise AM-GM bound `|a n x * b x| <= l/2 * (a n x)^2 + (1/(2*l)) * (b x)^2` for `l > 0`,
-- which needs no measurability: `Integrable.const_mul`/`Integrable.add` give integrability of the
-- right-hand side, `integral_mono_of_nonneg` then bounds `∫ |a n * b|` by it, and
-- `abs_integral_le_integral_abs` is unconditional. Pick `l = (∫ b^2)/eps + 1`, use `hconv` with
-- tolerance `eps/(2*l)` and `Metric.tendsto_atTop`; `integral_nonneg` gives `0 <= ∫ b^2`.

/-- Pointwise AM–GM: for `l > 0`, `|a * b| ≤ l/2 * a² + (1/(2 l)) * b²`.  No measurability is
involved. -/
private lemma abs_mul_le_half_sq_add {l a b : ℝ} (hl : 0 < l) :
    |a * b| ≤ l / 2 * a ^ 2 + 1 / (2 * l) * b ^ 2 := by
  rw [abs_mul]
  set A := |a| with hA
  set B := |b| with hB
  have hAa : A ^ 2 = a ^ 2 := by rw [hA]; exact sq_abs a
  have hBb : B ^ 2 = b ^ 2 := by rw [hB]; exact sq_abs b
  have key : 2 * l * A * B ≤ l ^ 2 * a ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (l * A - B)]
  calc |a| * |b| = (1 / (2 * l)) * (2 * l * A * B) := by
        rw [← hA, ← hB]; field_simp
    _ ≤ (1 / (2 * l)) * (l ^ 2 * a ^ 2 + b ^ 2) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = l / 2 * a ^ 2 + 1 / (2 * l) * b ^ 2 := by field_simp

theorem tendsto_integral_mul_of_tendsto_integral_sq_zero {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {a : ℕ → α → ℝ} {b : α → ℝ}
    (ha : ∀ n, MeasureTheory.Integrable (fun x : α => (a n x) ^ 2) μ)
    (hb : MeasureTheory.Integrable (fun x : α => (b x) ^ 2) μ)
    (hconv : Filter.Tendsto (fun n : ℕ => ∫ x, (a n x) ^ 2 ∂μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => ∫ x, a n x * b x ∂μ) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at hconv
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- `B2 := ∫ b²` is nonnegative.
  set B2 : ℝ := ∫ x, (b x) ^ 2 ∂μ with hB2
  have hB2_nonneg : 0 ≤ B2 := by
    rw [hB2]; exact integral_nonneg (fun x => sq_nonneg _)
  -- The AM–GM parameter: `l = B2/ε + 1 ≥ 1 > 0`, chosen so that `B2/(2 l) ≤ ε/2`.
  set l : ℝ := B2 / ε + 1 with hl
  have hl_pos : 0 < l := by rw [hl]; positivity
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hεl_pos : 0 < ε / l := div_pos hε hl_pos
  rcases hconv (ε / l) hεl_pos with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  -- Eventually `∫ (a n)² < ε / l`.
  have hAn : ∫ x, (a n x) ^ 2 ∂μ < ε / l := by
    have h1 := hN n hn
    have h2 : |∫ x, (a n x) ^ 2 ∂μ| = ∫ x, (a n x) ^ 2 ∂μ :=
      abs_of_nonneg (integral_nonneg (fun x => sq_nonneg _))
    rw [Real.dist_eq, sub_zero, h2] at h1
    exact h1
  -- the pointwise majorant is integrable
  have hφ_int : MeasureTheory.Integrable (fun x => l/2 * (a n x)^2 + 1/(2*l) * (b x)^2) μ :=
    ((ha n).const_mul (l/2)).add (hb.const_mul (1/(2*l)))
  -- `‖∫ a n * b‖` is bounded by the integral of the majorant
  have hbound : ‖∫ x, a n x * b x ∂μ‖ ≤
      ∫ x, (l/2 * (a n x)^2 + 1/(2*l) * (b x)^2) ∂μ := by
    have h2 : ‖∫ x, a n x * b x ∂μ‖ ≤ ∫ x, |a n x * b x| ∂μ := by
      simpa using norm_integral_le_integral_norm (fun x => a n x * b x)
    have h3 : ∫ x, |a n x * b x| ∂μ ≤
        ∫ x, (l/2 * (a n x)^2 + 1/(2*l) * (b x)^2) ∂μ := by
      apply integral_mono_of_nonneg
      · filter_upwards with x; exact abs_nonneg _
      · exact hφ_int
      · filter_upwards with x
        exact abs_mul_le_half_sq_add hl_pos
    linarith
  have hφ_eval : ∫ x, (l/2 * (a n x)^2 + 1/(2*l) * (b x)^2) ∂μ
      = l/2 * (∫ x, (a n x)^2 ∂μ) + 1/(2*l) * B2 := by
    rw [integral_add ((ha n).const_mul _) (hb.const_mul _), integral_const_mul,
      integral_const_mul, hB2]
  have hB2_le : (1/(2*l)) * B2 ≤ ε/2 := by
    have hB2e : ε * (B2 / ε) = B2 := by field_simp
    have hεl : ε * l = B2 + ε := by rw [hl, mul_add, hB2e, mul_one]
    have h1 : B2 ≤ ε * l := by rw [hεl]; linarith
    have h2 : (1/(2*l)) * B2 ≤ (1/(2*l)) * (ε*l) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (1/(2*l)) * (ε*l) = ε/2 := by field_simp
    linarith
  have hAn_le : l/2 * (∫ x, (a n x)^2 ∂μ) < ε/2 := by
    have h2 : l/2 * (∫ x, (a n x)^2 ∂μ) < l/2 * (ε/l) :=
      mul_lt_mul_of_pos_left hAn (by linarith)
    have h3 : l/2 * (ε/l) = ε/2 := by field_simp
    linarith
  have hfin : ‖∫ x, a n x * b x ∂μ‖ < ε := by
    rw [hφ_eval] at hbound
    linarith
  simpa [Real.dist_eq, Real.norm_eq_abs] using hfin

end Work.FTS.PhiStar.Honesty
