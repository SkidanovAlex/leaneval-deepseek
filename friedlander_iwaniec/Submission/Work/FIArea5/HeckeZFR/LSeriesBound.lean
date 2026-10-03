/-
# `Submission.Work.FIArea5.HeckeZFR.LSeriesBound`

Elementary bounds for the Hecke `L`-series at fixed `σ`:

* `LSeries_norm_le_of_tau_bound` — for *any* coefficient sequence with `‖f n‖ ≤ 4 τ(n)`,
  `‖LSeries f s‖ ≤ C₀` on `re s ≥ 3/2`, where `C₀ = 4 Σ_n τ(n)n^{-3/2}` is an absolute constant;
* `heckeLSeries_norm_le_re_ge_three_halves` — the specialization to `f = heckeLam chi k`;
* `heckeLSeries_deriv_norm_le` — `‖L'(s,ψ)‖ ≤ 2C₀` on `re s ≥ 2`, by Cauchy's estimate on the
  sphere of radius `1/2` (which stays inside `re ≥ 3/2`);
* `heckeLSeries_logDeriv_norm_le` — `‖L'/L(s,ψ)‖ ≤ 2C₀·C₁` for `re s = 2`, combining the above
  with the half-plane inverse bound `heckeL_inv_halfPlane` evaluated at `σ = 2`, where its
  `C/(σ-1)` is just `C`.

This is the input that turns the functional-equation reflection
`Λ'/Λ(-1+iγ) = - conj (Λ'/Λ(2+iγ))` (`FELogDeriv.logDeriv_FE_at_neg_one`) into a bound at the base
point `s₁ = -1+iγ` of the Hadamard rebasing.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeLStripAux
import Submission.Work.FIArea5.S16Hecke.heckeL_inv_halfPlane
import Submission.Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg
import Submission.Work.FIArea5.HeckeZFR.HeckeNonvanishing

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea5.S16Hecke

open LSeries
open scoped BigOperators

noncomputable section

/-- The absolute majorant constant `4 Σ_n τ(n) n^{-3/2}` of the Hecke `L`-series on `re s ≥ 3/2`. -/
def heckeLMajorant : ℝ :=
  4 * ∑' n : ℕ, ((n.divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ))

lemma heckeLMajorant_pos : 0 < heckeLMajorant := by
  have hnn : ∀ n : ℕ, 0 ≤ ((n.divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    fun n => mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hsumm := summable_card_divisors_mul_rpow_neg (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 : ((1 : ℕ).divisors.card : ℝ) * (((1 : ℕ) : ℝ)) ^ (-(3 / 2 : ℝ))
      ≤ ∑' n : ℕ, ((n.divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    hsumm.le_tsum 1 (fun i _ => hnn i)
  have h2 : ((1 : ℕ).divisors.card : ℝ) * (((1 : ℕ) : ℝ)) ^ (-(3 / 2 : ℝ)) = 1 := by norm_num
  rw [heckeLMajorant]
  linarith [h1, h2.le, h2.ge]

/-- **A general `L`-series bound.**  If `‖f n‖ ≤ 4 τ(n)` for all `n`, then `‖LSeries f s‖ ≤ C₀`
on `re s ≥ 3/2`. -/
theorem LSeries_norm_le_of_tau_bound (f : ℕ → ℂ)
    (hf : ∀ n : ℕ, ‖f n‖ ≤ 4 * ((n.divisors.card : ℕ) : ℝ))
    {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖LSeries f s‖ ≤ heckeLMajorant := by
  have hbd : ∀ n : ℕ, ‖LSeries.term f s n‖
      ≤ 4 * (((n.divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg hn]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hle : ((n : ℝ) ^ s.re)⁻¹ ≤ ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnpos ((3 : ℝ) / 2))
          (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
      rw [div_eq_mul_inv]
      calc ‖f n‖ * ((n : ℝ) ^ s.re)⁻¹
          ≤ 4 * ((n.divisors.card : ℕ) : ℝ) * ((n : ℝ) ^ s.re)⁻¹ :=
            mul_le_mul_of_nonneg_right (hf n) (by positivity)
        _ ≤ 4 * ((n.divisors.card : ℕ) : ℝ) * ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = 4 * (((n.divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
            rw [Real.rpow_neg hnpos.le]; ring
  have hsumm : Summable (fun n : ℕ => LSeries.term f s n) :=
    Summable.of_norm_bounded
      ((summable_card_divisors_mul_rpow_neg (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 4) hbd
  have hnormsum : Summable (fun n : ℕ => ‖LSeries.term f s n‖) := hsumm.norm
  have h1 : ‖LSeries f s‖ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ :=
    norm_tsum_le_tsum_norm (f := fun n : ℕ => LSeries.term f s n) hnormsum
  refine h1.trans ?_
  have hsum2 : Summable (fun n : ℕ =>
      4 * (((n.divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    (summable_card_divisors_mul_rpow_neg (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 4
  have h2 : (∑' n : ℕ, ‖LSeries.term f s n‖)
      ≤ ∑' n : ℕ, 4 * (((n.divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Summable.tsum_le_tsum (fun n => hbd n) hnormsum hsum2
  have h3 : (∑' n : ℕ, 4 * (((n.divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ))))
      = heckeLMajorant := by
    rw [heckeLMajorant, tsum_mul_left]
  linarith [h2, h3.le]

/-- **`‖L(s,ψ)‖ ≤ C₀` on `re s ≥ 3/2`**, uniformly in the character and in `k`. -/
theorem heckeLSeries_norm_le_re_ge_three_halves (chi : GaussianInt → ℂ) (k : ℤ)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖heckeLSeries chi k s‖ ≤ heckeLMajorant := by
  refine LSeries_norm_le_of_tau_bound (heckeLam chi k) (fun n => ?_) hs
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [heckeLam_zero, norm_zero]
    simp
  · exact heckeLam_bound chi k hb h

/-- **`‖L'(s,ψ)‖ ≤ 2 C₀` on `re s ≥ 2`**, by Cauchy's estimate on the sphere of radius `1/2`
(which stays inside `re ≥ 3/2`). -/
theorem heckeLSeries_deriv_norm_le (chi : GaussianInt → ℂ) (k : ℤ)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖deriv (heckeLSeries chi k) s‖ ≤ 2 * heckeLMajorant := by
  have habs : LSeries.abscissaOfAbsConv (heckeLam chi k) < ((3 : ℝ) / 2 : EReal) :=
    lt_of_le_of_lt (heckeLSeries_absc_le_one chi k hb)
      (EReal.coe_lt_coe_iff.mpr (by norm_num : (1 : ℝ) < 3 / 2))
  have hsub : Metric.closedBall s (1 / 2) ⊆ {z : ℂ | ((3 : ℝ) / 2) ≤ z.re} := by
    intro z hz
    show ((3 : ℝ) / 2) ≤ z.re
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h1 : |z.re - s.re| ≤ ‖z - s‖ := by
      simpa using Complex.abs_re_le_norm (z - s)
    have h2 : |z.re - s.re| ≤ 1 / 2 := le_trans h1 hz
    have h3 := abs_le.mp h2
    linarith [h3.1, hs]
  have hset : ∀ z : ℂ, z ∈ Metric.closedBall s (1 / 2) →
      LSeries.abscissaOfAbsConv (heckeLam chi k) < (z.re : EReal) := by
    intro z hz
    exact lt_of_lt_of_le habs (EReal.coe_le_coe_iff.mpr (hsub hz))
  have hbig : DifferentiableOn ℂ (LSeries (heckeLam chi k))
      {z : ℂ | LSeries.abscissaOfAbsConv (heckeLam chi k) < (z.re : EReal)} :=
    fun z hz => LSeries_differentiableOn (heckeLam chi k) z hz
  have hdiffcl : DifferentiableOn ℂ (heckeLSeries chi k) (Metric.closedBall s (1 / 2)) :=
    hbig.mono (fun z hz => hset z hz)
  have hdC : DiffContOnCl ℂ (heckeLSeries chi k) (Metric.ball s (1 / 2)) :=
    ⟨hdiffcl.mono Metric.ball_subset_closedBall,
      hdiffcl.continuousOn.mono
        (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)⟩
  have hsphere : ∀ w ∈ Metric.sphere s (1 / 2), ‖heckeLSeries chi k w‖ ≤ heckeLMajorant := by
    intro w hw
    refine heckeLSeries_norm_le_re_ge_three_halves chi k hb ?_
    have h1 : |w.re - s.re| ≤ ‖w - s‖ := by
      simpa using Complex.abs_re_le_norm (w - s)
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    have h2 : |w.re - s.re| ≤ 1 / 2 := le_trans h1 hw.le
    have h3 := abs_le.mp h2
    linarith [h3.1, hs]
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (R := (1 / 2 : ℝ))
    (by norm_num) hdC hsphere
  have h2 : heckeLMajorant / (1 / 2 : ℝ) = 2 * heckeLMajorant := by ring
  linarith [hcauchy, h2.le]

/-- **`‖L'/L(s,ψ)‖ ≤ 2 C₀ C₁` on `re s = 2`**, combining the derivative bound with the half-plane
inverse bound `heckeL_inv_halfPlane` at `σ = 2`. -/
theorem heckeLSeries_logDeriv_norm_le (chi : GaussianInt → ℂ) (k : ℤ)
    (h1 : chi 1 = 1) (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = 2 →
      ‖deriv (heckeLSeries chi k) s / heckeLSeries chi k s‖ ≤ C := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := heckeL_inv_halfPlane chi k h1 hmul hb
  refine ⟨2 * heckeLMajorant * C₁, by have := heckeLMajorant_pos; positivity, ?_⟩
  intro s hs
  have hs1 : (1 : ℝ) < s.re := by rw [hs]; norm_num
  have hs2 : s.re ≤ 2 := by rw [hs]
  have hLs : heckeLSeries chi k s ≠ 0 :=
    heckeLSeries_ne_zero_of_one_lt_re chi k h1 hmul hb hs1
  rw [norm_div]
  have hd := heckeLSeries_deriv_norm_le chi k hb (by rw [hs])
  have hi := hC₁ s hs1 hs2
  have hspos : 0 < s.re - 1 := by linarith
  have hC₁div : C₁ / (s.re - 1) ≤ C₁ := by
    rw [div_le_iff₀ hspos]; nlinarith [hC₁pos]
  calc ‖deriv (heckeLSeries chi k) s‖ / ‖heckeLSeries chi k s‖
      = ‖deriv (heckeLSeries chi k) s‖ * ‖(heckeLSeries chi k s)⁻¹‖ := by rw [norm_inv]; ring
    _ ≤ (2 * heckeLMajorant) * C₁ := by
        refine mul_le_mul hd ?_ (norm_nonneg _) (by have := heckeLMajorant_pos; positivity)
        exact le_trans hi hC₁div
    _ = 2 * heckeLMajorant * C₁ := by try ring

end

end Work.FIArea5.S16Hecke
