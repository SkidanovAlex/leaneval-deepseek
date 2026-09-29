import Mathlib
import Submission.Work.ANum.ACertD
import Submission.Work.Haupt.haupt_facts

/-! # The logarithmic derivative of the Hauptmodul `h`

`h(q) = -256 q ∏'_{n} (1 + q^{n+1})^{24}` on the unit disc.  Since the product converges
locally uniformly there, its logarithmic derivative is the sum of the logarithmic derivatives
of the factors, and each factor contributes `24 (n+1) q^n / (1 + q^{n+1})`. -/

open scoped BigOperators

namespace Work.ANum

open Work.Haupt (hfactor hdev hprod hauptH_eq hfactor_ne_zero hprod_ne_zero
  differentiableOn_hprod hasProdLocallyUniformlyOn_hfactor)

lemma hfactor_eq (n : ℕ) (z : ℂ) : hfactor n z = (1 + z ^ (n + 1)) ^ 24 := by
  simp only [hfactor, hdev]
  ring

lemma hfactor_fun (n : ℕ) : hfactor n = fun z : ℂ => (1 + z ^ (n + 1)) ^ 24 :=
  funext (hfactor_eq n)

lemma one_add_pow_ne_zero (n : ℕ) (q : ℂ) (hq : ‖q‖ < 1) : (1 + q ^ (n + 1)) ≠ 0 := by
  have h := hfactor_ne_zero q hq n
  rw [hfactor_eq] at h
  exact fun h0 => h (by rw [h0]; norm_num)

lemma norm_one_add_pow_ge (n : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    1 - ‖q‖ ≤ ‖1 + q ^ (n + 1)‖ := by
  have h1 : ‖q ^ (n + 1)‖ ≤ ‖q‖ := by
    rw [norm_pow]
    calc ‖q‖ ^ (n + 1) = ‖q‖ ^ n * ‖q‖ := by rw [pow_succ]
      _ ≤ 1 * ‖q‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hq.le) (norm_nonneg _)
      _ = ‖q‖ := one_mul _
  have h3 := norm_add_le (1 + q ^ (n + 1)) (-(q ^ (n + 1)))
  rw [show (1 + q ^ (n + 1)) + -(q ^ (n + 1)) = 1 by ring, norm_one, norm_neg] at h3
  linarith

lemma logDeriv_hfactor (n : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    logDeriv (hfactor n) q = 24 * ((n : ℂ) + 1) * q ^ n / (1 + q ^ (n + 1)) := by
  have hne := one_add_pow_ne_zero n q hq
  rw [hfactor_fun n]
  have hp : HasDerivAt (fun z : ℂ => z ^ (n + 1)) (((n : ℂ) + 1) * q ^ n) q := by
    simpa [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using hasDerivAt_pow (n + 1) q
  have hderiv : HasDerivAt (fun z : ℂ => (1 + z ^ (n + 1)) ^ 24)
      (24 * (1 + q ^ (n + 1)) ^ 23 * (((n : ℂ) + 1) * q ^ n)) q :=
    (hp.const_add 1).pow 24
  rw [logDeriv_apply, hderiv.deriv]
  field_simp

lemma summable_logDeriv_hfactor (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => logDeriv (hfactor n) q) := by
  have hr : ‖(‖q‖ : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hq
  have hgeom : Summable (fun n : ℕ => ((n : ℝ) + 1) * ‖q‖ ^ n) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 1 * ‖q‖ ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 hr
    have h2 : Summable (fun n : ℕ => ‖q‖ ^ n) := summable_geometric_of_norm_lt_one hr
    refine (h1.add h2).congr (fun n => ?_)
    ring
  have hbound : Summable (fun n : ℕ => 24 * ((n : ℝ) + 1) * ‖q‖ ^ n / (1 - ‖q‖)) := by
    have h3 : Summable (fun n : ℕ => 24 * (((n : ℝ) + 1) * ‖q‖ ^ n) / (1 - ‖q‖)) :=
      (hgeom.mul_left 24).div_const (1 - ‖q‖)
    exact h3.congr (fun n => by ring)
  refine Summable.of_norm_bounded hbound (fun n => ?_)
  have hge := norm_one_add_pow_ge n q hq
  have hnum : ‖(24 : ℂ) * ((n : ℂ) + 1) * q ^ n‖ ≤ 24 * ((n : ℝ) + 1) * ‖q‖ ^ n := by
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖(24 : ℂ)‖ = 24 := by norm_num
    rw [h1]
    have h2 : ‖((n : ℂ) + 1)‖ ≤ (n : ℝ) + 1 := by
      calc ‖((n : ℂ) + 1)‖ ≤ ‖(n : ℂ)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = (n : ℝ) + 1 := by rw [Complex.norm_natCast]; norm_num
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h2 (by norm_num)) (by positivity)
  calc ‖logDeriv (hfactor n) q‖
      = ‖(24 : ℂ) * ((n : ℂ) + 1) * q ^ n / (1 + q ^ (n + 1))‖ := by
        rw [logDeriv_hfactor n q hq]
    _ = ‖(24 : ℂ) * ((n : ℂ) + 1) * q ^ n‖ / ‖1 + q ^ (n + 1)‖ := by rw [norm_div]
    _ ≤ 24 * ((n : ℝ) + 1) * ‖q‖ ^ n / ‖1 + q ^ (n + 1)‖ :=
        div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ 24 * ((n : ℝ) + 1) * ‖q‖ ^ n / (1 - ‖q‖) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hge

lemma differentiableOn_hfactor (n : ℕ) :
    DifferentiableOn ℂ (hfactor n) (Metric.ball (0 : ℂ) 1) := by
  rw [hfactor_fun n]
  fun_prop

/-- The logarithmic derivative of the Hauptmodul function
`hauptH q = -256 q ∏'_{n≥1} (1 + qⁿ)^24` on the unit disc: differentiating the infinite product
termwise gives `h'/h = 1/q + 24 ∑_{n≥1} (n+1) qⁿ/(1+q^{n+1})`. -/
theorem hauptH_logDeriv (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    deriv Submission.CDTPlan.hauptH q / Submission.CDTPlan.hauptH q =
      1 / q + 24 * ∑' n : ℕ, ((n : ℂ) + 1) * q ^ n / (1 + q ^ (n + 1)) := by
  have hmem : q ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact hq
  have hdiff_hprod : DifferentiableAt ℂ hprod q :=
    differentiableOn_hprod.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
  have hdiff_c : DifferentiableAt ℂ (fun z : ℂ => (-256 : ℂ) * z) q :=
    ((hasDerivAt_id q).const_mul (-256 : ℂ)).differentiableAt
  have hprod_log : logDeriv hprod q = ∑' n : ℕ, logDeriv (hfactor n) q := by
    have hmain := logDeriv_tprod_eq_tsum (s := Metric.ball (0 : ℂ) 1) Metric.isOpen_ball hmem
      (f := hfactor) (fun n => hfactor_ne_zero q hq n)
      (fun n => differentiableOn_hfactor n) (summable_logDeriv_hfactor q hq)
      hasProdLocallyUniformlyOn_hfactor.multipliableLocallyUniformlyOn
      (hprod_ne_zero q hq)
    rw [show hprod = fun x : ℂ => ∏' i : ℕ, hfactor i x from rfl]
    exact hmain
  have hc_log : logDeriv (fun z : ℂ => (-256 : ℂ) * z) q = 1 / q := by
    rw [logDeriv_apply]
    have hd : deriv (fun z : ℂ => (-256 : ℂ) * z) q = -256 := by
      simp
    rw [hd]
    field_simp
  have hmain_log : logDeriv Submission.CDTPlan.hauptH q = 1 / q + logDeriv hprod q := by
    rw [show Submission.CDTPlan.hauptH = fun z : ℂ => (-256 : ℂ) * z * hprod z from
      funext (fun z => hauptH_eq z)]
    rw [logDeriv_fun_mul q (mul_ne_zero (by norm_num) hq0) (hprod_ne_zero q hq) hdiff_c hdiff_hprod,
      hc_log]
  rw [← logDeriv_apply, hmain_log, hprod_log]
  congr 1
  rw [tsum_congr (fun n => logDeriv_hfactor n q hq), ← tsum_mul_left]
  exact tsum_congr (fun n => by ring)

end Work.ANum
