import Mathlib
import Submission.Work.CPull.defs
import Submission.Work.Pure.pure_facts
import Submission.Work.Pure.b4_eq_prod
import Submission.Work.CPull.B2_coeff_bound
import Submission.Work.CPull.B4_coeff_bound
import Submission.Work.CPull.B4_coeff_rec
import Submission.Work.CPull.tsum_ode_of_rec

/-!
# The analytic facts about `evp B₄` on the unit disc

`Submission.CDTPlan.B₄` is the pure function
`B₄ = 4 Σ_{n≥0} y^{n+1}/16ⁿ Σ_k C(2k,k)C(2n-2k,n-k)/((2k-1)(2n-2k+1)²)` of
Calegari--Dimitrov--Tang (arXiv:2408.15403, eq. `defB`).  This module proves the three
analytic facts about its evaluation series `Work.CPull.evp B₄ y = Σ cₙ yⁿ` on the unit disc:

* it is complex differentiable on `Metric.ball 0 1`;
* the defining series sums to it there;
* it satisfies the first-order equation of the paper's eq. `diffformulas`,
  `y(4-y)·(evp B₄)' = (2-y)·evp B₄ + (4-y)·evp B₂ - 2y(4-y)`.

The coefficient bound `‖cₙ‖ ≤ 16·(1/2)ⁿ` (`Work.CPull.B4_coeff_bound`, obtained from the
product formula `B₄ = 4·y·Fser·fG`) gives radius of convergence `≥ 2`, hence analyticity on the
unit disc; differentiability and the termwise-derivative formula come from
`Complex.differentiableOn_tsum_of_summable_norm` / `Complex.hasSum_deriv_of_summable_norm`.
The differential equation is then read off coefficient by coefficient
(`Work.CPull.B4_coeff_rec`, which extracts the recurrence from the formal identity
`Work.Pure.b4_rel`) and reassembled at the level of the series by
`Work.CPull.tsum_ode_of_rec`.
-/

namespace Work.CPull

set_option maxHeartbeats 1000000 in
/-- A power series whose `n`-th coefficient is bounded by `C·(1/2)ⁿ` defines a function that is
differentiable on the unit disc, whose series sums to it there, and whose derivative is given by
the termwise-derivative series.  (`(1/2)ⁿ` decay means radius of convergence `≥ 2 > 1`.) -/
theorem evp_analytic_half (c : ℕ → ℂ) (C : ℝ) (hC : 0 < C)
    (hb : ∀ n : ℕ, ‖c n‖ ≤ C * (1 / 2 : ℝ) ^ n) :
    (∀ y : ℂ, ‖y‖ < 1 → Summable fun n : ℕ => c n * y ^ n) ∧
    (∀ y : ℂ, ‖y‖ < 1 → Summable fun n : ℕ => (n : ℂ) * c n * y ^ n) ∧
    (∀ y : ℂ, ‖y‖ < 1 → Summable fun n : ℕ => ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n) ∧
    DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ, c n * z ^ n) (Metric.ball 0 1) ∧
    (∀ y : ℂ, ‖y‖ < 1 → deriv (fun z : ℂ => ∑' n : ℕ, c n * z ^ n) y
      = ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n) := by
  have hgeom : Summable fun n : ℕ => C * (1 / 2 : ℝ) ^ n :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  have hhalf : ∀ t : ℝ, 0 ≤ t → t < 1 → Summable fun n : ℕ => (n : ℝ) * t ^ n := by
    intro t ht0 ht1
    exact (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := t)
      (by rw [Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1)).summable
  have hp : ∀ (t : ℝ) (n : ℕ), (1/2:ℝ) ^ n * t ^ n = (t / 2) ^ n := by
    intro t n
    rw [← mul_pow]; congr 1; ring
  have hkey : ∀ y : ℂ, ‖y‖ < 1 → Summable fun n : ℕ => c n * y ^ n := by
    intro y hy
    have hg : Summable fun n : ℕ => C * (‖y‖ / 2) ^ n :=
      (summable_geometric_of_lt_one (by positivity) (by linarith)).mul_left C
    refine hg.of_norm_bounded fun n => ?_
    rw [norm_mul, norm_pow]
    calc ‖c n‖ * ‖y‖ ^ n ≤ (C * (1 / 2 : ℝ) ^ n) * ‖y‖ ^ n :=
          mul_le_mul_of_nonneg_right (hb n) (by positivity)
      _ = C * ((1 / 2 : ℝ) ^ n * ‖y‖ ^ n) := by ring
      _ = C * (‖y‖ / 2) ^ n := by rw [hp]
  have hkey2 : ∀ y : ℂ, ‖y‖ < 1 → Summable fun n : ℕ => (n : ℂ) * c n * y ^ n := by
    intro y hy
    have hg : Summable fun n : ℕ => C * ((n : ℝ) * (‖y‖ / 2) ^ n) :=
      (hhalf (‖y‖/2) (by positivity) (by linarith)).mul_left C
    refine hg.of_norm_bounded fun n => ?_
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    calc (n : ℝ) * ‖c n‖ * ‖y‖ ^ n ≤ (n : ℝ) * (C * (1 / 2 : ℝ) ^ n) * ‖y‖ ^ n := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hb n) (Nat.cast_nonneg n)) (by positivity)
      _ = C * ((n : ℝ) * ((1 / 2 : ℝ) ^ n * ‖y‖ ^ n)) := by ring
      _ = C * ((n : ℝ) * (‖y‖ / 2) ^ n) := by rw [hp]
  have hkey3 : ∀ y : ℂ, ‖y‖ < 1 →
      Summable fun n : ℕ => ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n := by
    intro y hy
    have ht : (‖y‖ / 2 : ℝ) < 1 := by linarith
    have ht0 : (0:ℝ) ≤ ‖y‖ / 2 := by positivity
    have h4 : Summable fun n : ℕ => ((n : ℝ) + 1) * (‖y‖ / 2) ^ n :=
      ((hhalf (‖y‖/2) ht0 ht).add
        (summable_geometric_of_lt_one ht0 ht)).congr (fun n => by ring)
    have hg : Summable fun n : ℕ => C * ((1/2 : ℝ) * (((n : ℝ) + 1) * (‖y‖ / 2) ^ n)) :=
      (h4.mul_left (1/2 : ℝ)).mul_left C
    refine hg.of_norm_bounded fun n => ?_
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    calc ((n : ℝ) + 1) * ‖c (n + 1)‖ * ‖y‖ ^ n
        ≤ ((n : ℝ) + 1) * (C * (1 / 2 : ℝ) ^ (n + 1)) * ‖y‖ ^ n := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hb (n+1)) (by positivity)) (by positivity)
      _ = C * ((1/2 : ℝ) * (((n : ℝ) + 1) * (‖y‖ / 2) ^ n)) := by
          rw [pow_succ]; ring
  have hf : ∀ i : ℕ, DifferentiableOn ℂ (fun w : ℂ => c i * w ^ i) (Metric.ball (0:ℂ) 1) :=
    fun i => ((differentiable_const (c i)).mul (differentiable_id.pow i)).differentiableOn
  have hF_le : ∀ (i : ℕ) (w : ℂ),
      w ∈ Metric.ball (0:ℂ) 1 → ‖c i * w ^ i‖ ≤ C * (1 / 2 : ℝ) ^ i := by
    intro i w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    rw [norm_mul, norm_pow]
    calc ‖c i‖ * ‖w‖ ^ i ≤ (C * (1 / 2 : ℝ) ^ i) * 1 :=
          mul_le_mul (hb i) (pow_le_one₀ (norm_nonneg _) (le_of_lt hw)) (by positivity)
            (by positivity)
      _ = C * (1 / 2 : ℝ) ^ i := by ring
  refine ⟨hkey, hkey2, hkey3, ?_, ?_⟩
  · exact Complex.differentiableOn_tsum_of_summable_norm hgeom hf Metric.isOpen_ball hF_le
  · intro y hy
    have hU : y ∈ Metric.ball (0:ℂ) 1 := by rw [Metric.mem_ball, dist_zero_right]; exact hy
    have hHS := Complex.hasSum_deriv_of_summable_norm hgeom hf Metric.isOpen_ball hF_le hU
    have hdeq : ∀ i : ℕ, deriv (fun w : ℂ => c i * w ^ i) y = (i : ℂ) * c i * y ^ (i - 1) := by
      intro i
      rw [deriv_const_mul _ (by fun_prop), (hasDerivAt_pow i y).deriv]
      ring
    have hHS' : HasSum (fun i : ℕ => (i : ℂ) * c i * y ^ (i - 1))
        (deriv (fun w : ℂ => ∑' i : ℕ, c i * w ^ i) y) :=
      hHS.congr_fun fun i => (hdeq i).symm
    have hshift :=
      (hasSum_nat_add_iff' (f := fun i : ℕ => (i : ℂ) * c i * y ^ (i - 1)) 1).mpr hHS'
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero] at hshift
    have hfun : (fun n : ℕ => (fun i : ℕ => (i : ℂ) * c i * y ^ (i - 1)) (n + 1))
        = fun n : ℕ => ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n := by
      funext n; simp
    rw [hfun] at hshift
    exact hshift.tsum_eq.symm

/-- Casting the branches of a rational `if` to `ℂ`. -/
private lemma ratCast_ite {p : Prop} [Decidable p] (a b : ℚ) :
    (((if p then a else b : ℚ)) : ℂ) = (if p then (a : ℂ) else (b : ℂ)) := by
  by_cases h : p <;> simp [h]

set_option maxHeartbeats 1000000 in
theorem evp_B4_facts :
    DifferentiableOn ℂ (fun y : ℂ => Work.CPull.evp Submission.CDTPlan.B4 y) (Metric.ball 0 1) ∧
    (∀ y ∈ Metric.ball (0:ℂ) 1, HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n Submission.CDTPlan.B4 : ℚ) : ℂ) * y ^ n)
      (Work.CPull.evp Submission.CDTPlan.B4 y)) ∧
    (∀ y ∈ Metric.ball (0:ℂ) 1,
      y * (4 - y) * deriv (fun w : ℂ => Work.CPull.evp Submission.CDTPlan.B4 w) y
        = (2 - y) * Work.CPull.evp Submission.CDTPlan.B4 y
          + (4 - y) * Work.CPull.evp Submission.CDTPlan.B2 y - 2 * y * (4 - y)) := by
  have hb4 : ∀ n : ℕ, ‖(((PowerSeries.coeff n Submission.CDTPlan.B4 : ℚ) : ℂ))‖
      ≤ 16 * (1/2 : ℝ)^n := B4_coeff_bound
  have hb2 : ∀ n : ℕ, ‖(((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ))‖
      ≤ 16 * (1/2 : ℝ)^n := by
    intro n
    have h := B2_coeff_bound n
    have hpow : (1/4:ℝ)^n ≤ (1/2)^n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    have h2 : (0:ℝ) ≤ (1/2)^n := by positivity
    linarith
  obtain ⟨hS4, hS4', hS4'', hdiff4, hderiv4⟩ := evp_analytic_half _ 16 (by norm_num) hb4
  obtain ⟨hS2, hS2', hS2'', hdiff2, hderiv2⟩ := evp_analytic_half _ 16 (by norm_num) hb2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Work.CPull.evp] using hdiff4
  · intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    simpa only [Work.CPull.evp] using (hS4 y hy).hasSum
  · intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    have hrec : ∀ n : ℕ,
        4 * ((n : ℂ) * ((PowerSeries.coeff n Submission.CDTPlan.B4 : ℚ) : ℂ))
          - (((n - 1 : ℕ) : ℂ) * ((PowerSeries.coeff (n - 1) Submission.CDTPlan.B4 : ℚ) : ℂ))
        = 2 * ((PowerSeries.coeff n Submission.CDTPlan.B4 : ℚ) : ℂ)
          - (if n = 0 then 0 else ((PowerSeries.coeff (n - 1) Submission.CDTPlan.B4 : ℚ) : ℂ))
          + (4 * ((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ)
             - (if n = 0 then 0
                else ((PowerSeries.coeff (n - 1) Submission.CDTPlan.B2 : ℚ) : ℂ)))
          - (if n = 1 then 8 else 0) + (if n = 2 then 2 else 0) := by
      intro n
      have h := congrArg (fun z : ℚ => (z : ℂ)) (B4_coeff_rec n)
      push_cast at h
      simp only [ratCast_ite] at h
      simpa using h
    have hmain := tsum_ode_of_rec
      (fun n : ℕ => ((PowerSeries.coeff n Submission.CDTPlan.B4 : ℚ) : ℂ))
      (fun n : ℕ => ((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ)) y hrec
      (hS4 y hy) (hS4' y hy) (hS4'' y hy) (hS2 y hy) (hderiv4 y hy)
    simpa only [Work.CPull.evp] using hmain

end Work.CPull
