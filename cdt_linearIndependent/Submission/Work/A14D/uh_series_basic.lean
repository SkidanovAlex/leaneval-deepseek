import Mathlib
import Submission.Work.A14D.uh_defs
import Submission.Work.A14D.uhCoeff_bound
import Submission.Work.A14D.powSeries_summable
import Submission.Work.A14D.powSeries_deriv

/-!
# A14D — basic analytic properties of the series `G0 w = Σ aₙ wⁿ`

`G0` is the coefficient series of the holomorphic solution `uh` of the Zagier operator at `x = 1`
(see `Submission.Work.A14D.uh_defs`).  Here we collect the elementary analytic facts on the disc
`‖w‖ < 8/9`:

* `Σ aₙ wⁿ = G0 w`, and `G0`, `deriv G0` are holomorphic there;
* the derivative series of `Σ aₙ wⁿ` and of `Σ (n+1)a_{n+1} wⁿ`;
* summability of the three norm series.

The radius `8/9` comes from the geometric growth bound `a_{n+1} ≤ (9/8) a_n` of
`Submission.Work.A14D.uhCoeff_bound`; the analytic input (termwise differentiation of a power
series under a polynomial-geometric coefficient bound) is `Submission.Work.A14D.powSeries_deriv`.
-/

open Complex Metric Filter
open scoped Topology BigOperators

noncomputable section
namespace Work.A14D

private lemma uhCoeff_nonneg (n : ℕ) : (0 : ℝ) ≤ (uhCoeff n : ℝ) := by
  exact_mod_cast le_of_lt (uhCoeff_bound.1 n)

private lemma uhCoeff_geom_Q (n : ℕ) : uhCoeff n ≤ (9 / 8 : ℚ) ^ n := by
  induction n with
  | zero => norm_num [uhCoeff]
  | succ n ih =>
    calc uhCoeff (n + 1) ≤ 9 / 8 * uhCoeff n := (uhCoeff_bound.2.1) n
      _ ≤ 9 / 8 * (9 / 8 : ℚ) ^ n := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (9 / 8 : ℚ) ^ (n + 1) := by ring

private lemma uhCoeff_geom (n : ℕ) : (uhCoeff n : ℝ) ≤ (9 / 8 : ℝ) ^ n := by
  have := uhCoeff_geom_Q n
  have h : ((uhCoeff n : ℚ) : ℝ) ≤ (((9 / 8 : ℚ) ^ n : ℚ) : ℝ) := by exact_mod_cast this
  rw [Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofNat] at h
  norm_num at h
  exact h

private lemma norm_uhCoeff (n : ℕ) : ‖(uhCoeff n : ℂ)‖ = (uhCoeff n : ℝ) := by
  rw [Complex.norm_ratCast, abs_of_nonneg (uhCoeff_nonneg n)]

/-- The coefficient sequence `c n = aₙ`, as a complex sequence. -/
private def c (n : ℕ) : ℂ := (uhCoeff n : ℂ)
/-- The coefficient sequence `(n+1)a_{n+1}` of the derivative series. -/
private def d (n : ℕ) : ℂ := ((n : ℂ) + 1) * (uhCoeff (n + 1) : ℂ)
/-- The coefficient sequence `(n+1)(n+2)a_{n+2}` of the second derivative series. -/
private def e (n : ℕ) : ℂ := ((n : ℂ) + 1) * ((n : ℂ) + 2) * (uhCoeff (n + 2) : ℂ)

private lemma norm_ofRealC (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h2 : ‖(r:ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq_abs]; ring
  nlinarith [norm_nonneg (r:ℂ), abs_nonneg r]

private lemma norm_succ (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring]
  rw [norm_ofRealC, abs_of_nonneg (by positivity)]

private lemma norm_succ2 (n : ℕ) : ‖((n : ℂ) + 2)‖ = (n : ℝ) + 2 := by
  rw [show ((n : ℂ) + 2) = (((n : ℝ) + 2 : ℝ) : ℂ) by push_cast; ring]
  rw [norm_ofRealC, abs_of_nonneg (by positivity)]

private lemma c_bound (n : ℕ) :
    ‖c n‖ ≤ (1 : ℝ) * (9 / 8 : ℝ) ^ n * ((n : ℝ) + 1) ^ 0 := by
  show ‖(uhCoeff n : ℂ)‖ ≤ _
  rw [norm_uhCoeff]
  simpa using uhCoeff_geom n

private lemma d_bound (n : ℕ) :
    ‖d n‖ ≤ (9 / 8 : ℝ) * (9 / 8 : ℝ) ^ n * ((n : ℝ) + 1) ^ 1 := by
  have h : ‖d n‖ = ((n : ℝ) + 1) * (uhCoeff (n + 1) : ℝ) := by
    show ‖((n : ℂ) + 1) * (uhCoeff (n + 1) : ℂ)‖ = _
    rw [norm_mul, norm_succ n, norm_uhCoeff]
  rw [h, pow_one]
  calc ((n : ℝ) + 1) * (uhCoeff (n + 1) : ℝ)
      ≤ ((n : ℝ) + 1) * (9 / 8 : ℝ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (uhCoeff_geom (n + 1)) (by positivity)
    _ = (9 / 8 : ℝ) * (9 / 8 : ℝ) ^ n * ((n : ℝ) + 1) := by ring

private lemma e_bound (n : ℕ) :
    ‖e n‖ ≤ 2 * (9 / 8 : ℝ) ^ 2 * (9 / 8 : ℝ) ^ n * ((n : ℝ) + 1) ^ 2 := by
  have h : ‖e n‖ = ((n : ℝ) + 1) * ((n : ℝ) + 2) * (uhCoeff (n + 2) : ℝ) := by
    show ‖((n : ℂ) + 1) * ((n : ℂ) + 2) * (uhCoeff (n + 2) : ℂ)‖ = _
    rw [norm_mul, norm_mul, norm_succ n, norm_succ2 n, norm_uhCoeff]
  rw [h]
  have hn : (0:ℝ) ≤ (n:ℝ)+1 := by positivity
  calc ((n : ℝ) + 1) * ((n : ℝ) + 2) * (uhCoeff (n + 2) : ℝ)
      ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) * (9 / 8 : ℝ) ^ (n + 2) := by
        apply mul_le_mul_of_nonneg_left (uhCoeff_geom (n + 2))
        positivity
    _ ≤ 2 * (9/8:ℝ)^2 * (9/8:ℝ)^n * ((n:ℝ)+1)^2 := by
        rw [show (9/8:ℝ)^(n+2) = (9/8:ℝ)^2 * (9/8:ℝ)^n by ring]
        have h2 : ((n:ℝ)+1) * ((n:ℝ)+2) ≤ 2 * ((n:ℝ)+1)^2 := by nlinarith [hn]
        calc ((n:ℝ)+1) * ((n:ℝ)+2) * ((9/8:ℝ)^2 * (9/8:ℝ)^n)
            = (((n:ℝ)+1) * ((n:ℝ)+2)) * ((9/8:ℝ)^2 * (9/8:ℝ)^n) := by ring
          _ ≤ (2 * ((n:ℝ)+1)^2) * ((9/8:ℝ)^2 * (9/8:ℝ)^n) :=
              mul_le_mul_of_nonneg_right h2 (by positivity)
          _ = 2 * (9/8:ℝ)^2 * (9/8:ℝ)^n * ((n:ℝ)+1)^2 := by ring

private lemma hw_of (w : ℂ) (hw : ‖w‖ < 8/9) : (9/8 : ℝ) * ‖w‖ < 1 := by
  have h : (9/8 : ℝ) * (8/9) = 1 := by norm_num
  calc (9/8) * ‖w‖ < (9/8) * (8/9) := by linarith
    _ = 1 := h

private lemma summable_c (w : ℂ) (hw : ‖w‖ < 8/9) :
    Summable (fun n : ℕ => ‖c n * w ^ n‖) :=
  powSeries_summable c (by norm_num) (by norm_num) c_bound (hw_of w hw)

private lemma summable_d (w : ℂ) (hw : ‖w‖ < 8/9) :
    Summable (fun n : ℕ => ‖d n * w ^ n‖) :=
  powSeries_summable d (by norm_num) (by norm_num) d_bound (hw_of w hw)

private lemma summable_e (w : ℂ) (hw : ‖w‖ < 8/9) :
    Summable (fun n : ℕ => ‖e n * w ^ n‖) :=
  powSeries_summable e (by positivity) (by norm_num) e_bound (hw_of w hw)

private lemma hasDerivAt_G0 (w : ℂ) (hw : ‖w‖ < 8/9) :
    HasDerivAt G0 (∑' n : ℕ, d n * w ^ n) w := by
  have h := powSeries_deriv c (by norm_num) (by norm_num : (0:ℝ) < 9/8) c_bound w (hw_of w hw)
  have h2 : (∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * w ^ n) = ∑' n : ℕ, d n * w ^ n := by
    apply tsum_congr; intro n; simp [c, d]
  rw [h2] at h
  exact h

private lemma derivG0_eq (w : ℂ) (hw : ‖w‖ < 8/9) : deriv G0 w = ∑' n : ℕ, d n * w ^ n :=
  (hasDerivAt_G0 w hw).deriv

private lemma hasDerivAt_derivG0 (w : ℂ) (hw : ‖w‖ < 8/9) :
    HasDerivAt (deriv G0) (∑' n : ℕ, e n * w ^ n) w := by
  have h := powSeries_deriv d (by norm_num) (by norm_num : (0:ℝ) < 9/8) d_bound w (hw_of w hw)
  have h2 : (∑' n : ℕ, ((n : ℂ) + 1) * d (n + 1) * w ^ n) = ∑' n : ℕ, e n * w ^ n := by
    apply tsum_congr; intro n
    simp only [d, e]
    push_cast
    ring
  rw [h2] at h
  have hev : deriv G0 =ᶠ[𝓝 w] (fun z : ℂ => ∑' n : ℕ, d n * z ^ n) := by
    have hb : w ∈ Metric.ball (0:ℂ) (8/9) := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hw
    filter_upwards [Metric.isOpen_ball.mem_nhds hb] with z hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
    exact derivG0_eq z hz
  exact h.congr_of_eventuallyEq hev

/-- Basic analytic properties of the series `G0 w = Σₙ aₙ wⁿ` on the disc `‖w‖ < 8/9`. -/
theorem uh_series_basic : (∀ w : ℂ, ‖w‖ < 8 / 9 → HasSum (fun n : ℕ => (uhCoeff n : ℂ) * w ^ n) (G0 w)) ∧ DifferentiableOn ℂ G0 (Metric.ball 0 (8 / 9)) ∧ DifferentiableOn ℂ (deriv G0) (Metric.ball 0 (8 / 9)) ∧ (∀ w : ℂ, ‖w‖ < 8 / 9 → HasSum (fun n : ℕ => ((n : ℂ) + 1) * (uhCoeff (n + 1) : ℂ) * w ^ n) (deriv G0 w)) ∧ (∀ w : ℂ, ‖w‖ < 8 / 9 → HasSum (fun n : ℕ => ((n : ℂ) + 1) * ((n : ℂ) + 2) * (uhCoeff (n + 2) : ℂ) * w ^ n) (deriv (deriv G0) w)) ∧ (∀ w : ℂ, ‖w‖ < 8 / 9 → Summable (fun n : ℕ => ‖(uhCoeff n : ℂ) * w ^ n‖)) ∧ (∀ w : ℂ, ‖w‖ < 8 / 9 → Summable (fun n : ℕ => ‖((n : ℂ) + 1) * (uhCoeff (n + 1) : ℂ) * w ^ n‖)) ∧ (∀ w : ℂ, ‖w‖ < 8 / 9 → Summable (fun n : ℕ => ‖((n : ℂ) + 1) * ((n : ℂ) + 2) * (uhCoeff (n + 2) : ℂ) * w ^ n‖)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    show HasSum (fun n : ℕ => c n * w ^ n) (∑' n : ℕ, c n * w ^ n)
    exact (summable_c w hw).of_norm.hasSum
  · intro w hw
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hw
    exact (hasDerivAt_G0 w hw).differentiableAt.differentiableWithinAt
  · intro w hw
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hw
    exact (hasDerivAt_derivG0 w hw).differentiableAt.differentiableWithinAt
  · intro w hw
    have hs := (summable_d w hw).of_norm.hasSum
    rw [(hasDerivAt_G0 w hw).deriv]
    simpa only [d] using hs
  · intro w hw
    have hs := (summable_e w hw).of_norm.hasSum
    rw [(hasDerivAt_derivG0 w hw).deriv]
    simpa only [e] using hs
  · intro w hw
    show Summable (fun n : ℕ => ‖c n * w ^ n‖)
    exact summable_c w hw
  · intro w hw
    show Summable (fun n : ℕ => ‖d n * w ^ n‖)
    exact summable_d w hw
  · intro w hw
    show Summable (fun n : ℕ => ‖e n * w ^ n‖)
    exact summable_e w hw

end Work.A14D
