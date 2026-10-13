/-
# `Work.FTS.PhiStar.Psi0Est.qfun_tendsto_endpoints_alt` — `Pfun/sin²θ → 0` at both ends of `Iθ`

`qfun α θ = Pfun α θ / sin²θ = Gzero α θ / (2 cos³θ sin²θ)`, and both limits
`qfun α → 0` (`θ → 0`) and `qfun α → 0` (`θ → π/2`) follow from the two two-sided power
bounds for `G₀`:

* `Gzero_rpow_zero`: `|G₀(θ)| ≤ C|θ|^{2+α/3}` for `|θ| ≤ 1/2`;
* `Gzero_rpow_pi_div_two`: `|G₀(θ)| ≤ C|θ-π/2|^{3+2α/3}` for `|θ-π/2| ≤ 1/2`.

Near `0` the denominators satisfy `2cos³θ ≥ 1/4` and `sin²θ ≥ θ²/4`, so
`|qfun α θ| ≤ 16C|θ|^{α/3} → 0`; near `π/2` one has `2|cos θ|³ ≥ |θ-π/2|³/4` and
`sin²θ ≥ 1/4`, so `|qfun α θ| ≤ 16C|θ-π/2|^{2α/3} → 0`.  Both are two-sided: the estimates
for `G₀` are, and the elementary trigonometric bounds hold for `|θ| ≤ 1/2` resp.
`|θ - π/2| ≤ 1/2` on either side.  The limits are then obtained by squeezing, using
`Real.continuousAt_rpow_const` (the exponent is positive) at the value `0`.

This module re-proves the statement of the requested
`Work.FTS.PhiStar.Psi0Est.qfun_tendsto_endpoints` (whose proof rests on the same two
`Gzero` estimates) under a name that can be imported together with both of them.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.PhiStar.Psi0Est.Defs
import Submission.Work.FTS.PhiStar.Psi0Est.Gzero_rpow_zero
import Submission.Work.FTS.PhiStar.Psi0Est.Gzero_rpow_pi_div_two

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Psi0Est

set_option autoImplicit false

private lemma cos_ge_half {θ : ℝ} (hθ : |θ| ≤ 1 / 2) : (1 / 2 : ℝ) ≤ Real.cos θ := by
  have hθle : θ ≤ 1 / 2 := (abs_le.mp hθ).2
  have h1 : Real.cos (Real.pi / 3) ≤ Real.cos |θ| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (x := |θ|) (y := Real.pi / 3) (abs_nonneg θ)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_three])
  rw [Real.cos_pi_div_three] at h1
  have h4 : Real.cos |θ| = Real.cos θ := by
    rcases le_or_gt 0 θ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, Real.cos_neg]
  rwa [h4] at h1

private lemma abs_sin_ge {θ : ℝ} (hθ : |θ| ≤ 1 / 2) : |θ| / 2 ≤ |Real.sin θ| := by
  have hθle : θ ≤ 1 / 2 := (abs_le.mp hθ).2
  have hθge : -(1 / 2) ≤ θ := (abs_le.mp hθ).1
  have hπ : (2 / Real.pi) * |θ| ≤ Real.sin |θ| :=
    Real.mul_le_sin (abs_nonneg θ) (by linarith [hθ, Real.pi_gt_three])
  have h2 : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < Real.pi)]
    linarith [Real.pi_lt_four]
  have h3 : |θ| / 2 ≤ Real.sin |θ| := by
    calc |θ| / 2 = (1 / 2) * |θ| := by ring
      _ ≤ (2 / Real.pi) * |θ| := mul_le_mul_of_nonneg_right h2 (abs_nonneg θ)
      _ ≤ Real.sin |θ| := hπ
  have h4 : Real.sin |θ| = |Real.sin θ| := by
    rcases le_or_gt 0 θ with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h
        (by linarith [hθle, Real.pi_gt_three]))]
    · rw [abs_of_neg h, Real.sin_neg, abs_of_neg (Real.sin_neg_of_neg_of_neg_pi_lt h
        (by linarith [hθge, Real.pi_gt_three]))]
  rwa [h4] at h3

private lemma sin_ge_half {θ : ℝ} (hθ : |θ - Real.pi / 2| ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ Real.sin θ := by
  have h1 : Real.sin θ = Real.cos (θ - Real.pi / 2) := by
    have h := Real.sin_add_pi_div_two (θ - Real.pi / 2)
    rwa [show (θ - Real.pi / 2) + Real.pi / 2 = θ from by ring] at h
  rw [h1]
  rcases le_or_gt 0 (θ - Real.pi / 2) with h | h
  · exact cos_ge_half hθ
  · have h' : |-(θ - Real.pi / 2)| ≤ 1 / 2 := by rw [abs_neg]; exact hθ
    rw [← Real.cos_neg (θ - Real.pi / 2)]
    exact cos_ge_half h'

private lemma abs_cos_ge {θ : ℝ} (hθ : |θ - Real.pi / 2| ≤ 1 / 2) :
    |θ - Real.pi / 2| / 2 ≤ |Real.cos θ| := by
  have h1 : Real.cos θ = Real.sin (Real.pi / 2 - θ) := by
    have h := Real.cos_pi_div_two_sub (Real.pi / 2 - θ)
    rwa [sub_sub_cancel] at h
  have h2 : Real.sin (Real.pi / 2 - θ) = -Real.sin (θ - Real.pi / 2) := by
    rw [show Real.pi / 2 - θ = -(θ - Real.pi / 2) from by ring, Real.sin_neg]
  rw [h1, h2, abs_neg]
  exact abs_sin_ge hθ

theorem qfun_tendsto_zero_alt (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    Filter.Tendsto (qfun α) (nhds 0) (nhds 0) := by
  obtain ⟨C, hCpos, hCbd⟩ := Gzero_rpow_zero α hα hα1
  have hα3 : 0 < α / 3 := by linarith
  have hbound : ∀ θ : ℝ, |θ| ≤ 1 / 2 → |qfun α θ| ≤ (16 * C) * |θ| ^ (α / 3) := by
    intro θ hθ
    rcases eq_or_ne θ 0 with rfl | hne
    · have hz : qfun α 0 = 0 := by simp [qfun, Pfun]
      simp only [hz, abs_zero, Real.zero_rpow (ne_of_gt hα3), mul_zero, le_refl]
    · have hcos : (1 / 2 : ℝ) ≤ Real.cos θ := cos_ge_half hθ
      have hcos3 : (1 / 8 : ℝ) ≤ Real.cos θ ^ 3 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hcos 3
        norm_num at h
        exact h
      have hsin2 : θ ^ 2 / 4 ≤ Real.sin θ ^ 2 := by
        have h' : (|θ| / 2) ^ 2 ≤ |Real.sin θ| ^ 2 :=
          pow_le_pow_left₀ (by positivity) (abs_sin_ge hθ) 2
        have h1 : (|θ| / 2) ^ 2 = θ ^ 2 / 4 := by rw [div_pow, sq_abs θ]; norm_num
        have h2 : |Real.sin θ| ^ 2 = Real.sin θ ^ 2 := sq_abs _
        rwa [h1, h2] at h'
      have hden : θ ^ 2 / 16 ≤ 2 * Real.cos θ ^ 3 * Real.sin θ ^ 2 := by
        have hA : 2 * Real.cos θ ^ 3 * (θ ^ 2 / 4) ≤ 2 * Real.cos θ ^ 3 * Real.sin θ ^ 2 :=
          mul_le_mul_of_nonneg_left hsin2 (by positivity)
        have hB : 2 * (1 / 8) * (θ ^ 2 / 4) ≤ 2 * Real.cos θ ^ 3 * (θ ^ 2 / 4) := by
          have h := mul_le_mul_of_nonneg_right
            (by linarith : (2 : ℝ) * (1 / 8) ≤ 2 * Real.cos θ ^ 3)
            (by positivity : (0 : ℝ) ≤ θ ^ 2 / 4)
          linarith [h]
        calc θ ^ 2 / 16 = 2 * (1 / 8) * (θ ^ 2 / 4) := by ring
          _ ≤ 2 * Real.cos θ ^ 3 * (θ ^ 2 / 4) := hB
          _ ≤ 2 * Real.cos θ ^ 3 * Real.sin θ ^ 2 := hA
      have hG : |Gzero α θ| ≤ C * |θ| ^ (2 + α / 3) := hCbd θ hθ
      have hq : |qfun α θ| = |Gzero α θ| / (2 * Real.cos θ ^ 3 * Real.sin θ ^ 2) := by
        rw [qfun_apply, abs_div, abs_of_nonneg (sq_nonneg (Real.sin θ)), Pfun, abs_div,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.cos θ ^ 3), div_div]
      rw [hq]
      have hstep1 : |Gzero α θ| / (2 * Real.cos θ ^ 3 * Real.sin θ ^ 2)
          ≤ (C * |θ| ^ (2 + α / 3)) / (θ ^ 2 / 16) :=
        div_le_div₀ (by positivity) hG (by positivity) hden
      refine hstep1.trans ?_
      rw [show (2 + α / 3 : ℝ) = (2 : ℝ) + α / 3 from rfl, Real.rpow_add (abs_pos.mpr hne)]
      have hsq : |θ| ^ (2 : ℝ) = θ ^ 2 := by norm_num [Real.rpow_natCast, sq_abs]
      rw [hsq, div_le_iff₀ (by positivity : (0 : ℝ) < θ ^ 2 / 16)]
      ring_nf
      exact le_refl _
  have hlim : Filter.Tendsto (fun θ : ℝ => (16 * C) * |θ| ^ (α / 3)) (nhds 0) (nhds 0) := by
    have hcont : ContinuousAt (fun θ : ℝ => |θ| ^ (α / 3)) 0 :=
      continuous_abs.continuousAt.rpow_const (Or.inr (le_of_lt hα3))
    have hval : (fun θ : ℝ => |θ| ^ (α / 3)) 0 = 0 := by
      simp only [abs_zero]
      exact Real.zero_rpow (ne_of_gt hα3)
    have h2 : ContinuousAt (fun θ : ℝ => (16 * C) * |θ| ^ (α / 3)) 0 :=
      hcont.const_mul (16 * C)
    have h3 : (fun θ : ℝ => (16 * C) * |θ| ^ (α / 3)) 0 = 0 := by
      simp only [abs_zero, Real.zero_rpow (ne_of_gt hα3), mul_zero]
    simpa only [ContinuousAt, h3] using h2
  have hmain : Filter.Tendsto (fun θ : ℝ => |qfun α θ|) (nhds 0) (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) ?_ hlim
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with θ hθ
    have hθ' : |θ| ≤ 1 / 2 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hθ
      exact le_of_lt hθ
    exact hbound θ hθ'
  have hgoal : Filter.Tendsto (fun θ : ℝ => Pfun α θ / Real.sin θ ^ 2) (nhds 0) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs, qfun_apply] using hmain
  rw [show qfun α = (fun θ : ℝ => Pfun α θ / Real.sin θ ^ 2) from rfl]
  exact hgoal

/-- The two-sided power bound for `qfun` near `π/2`. -/
theorem qfun_tendsto_pi_div_two_alt (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    Filter.Tendsto (qfun α) (nhds (Real.pi / 2)) (nhds 0) := by
  obtain ⟨K, hKpos, hKbd⟩ := Gzero_rpow_pi_div_two α hα hα1
  have h2α3 : 0 < 2 * (α / 3) := by linarith
  have hbound : ∀ θ : ℝ, |θ - Real.pi / 2| ≤ 1 / 2 →
      |qfun α θ| ≤ (16 * K) * |θ - Real.pi / 2| ^ (2 * (α / 3)) := by
    intro θ hθ
    rcases eq_or_ne (θ - Real.pi / 2) 0 with hzero | hne
    · have hθpi : θ = Real.pi / 2 := by linarith [sub_eq_zero.mp hzero]
      subst hθpi
      have hq : qfun α (Real.pi / 2) = 0 := by
        rw [qfun_apply, Pfun, Gzero_pi_div_two, Real.cos_pi_div_two]
        norm_num
      simp only [hq, abs_zero, sub_self, abs_zero, Real.zero_rpow (ne_of_gt h2α3), mul_zero,
        le_refl]
    · have hδpos : 0 < |θ - Real.pi / 2| := abs_pos.mpr hne
      have hcos : |θ - Real.pi / 2| / 2 ≤ |Real.cos θ| := abs_cos_ge hθ
      have hcos3 : (|θ - Real.pi / 2| / 2) ^ 3 ≤ |Real.cos θ| ^ 3 :=
        pow_le_pow_left₀ (by positivity) hcos 3
      have hsin2 : (1 / 4 : ℝ) ≤ Real.sin θ ^ 2 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (sin_ge_half hθ) 2
        norm_num at h
        exact h
      have hden : |θ - Real.pi / 2| ^ 3 / 16 ≤ 2 * |Real.cos θ| ^ 3 * Real.sin θ ^ 2 := by
        have hA : 2 * |Real.cos θ| ^ 3 * (1 / 4) ≤
            2 * |Real.cos θ| ^ 3 * Real.sin θ ^ 2 :=
          mul_le_mul_of_nonneg_left hsin2 (by positivity)
        have hB : 2 * (|θ - Real.pi / 2| / 2) ^ 3 * (1 / 4) ≤
            2 * |Real.cos θ| ^ 3 * (1 / 4) := by
          have h := mul_le_mul_of_nonneg_right
            (by linarith : 2 * (|θ - Real.pi / 2| / 2) ^ 3 ≤ 2 * |Real.cos θ| ^ 3)
            (by norm_num : (0 : ℝ) ≤ 1 / 4)
          linarith [h]
        calc |θ - Real.pi / 2| ^ 3 / 16 = 2 * (|θ - Real.pi / 2| / 2) ^ 3 * (1 / 4) := by ring
          _ ≤ 2 * |Real.cos θ| ^ 3 * (1 / 4) := hB
          _ ≤ 2 * |Real.cos θ| ^ 3 * Real.sin θ ^ 2 := hA
      have hG : |Gzero α θ| ≤ K * |θ - Real.pi / 2| ^ (3 + 2 * (α / 3)) := hKbd θ hθ
      have hq : |qfun α θ| = |Gzero α θ| / (2 * |Real.cos θ| ^ 3 * Real.sin θ ^ 2) := by
        rw [qfun_apply, abs_div, abs_of_nonneg (sq_nonneg (Real.sin θ)), Pfun, abs_div,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_pow, div_div]
      rw [hq]
      have hstep1 : |Gzero α θ| / (2 * |Real.cos θ| ^ 3 * Real.sin θ ^ 2)
          ≤ (K * |θ - Real.pi / 2| ^ (3 + 2 * (α / 3))) / (|θ - Real.pi / 2| ^ 3 / 16) :=
        div_le_div₀ (by positivity) hG (by positivity) hden
      refine hstep1.trans ?_
      rw [show (3 + 2 * (α / 3) : ℝ) = (3 : ℝ) + 2 * (α / 3) from rfl,
        Real.rpow_add (abs_pos.mpr hne)]
      have hc3 : |θ - Real.pi / 2| ^ (3 : ℝ) = |θ - Real.pi / 2| ^ 3 := by
        norm_num [Real.rpow_natCast]
      rw [hc3, div_le_iff₀ (by positivity : (0 : ℝ) < |θ - Real.pi / 2| ^ 3 / 16)]
      ring_nf
      exact le_refl _
  have hlim : Filter.Tendsto
      (fun θ : ℝ => (16 * K) * |θ - Real.pi / 2| ^ (2 * (α / 3))) (nhds (Real.pi / 2))
      (nhds 0) := by
    have hcont : ContinuousAt (fun δ : ℝ => |δ| ^ (2 * (α / 3))) 0 :=
      continuous_abs.continuousAt.rpow_const (Or.inr (le_of_lt h2α3))
    have h2 : ContinuousAt (fun δ : ℝ => (16 * K) * |δ| ^ (2 * (α / 3))) 0 :=
      hcont.const_mul (16 * K)
    have h2' : Filter.Tendsto (fun δ : ℝ => (16 * K) * |δ| ^ (2 * (α / 3))) (nhds 0)
        (nhds 0) := by
      have h3 : (fun δ : ℝ => (16 * K) * |δ| ^ (2 * (α / 3))) 0 = 0 := by
        simp only [abs_zero, Real.zero_rpow (ne_of_gt h2α3), mul_zero]
      simpa only [ContinuousAt, h3] using h2
    have h1 : Filter.Tendsto (fun θ : ℝ => θ - Real.pi / 2) (nhds (Real.pi / 2)) (nhds 0) := by
      have h : Filter.Tendsto (fun θ : ℝ => θ - Real.pi / 2) (nhds (Real.pi / 2))
          (nhds (Real.pi / 2 - Real.pi / 2)) :=
        tendsto_id.sub tendsto_const_nhds
      simpa using h
    have h3 := h2'.comp h1
    simpa only [Function.comp_def] using h3
  have hmain : Filter.Tendsto (fun θ : ℝ => |qfun α θ|) (nhds (Real.pi / 2)) (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) ?_ hlim
    filter_upwards [Metric.ball_mem_nhds (Real.pi / 2) (by norm_num : (0 : ℝ) < 1 / 2)]
      with θ hθ
    have hθ' : |θ - Real.pi / 2| ≤ 1 / 2 := by
      rw [Metric.mem_ball, Real.dist_eq] at hθ
      exact le_of_lt hθ
    exact hbound θ hθ'
  have hgoal : Filter.Tendsto (fun θ : ℝ => Pfun α θ / Real.sin θ ^ 2) (nhds (Real.pi / 2))
      (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs, qfun_apply] using hmain
  rw [show qfun α = (fun θ : ℝ => Pfun α θ / Real.sin θ ^ 2) from rfl]
  exact hgoal


/-- **Both endpoint limits at once**, in the shape of `qfun_tendsto_endpoints`. -/
theorem qfun_tendsto_endpoints_alt (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    Filter.Tendsto (qfun α) (nhds 0) (nhds 0) ∧
      Filter.Tendsto (qfun α) (nhds (Real.pi / 2)) (nhds 0) :=
  ⟨qfun_tendsto_zero_alt α hα hα1, qfun_tendsto_pi_div_two_alt α hα hα1⟩

end Work.FTS.PhiStar.Psi0Est
