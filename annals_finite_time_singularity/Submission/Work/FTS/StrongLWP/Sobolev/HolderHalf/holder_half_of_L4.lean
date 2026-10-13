import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.vol_ball_prod
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.leg_one_bound
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.leg_two_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

/-!
# The 2-D Morrey estimate `W^{1,4}(ℝ²) ⊂ C^{0,1/2}` with constant `4`

`|v p - v q| ≤ 4 (∫ ‖∇v‖⁴)^{1/4} √(dist p q)` for `v : ℝ × ℝ → ℝ` of class `C¹` with compact
support (and the fundamental-theorem-of-calculus identity along segments).

The proof averages the segment identity over the ball `B(0, a)`, `a = ρ/2 = dist p q / 2`:

* `leg_one_bound` : `⨍_{ζ ∈ B(0,a)} |v p - v (p+ζ)| ≤ √2 (∫‖∇v‖⁴)^{1/4} √a`;
* `leg_two_bound` : `⨍_{ζ ∈ B(0,a)} |v (p+ζ) - v q| ≤ √2 (∫‖∇v‖⁴)^{1/4} (a + dist p q)/√a`.

Both are proved by Fubini plus the substitution that scales the ball, followed by Hölder with
exponents `(4, 4/3)` on the ball `B(0, ta)` of volume `4t²a²`, and `∫_0^1 t^{-1/2} dt = 2`.
Adding the two legs (the ball has volume `4a²` in the product/sup norm on `ℝ × ℝ`, so
`1/(4a²) ∫_B` is the mean value) and using
`√2 (√a + (a+ρ)/√a) = 4√ρ` for `a = ρ/2` gives the stated constant `4`.
-/

/-- Ball volume in `ℝ × ℝ` in real-valued form (for normalising averages). -/
private lemma vol_ball_real (x : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (ℝ × ℝ)).real (Metric.ball x r) = 4 * r ^ 2 := by
  rw [Measure.real_def, vol_ball_prod x hr, ENNReal.toReal_ofReal (by positivity)]

/-- The arithmetic core of the two-leg estimate: for `a = ρ/2`,
`√2 (√a + (a+ρ)/√a) = 4√ρ`. -/
private lemma arith {ρ : ℝ} (hρ : 0 < ρ) :
    Real.sqrt 2 * (Real.sqrt (ρ / 2) + (ρ / 2 + ρ) / Real.sqrt (ρ / 2)) = 4 * Real.sqrt ρ := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : Real.sqrt (ρ / 2) * Real.sqrt (ρ / 2) = ρ / 2 := Real.mul_self_sqrt (by positivity)
  have hpos : 0 < Real.sqrt (ρ / 2) := Real.sqrt_pos.mpr (by positivity)
  have hrp : Real.sqrt ρ = Real.sqrt 2 * Real.sqrt (ρ / 2) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hrp]
  field_simp
  nlinarith [h2, hs]

theorem holder_half_of_L4 {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (hseg : ∀ p z : ℝ × ℝ, v z - v p = ∫ t in (0 : ℝ)..1, (fderiv ℝ v (p + t • (z - p))) (z - p)) :
    ∀ p q : ℝ × ℝ, |v p - v q| ≤ 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) * Real.sqrt (dist p q) := by
  intro p q
  rcases eq_or_ne p q with hp | hpq
  · subst hp
    simp
  let ρ : ℝ := dist p q
  have hρpos : 0 < ρ := dist_pos.mpr hpq
  have ha' : 0 < ρ / 2 := by positivity
  -- integrability of the two summands on the ball
  have hvint : Integrable v := hv.continuous.integrable_of_hasCompactSupport hc
  have hvit : Integrable (fun ζ : ℝ × ℝ => v (p + ζ)) := by
    have h := hvint.comp_add_right p
    simpa [add_comm] using h
  have hBne : (volume : Measure (ℝ × ℝ)) (Metric.ball (0 : ℝ × ℝ) (ρ / 2)) ≠ ⊤ := by
    rw [vol_ball_prod (0 : ℝ × ℝ) (by positivity)]
    exact ENNReal.ofReal_ne_top
  have hint1 : IntegrableOn (fun ζ : ℝ × ℝ => |v p - v (p + ζ)|)
      (Metric.ball (0 : ℝ × ℝ) (ρ / 2)) :=
    Integrable.norm ((integrableOn_const (C := v p) hBne).sub hvit.integrableOn)
  have hint2 : IntegrableOn (fun ζ : ℝ × ℝ => |v (p + ζ) - v q|)
      (Metric.ball (0 : ℝ × ℝ) (ρ / 2)) :=
    Integrable.norm (hvit.integrableOn.sub (integrableOn_const (C := v q) hBne))
  have hconstint : IntegrableOn (fun _ : ℝ × ℝ => |v p - v q|)
      (Metric.ball (0 : ℝ × ℝ) (ρ / 2)) :=
    integrableOn_const (C := |v p - v q|) hBne
  -- the averaging step: `|v p - v q|` is bounded by the mean of `|v p - v (p+ζ)| + |v(p+ζ) - v q|`
  have hvolreal : (volume : Measure (ℝ × ℝ)).real (Metric.ball (0 : ℝ × ℝ) (ρ / 2))
      = 4 * (ρ / 2) ^ 2 := vol_ball_real _ (by positivity)
  have hconst : ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v q|
      = (4 * (ρ / 2) ^ 2) * |v p - v q| := by
    rw [setIntegral_const, smul_eq_mul, hvolreal]
  have hmono : ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v q|
      ≤ ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2),
          (|v p - v (p + ζ)| + |v (p + ζ) - v q|) := by
    refine integral_mono hconstint (hint1.add hint2) (fun ζ => ?_)
    calc |v p - v q| = |(v p - v (p + ζ)) + (v (p + ζ) - v q)| := by ring_nf
      _ ≤ |v p - v (p + ζ)| + |v (p + ζ) - v q| := abs_add_le _ _
  have hadd : ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2),
        (|v p - v (p + ζ)| + |v (p + ζ) - v q|)
      = (∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
        + ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q| :=
    integral_add hint1 hint2
  have hstep : (4 * (ρ / 2) ^ 2) * |v p - v q|
      ≤ (∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
        + ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q| := by
    rw [← hconst]
    exact hmono.trans (le_of_eq hadd)
  have key : |v p - v q| ≤ (1 / (4 * (ρ / 2) ^ 2)) *
      ((∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
        + ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q|) := by
    have hpos : 0 < 4 * (ρ / 2) ^ 2 := by positivity
    calc |v p - v q| = (1 / (4 * (ρ / 2) ^ 2)) * ((4 * (ρ / 2) ^ 2) * |v p - v q|) := by
          field_simp
      _ ≤ (1 / (4 * (ρ / 2) ^ 2)) *
            ((∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
              + ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q|) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
  -- the two leg estimates
  have hl1 := leg_one_bound (v := v) hv hc hseg p ha'
  have hl2 := leg_two_bound (v := v) hv hc hseg p q ha'
  have hG4 : (0 : ℝ) ≤ (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) := integral_nonneg (fun x => by positivity)
  have hcomb : (1 / (4 * (ρ / 2) ^ 2)) *
        ((∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
          + ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q|)
      ≤ Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)
          * (Real.sqrt (ρ / 2) + (ρ / 2 + ρ) / Real.sqrt (ρ / 2)) := by
    calc (1 / (4 * (ρ / 2) ^ 2)) *
          ((∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
            + ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q|)
        = (1 / (4 * (ρ / 2) ^ 2)) * (∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
          + (1 / (4 * (ρ / 2) ^ 2)) * ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q| := by
            ring
      _ ≤ Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) * Real.sqrt (ρ / 2)
          + Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)
              * ((ρ / 2 + ρ) / Real.sqrt (ρ / 2)) := add_le_add hl1 hl2
      _ = Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)
            * (Real.sqrt (ρ / 2) + (ρ / 2 + ρ) / Real.sqrt (ρ / 2)) := by ring
  have harith : Real.sqrt 2 * (Real.sqrt (ρ / 2) + (ρ / 2 + ρ) / Real.sqrt (ρ / 2))
      = 4 * Real.sqrt ρ := arith hρpos
  calc |v p - v q| ≤ (1 / (4 * (ρ / 2) ^ 2)) *
        ((∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v p - v (p + ζ)|)
          + ∫ ζ in Metric.ball (0 : ℝ × ℝ) (ρ / 2), |v (p + ζ) - v q|) := key
    _ ≤ Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)
          * (Real.sqrt (ρ / 2) + (ρ / 2 + ρ) / Real.sqrt (ρ / 2)) := hcomb
    _ = 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) * Real.sqrt ρ := by
        have e : Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)
              * (Real.sqrt (ρ / 2) + (ρ / 2 + ρ) / Real.sqrt (ρ / 2))
            = (Real.sqrt 2 * (Real.sqrt (ρ / 2) + (ρ / 2 + ρ) / Real.sqrt (ρ / 2)))
              * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) := by ring
        rw [e, harith]
        ring
    _ = 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) * Real.sqrt (dist p q) := by
        rw [show ρ = dist p q from rfl]

end Work.FTS.StrongLWP.Sobolev.HolderHalf
