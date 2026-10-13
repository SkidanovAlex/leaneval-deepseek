import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.vol_ball_prod
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D.integral_abs_le_L4_mul_vol
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D.setIntegral_comp_smul_add_ball

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped Pointwise

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

/-! ## First leg of the 2-D Morrey estimate

Averaging the segment identity over the ball `B(0,a)`:
`⨍_{ζ ∈ B(0,a)} |v p - v (p+ζ)| ≤ √2 (∫ ‖∇v‖⁴)^{1/4} √a`.

The substitution `ξ = t ζ` turns the inner integral at time `t` into `t^{-3}` times the same
quantity over `B(0,ta)`; Hölder (together with `‖ξ‖ ≤ ta` on that ball) gives
`t^{-3} · 4^{3/4}(ta)^{5/2}(∫‖∇v‖⁴)^{1/4} = 4^{3/4}a^{5/2}(∫‖∇v‖⁴)^{1/4} · t^{-1/2}`,
and `∫_0^1 t^{-1/2} dt = 2`. The final constant is
`(1/(4a²))·2·4^{3/4} = 2^{5/2}/4 = √2`. -/

/-- Integrability of a continuous function on a ball (via compactness of the closed ball). -/
private lemma legOne_integrableOn_ball_of_continuous {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    (x : ℝ × ℝ) (r : ℝ) : IntegrableOn g (Metric.ball x r) volume :=
  (ContinuousOn.integrableOn_compact (isCompact_closedBall x r) hg.continuousOn).mono_set
    Metric.ball_subset_closedBall

/-- Volume of a ball of `ℝ × ℝ` (product/sup norm) in real form. -/
private lemma legOne_ball_volume_real (x : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (ℝ × ℝ)).real (Metric.ball x r) = 4 * r ^ 2 := by
  rw [Measure.real_def, vol_ball_prod x hr, ENNReal.toReal_ofReal (by positivity)]

/-- `4^{3/4} = 2√2`. -/
private lemma legOne_rpow_four : (4 : ℝ) ^ (3 / 4 : ℝ) = 2 * Real.sqrt 2 := by
  have h2 : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * Real.sqrt 2 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (((2 : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]; norm_num
  nth_rewrite 1 [h4]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (((2 : ℕ) : ℝ)) * (3 / 4) = 3 / 2 by norm_num]
  exact h2

/-- `(4 R²)^{3/4} (R⁴ X)^{1/4} = 4^{3/4} R^{5/2} X^{1/4}` for `R > 0`, `X ≥ 0`. -/
private lemma legOne_rpow_arith {R X : ℝ} (hR : 0 < R) (hX : 0 ≤ X) :
    (4 * R ^ 2) ^ (3 / 4 : ℝ) * (R ^ 4 * X) ^ (1 / 4 : ℝ)
      = (4 : ℝ) ^ (3 / 4 : ℝ) * R ^ (5 / 2 : ℝ) * X ^ (1 / 4 : ℝ) := by
  have h4R : (4 * R ^ 2) ^ (3 / 4 : ℝ) = (4 : ℝ) ^ (3 / 4 : ℝ) * R ^ (3 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity : (0 : ℝ) ≤ R ^ 2)]
    congr 1
    rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le,
      show (((2 : ℕ) : ℝ)) * (3 / 4) = 3 / 2 by norm_num]
  have hRX : (R ^ 4 * X) ^ (1 / 4 : ℝ) = R * X ^ (1 / 4 : ℝ) := by
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ R ^ 4) hX]
    congr 1
    rw [← Real.rpow_natCast R 4, ← Real.rpow_mul hR.le,
      show (((4 : ℕ) : ℝ)) * (1 / 4) = 1 by norm_num, Real.rpow_one]
  have hR5 : R ^ (5 / 2 : ℝ) = R ^ (3 / 2 : ℝ) * R := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hR, Real.rpow_one]
  rw [h4R, hRX, hR5]
  ring

/-- Scaling arithmetic of the `t`-integral. -/
private lemma legOne_t_scale_arith {a t X : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (t ^ 3)⁻¹ * ((4 : ℝ) ^ (3 / 4 : ℝ) * (t * a) ^ (5 / 2 : ℝ) * X)
      = ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ) * X) * t ^ (-(1 / 2) : ℝ) := by
  have h1 : (t * a) ^ (5 / 2 : ℝ) = t ^ (5 / 2 : ℝ) * a ^ (5 / 2 : ℝ) :=
    Real.mul_rpow ht.le ha.le
  have h2 : (t ^ 3)⁻¹ = t ^ (-(((3 : ℕ) : ℝ))) := by
    rw [← Real.rpow_natCast t 3, ← Real.rpow_neg ht.le]
  have h3 : (4 : ℝ) ^ (3 / 4 : ℝ) * (t ^ (5 / 2 : ℝ) * a ^ (5 / 2 : ℝ)) * X
      = t ^ (5 / 2 : ℝ) * ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ) * X) := by ring
  rw [h1, h2, h3, ← mul_assoc, ← Real.rpow_add ht,
    show -(((3 : ℕ) : ℝ)) + 5 / 2 = -(1 / 2) by norm_num]
  ring

/-- Final arithmetic: `(1/(4a²))·2·4^{3/4}a^{5/2} = √2 √a`. -/
private lemma legOne_final_arith {a X : ℝ} (ha : 0 < a) :
    (1 / (4 * a ^ 2)) * (2 * ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ) * X))
      = Real.sqrt 2 * X * Real.sqrt a := by
  have ha5 : a ^ (5 / 2 : ℝ) = a ^ 2 * Real.sqrt a := by
    have h : a ^ (5 / 2 : ℝ) = a ^ (((2 : ℕ) : ℝ)) * a ^ (1 / 2 : ℝ) := by
      rw [show (5 / 2 : ℝ) = (((2 : ℕ) : ℝ)) + 1 / 2 by norm_num, Real.rpow_add ha]
    rw [h, Real.rpow_natCast a 2, ← Real.sqrt_eq_rpow]
  rw [legOne_rpow_four, ha5]
  have hden : (4 * a ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The pointwise segment bound obtained from the fundamental theorem of calculus. -/
private lemma legOne_abs_sub_le_integral_fderiv {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v)
    {p z : ℝ × ℝ}
    (hseg : v z - v p = ∫ t in (0 : ℝ)..1, (fderiv ℝ v (p + t • (z - p))) (z - p)) :
    |v z - v p| ≤ ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v (p + t • (z - p))‖ * ‖z - p‖ := by
  have hcont : Continuous (fun t : ℝ => (fderiv ℝ v (p + t • (z - p))) (z - p)) :=
    (hv.continuous_fderiv_apply (by norm_num)).comp
      ((continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const)
  have hcont2 : Continuous (fun t : ℝ => fderiv ℝ v (p + t • (z - p))) :=
    (hv.continuous_fderiv (by norm_num)).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hint1 : IntervalIntegrable
      (fun t : ℝ => |(fderiv ℝ v (p + t • (z - p))) (z - p)|) volume 0 1 := by
    simpa only [Real.norm_eq_abs] using hcont.norm.intervalIntegrable 0 1
  have hint2 : IntervalIntegrable
      (fun t : ℝ => ‖fderiv ℝ v (p + t • (z - p))‖ * ‖z - p‖) volume 0 1 :=
    (hcont2.norm.mul_const ‖z - p‖).intervalIntegrable 0 1
  rw [hseg]
  refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0 : ℝ) ≤ 1)).trans ?_
  refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hint1 hint2
    (fun t _ => ?_)
  simpa only [Real.norm_eq_abs] using (fderiv ℝ v (p + t • (z - p))).le_opNorm (z - p)

/-- Change of variables `ξ = t ζ` in the weighted ball integral. -/
private lemma legOne_smul_subst {v : ℝ × ℝ → ℝ} (p : ℝ × ℝ) {a t : ℝ} (ht : 0 < t) :
    ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖
      = (t ^ 3)⁻¹ * ∫ ξ in Metric.ball (0 : ℝ × ℝ) (t * a), ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖ := by
  have ht0 : t ≠ 0 := ht.ne'
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have hsmulball : t • Metric.ball (0 : ℝ × ℝ) a = Metric.ball (0 : ℝ × ℝ) (t * a) := by
    rw [smul_ball ht0, smul_zero, Real.norm_of_nonneg ht.le]
  have hfun : (fun ζ : ℝ × ℝ => ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖)
      = fun ζ : ℝ × ℝ => (fun ξ : ℝ × ℝ => ‖t⁻¹ • ξ‖ * ‖fderiv ℝ v (p + ξ)‖) (t • ζ) := by
    funext ζ
    simp only [smul_smul, inv_mul_cancel₀ ht0, one_smul]
  have hcongr : ∀ ξ : ℝ × ℝ,
      ‖t⁻¹ • ξ‖ * ‖fderiv ℝ v (p + ξ)‖ = t⁻¹ * (‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) := by
    intro ξ
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
    ring
  rw [hfun, Measure.setIntegral_comp_smul_of_pos (μ := volume)
      (f := fun ξ : ℝ × ℝ => ‖t⁻¹ • ξ‖ * ‖fderiv ℝ v (p + ξ)‖)
      (s := Metric.ball (0 : ℝ × ℝ) a) ht, hsmulball, hfin]
  rw [smul_eq_mul, setIntegral_congr_fun measurableSet_ball (fun ξ _ => hcongr ξ),
    integral_const_mul]
  have h3 : (t ^ 2)⁻¹ * t⁻¹ = (t ^ 3)⁻¹ := by
    rw [← mul_inv_rev, show t * t ^ 2 = t ^ 3 by ring]
  rw [← h3, mul_assoc]

/-- The `L⁴`/Hölder bound on a ball. -/
private lemma legOne_ball_L4_bound {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v)
    (hc : HasCompactSupport v) (p : ℝ × ℝ) {R : ℝ} (hR : 0 < R) :
    ∫ ξ in Metric.ball (0 : ℝ × ℝ) R, ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖
      ≤ (4 : ℝ) ^ (3 / 4 : ℝ) * R ^ (5 / 2 : ℝ)
        * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) := by
  have hR0 : (0 : ℝ) ≤ R := hR.le
  have hAint : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 4) volume := by
    have hcs : HasCompactSupport (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 4) :=
      (hc.fderiv ℝ).mono (by
        intro x hx
        simp only [Function.mem_support] at hx ⊢
        intro h0
        exact hx (by rw [h0]; norm_num))
    exact ((hv.continuous_fderiv (by norm_num)).norm.pow 4).integrable_of_hasCompactSupport hcs
  obtain ⟨M, hM⟩ :=
    (hc.fderiv ℝ).exists_bound_of_continuous (hv.continuous_fderiv (by norm_num))
  have hvol : volume (Metric.ball (0 : ℝ × ℝ) R) = ENNReal.ofReal (4 * R ^ 2) :=
    vol_ball_prod (0 : ℝ × ℝ) hR0
  have hvol_lt : volume (Metric.ball (0 : ℝ × ℝ) R) < ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℝ × ℝ) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hvol_lt⟩
  have hfncont : Continuous (fun ξ : ℝ × ℝ => ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) :=
    continuous_norm.mul
      (((hv.continuous_fderiv (by norm_num)).norm).comp (continuous_const.add continuous_id))
  have hMemLp : MemLp (fun ξ : ℝ × ℝ => ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) 4
      (volume.restrict (Metric.ball (0 : ℝ × ℝ) R)) := by
    refine MemLp.of_bound hfncont.aestronglyMeasurable (R * max M 0) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with ξ hξ
    rw [Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul ?_ ((hM (p + ξ)).trans (le_max_left M 0)) (norm_nonneg _) hR0
    have h2 : ‖ξ‖ < R := by
      simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hξ
    exact h2.le
  have hHolder := Morrey2D.integral_abs_le_L4_mul_vol
    (s := Metric.ball (0 : ℝ × ℝ) R)
    (f := fun ξ : ℝ × ℝ => ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) hvol_lt hMemLp
  have hL : (∫ x in Metric.ball (0 : ℝ × ℝ) R,
        |(fun ξ : ℝ × ℝ => ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) x|)
      = ∫ ξ in Metric.ball (0 : ℝ × ℝ) R, ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖ := by
    refine setIntegral_congr_fun measurableSet_ball (fun ξ _ => ?_)
    exact abs_of_nonneg (by positivity)
  have hR4 : (∫ x in Metric.ball (0 : ℝ × ℝ) R,
        |(fun ξ : ℝ × ℝ => ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) x| ^ 4)
      ≤ R ^ 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) := by
    have habs : ∀ x : ℝ × ℝ,
        |(fun ξ : ℝ × ℝ => ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) x| ^ 4
          = (‖x‖ * ‖fderiv ℝ v (p + x)‖) ^ 4 := by
      intro x
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs, ← pow_mul]
    rw [setIntegral_congr_fun measurableSet_ball (fun x _ => habs x)]
    have hpt : ∀ x ∈ Metric.ball (0 : ℝ × ℝ) R,
        (‖x‖ * ‖fderiv ℝ v (p + x)‖) ^ 4 ≤ R ^ 4 * ‖fderiv ℝ v (p + x)‖ ^ 4 := by
      intro x hx
      have h1 : ‖x‖ ≤ R := by
        have h2 : ‖x‖ < R := by
          simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hx
        exact h2.le
      have h2 : ‖x‖ ^ 4 ≤ R ^ 4 := pow_le_pow_left₀ (norm_nonneg x) h1 4
      calc (‖x‖ * ‖fderiv ℝ v (p + x)‖) ^ 4
          = ‖x‖ ^ 4 * ‖fderiv ℝ v (p + x)‖ ^ 4 := mul_pow _ _ 4
        _ ≤ R ^ 4 * ‖fderiv ℝ v (p + x)‖ ^ 4 := by gcongr
    have hcont1 : Continuous (fun x : ℝ × ℝ => (‖x‖ * ‖fderiv ℝ v (p + x)‖) ^ 4) :=
      hfncont.pow 4
    have hcont2 : Continuous (fun x : ℝ × ℝ => R ^ 4 * ‖fderiv ℝ v (p + x)‖ ^ 4) :=
      continuous_const.mul ((((hv.continuous_fderiv (by norm_num)).norm).comp
        (continuous_const.add continuous_id)).pow 4)
    calc ∫ x in Metric.ball (0 : ℝ × ℝ) R, (‖x‖ * ‖fderiv ℝ v (p + x)‖) ^ 4
        ≤ ∫ x in Metric.ball (0 : ℝ × ℝ) R, R ^ 4 * ‖fderiv ℝ v (p + x)‖ ^ 4 :=
          setIntegral_mono_on (legOne_integrableOn_ball_of_continuous hcont1 0 R)
            (legOne_integrableOn_ball_of_continuous hcont2 0 R) measurableSet_ball hpt
      _ = R ^ 4 * ∫ x in Metric.ball (0 : ℝ × ℝ) R, ‖fderiv ℝ v (p + x)‖ ^ 4 :=
          integral_const_mul _ _
      _ ≤ R ^ 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hshift : ∫ x in Metric.ball (0 : ℝ × ℝ) R, ‖fderiv ℝ v (p + x)‖ ^ 4
              = ∫ w in Metric.ball p R, ‖fderiv ℝ v w‖ ^ 4 := by
            have h := Morrey2D.setIntegral_comp_smul_add_ball
              (f := fun w : ℝ × ℝ => ‖fderiv ℝ v w‖ ^ 4) (a := R) (t := 1)
              (by norm_num : (0 : ℝ) < 1) p
            simpa using h
          rw [hshift]
          exact setIntegral_le_integral hAint (ae_of_all _ (fun w => by positivity))
  rw [hL] at hHolder
  have hHolder' : ∫ ξ in Metric.ball (0 : ℝ × ℝ) R, ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖
      ≤ (4 * R ^ 2) ^ (3 / 4 : ℝ)
        * (R ^ 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4)) ^ (1 / 4 : ℝ) := by
    rw [← Measure.real_def, legOne_ball_volume_real (0 : ℝ × ℝ) hR0] at hHolder
    refine hHolder.trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hR4 (by norm_num))
      (Real.rpow_nonneg (by positivity) _)
  refine hHolder'.trans (le_of_eq ?_)
  exact legOne_rpow_arith hR (integral_nonneg (fun x => by positivity))

/-- The main inequality after the `t`-integration. -/
private lemma legOne_main {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (hseg : ∀ p z : ℝ × ℝ, v z - v p = ∫ t in (0 : ℝ)..1,
      (fderiv ℝ v (p + t • (z - p))) (z - p)) (p : ℝ × ℝ) {a : ℝ} (ha : 0 < a) :
    ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, |v p - v (p + ζ)|
      ≤ 2 * ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
        * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) := by
  have hpt : ∀ ζ : ℝ × ℝ,
      |v p - v (p + ζ)| ≤ ∫ t in (0 : ℝ)..1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ := by
    intro ζ
    have h := legOne_abs_sub_le_integral_fderiv hv (hseg p (p + ζ))
    rw [abs_sub_comm] at h
    simpa [add_sub_cancel_left, mul_comm] using h
  have hjoint : Integrable
      (Function.uncurry fun (t : ℝ) (ζ : ℝ × ℝ) => ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict (Metric.ball (0 : ℝ × ℝ) a))) := by
    have hcont : Continuous (Function.uncurry
        fun (t : ℝ) (ζ : ℝ × ℝ) => ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖) := by
      show Continuous fun q : ℝ × (ℝ × ℝ) => ‖q.2‖ * ‖fderiv ℝ v (p + q.1 • q.2)‖
      refine continuous_norm.comp continuous_snd |>.mul ?_
      exact (((hv.continuous_fderiv (by norm_num)).norm).comp
        (continuous_const.add (continuous_fst.smul continuous_snd)))
    have hIntOn : IntegrableOn
        (Function.uncurry fun (t : ℝ) (ζ : ℝ × ℝ) => ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖)
        (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ℝ × ℝ) a) volume :=
      ContinuousOn.integrableOn_compact
        (isCompact_Icc.prod (isCompact_closedBall (0 : ℝ × ℝ) a)) hcont.continuousOn
    have hIntOn' : IntegrableOn
        (Function.uncurry fun (t : ℝ) (ζ : ℝ × ℝ) => ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖)
        (Set.Ioc (0 : ℝ) 1 ×ˢ Metric.ball (0 : ℝ × ℝ) a) volume :=
      hIntOn.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Metric.ball_subset_closedBall)
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hIntOn'
  have hInner : IntegrableOn (fun ζ : ℝ × ℝ =>
      ∫ t in (0 : ℝ)..1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖) (Metric.ball (0 : ℝ × ℝ) a) volume := by
    have h1 : Integrable (fun ζ : ℝ × ℝ =>
        ∫ t, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
        (volume.restrict (Metric.ball (0 : ℝ × ℝ) a)) := hjoint.integral_prod_right
    refine h1.congr ?_
    filter_upwards with ζ
    exact (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm
  have hleft : IntegrableOn (fun ζ : ℝ × ℝ => |v p - v (p + ζ)|)
      (Metric.ball (0 : ℝ × ℝ) a) volume := by
    refine legOne_integrableOn_ball_of_continuous ?_ 0 a
    have h1 : Continuous (fun ζ : ℝ × ℝ => v p - v (p + ζ)) :=
      continuous_const.sub (hv.continuous.comp (continuous_const.add continuous_id))
    simpa only [Real.norm_eq_abs] using h1.norm
  have hB : ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, |v p - v (p + ζ)|
      ≤ ∫ ζ in Metric.ball (0 : ℝ × ℝ) a,
          ∫ t in (0 : ℝ)..1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ :=
    setIntegral_mono_on hleft hInner measurableSet_ball (fun ζ _ => hpt ζ)
  have hIocEq : ∫ ζ in Metric.ball (0 : ℝ × ℝ) a,
        (∫ t in (0 : ℝ)..1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖)
      = ∫ ζ in Metric.ball (0 : ℝ × ℝ) a,
          ∫ t in Set.Ioc (0 : ℝ) 1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ :=
    setIntegral_congr_fun measurableSet_ball
      (fun ζ _ => intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1))
  have hswap : ∫ ζ in Metric.ball (0 : ℝ × ℝ) a,
        ∫ t in Set.Ioc (0 : ℝ) 1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖
      = ∫ t in Set.Ioc (0 : ℝ) 1,
          ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ :=
    (integral_integral_swap hjoint).symm
  have hC : ∫ t in Set.Ioc (0 : ℝ) 1,
        (∫ ζ in Metric.ball (0 : ℝ × ℝ) a, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖)
      = ∫ t in Set.Ioc (0 : ℝ) 1, (t ^ 3)⁻¹ *
          (∫ ξ in Metric.ball (0 : ℝ × ℝ) (t * a), ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) :=
    setIntegral_congr_fun measurableSet_Ioc (fun t ht => legOne_smul_subst p ht.1)
  have hD : ∫ t in Set.Ioc (0 : ℝ) 1, (t ^ 3)⁻¹ *
        (∫ ξ in Metric.ball (0 : ℝ × ℝ) (t * a), ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖)
      ≤ ∫ t in Set.Ioc (0 : ℝ) 1,
          ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
            * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) * t ^ (-(1 / 2) : ℝ) := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      exact mul_nonneg (inv_nonneg.mpr (by positivity))
        (setIntegral_nonneg measurableSet_ball (fun ξ _ => by positivity))
    · have hrp : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) volume 0 1 :=
        intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))
      exact hrp.1.const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      calc (t ^ 3)⁻¹ *
            (∫ ξ in Metric.ball (0 : ℝ × ℝ) (t * a), ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖)
          ≤ (t ^ 3)⁻¹ * ((4 : ℝ) ^ (3 / 4 : ℝ) * (t * a) ^ (5 / 2 : ℝ)
              * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left (legOne_ball_L4_bound hv hc p (by positivity))
              (by positivity)
        _ = ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
              * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) * t ^ (-(1 / 2) : ℝ) :=
            legOne_t_scale_arith ha ht0
  have hrpow : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ (-(1 / 2) : ℝ) = 2 := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
    norm_num [Real.zero_rpow]
  have hE : ∫ t in Set.Ioc (0 : ℝ) 1,
        ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
          * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) * t ^ (-(1 / 2) : ℝ)
      = ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
          * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) * 2 := by
    rw [integral_const_mul, hrpow]
  calc ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, |v p - v (p + ζ)|
      ≤ ∫ ζ in Metric.ball (0 : ℝ × ℝ) a,
          ∫ t in (0 : ℝ)..1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ := hB
    _ = ∫ ζ in Metric.ball (0 : ℝ × ℝ) a,
          ∫ t in Set.Ioc (0 : ℝ) 1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ := hIocEq
    _ = ∫ t in Set.Ioc (0 : ℝ) 1,
          ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ := hswap
    _ = ∫ t in Set.Ioc (0 : ℝ) 1, (t ^ 3)⁻¹ *
          (∫ ξ in Metric.ball (0 : ℝ × ℝ) (t * a), ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) := hC
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) 1,
          ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
            * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) * t ^ (-(1 / 2) : ℝ) := hD
    _ = ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
          * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) * 2 := hE
    _ = 2 * ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
          * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) := by ring

/-- **First leg of the 2-D Morrey estimate.**  Averaging the segment identity over the ball
`B(0,a)` (a square of volume `4a²` in the product norm on `ℝ × ℝ`) gives
`⨍_{ζ ∈ B(0,a)} |v p - v (p+ζ)| ≤ √2 (∫ ‖∇v‖⁴)^{1/4} √a`.
Proof route: segment bound `|v(p+ζ) - v p| ≤ ‖ζ‖ ∫_0^1 ‖∇v(p+tζ)‖ dt`; Fubini in `(ζ,t)`;
substitution `ξ = t ζ` (`MeasureTheory.Measure.setIntegral_comp_smul` + `smul_ball`, using
`Module.finrank ℝ (ℝ × ℝ) = 2`); Hölder `(4, 4/3)` on each ball `B(0,ta)` of volume `4t²a²`;
finally `∫_0^1 t^{-1/2} dt = 2`. -/
theorem leg_one_bound {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (hseg : ∀ p z : ℝ × ℝ, v z - v p = ∫ t in (0 : ℝ)..1, (fderiv ℝ v (p + t • (z - p))) (z - p))
    (p : ℝ × ℝ) {a : ℝ} (ha : 0 < a) :
    (1 / (4 * a ^ 2)) * ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, |v p - v (p + ζ)|
      ≤ Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) * Real.sqrt a := by
  calc (1 / (4 * a ^ 2)) * ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, |v p - v (p + ζ)|
      ≤ (1 / (4 * a ^ 2)) * (2 * ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
          * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (legOne_main hv hc hseg p ha) (by positivity)
    _ = Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) * Real.sqrt a :=
        legOne_final_arith ha

end Work.FTS.StrongLWP.Sobolev.HolderHalf
