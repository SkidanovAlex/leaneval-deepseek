import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.vol_ball_prod
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D.integral_abs_le_L4_mul_vol
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D.setIntegral_comp_smul_add_ball
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D.rpow_scale_identity
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D.arith_final
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D.abs_sub_le_mul_integral_norm_fderiv
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D.integral_ball_integral_swap

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

-- the skeleton carried this `namespace` line twice; it is kept so that the literal name
-- `...HolderHalf.Work.FTS.StrongLWP.Sobolev.HolderHalf.leg_two_bound` also exists
set_option linter.dupNamespace false

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

private lemma hasCompactSupport_norm_fderiv {v : ℝ × ℝ → ℝ} (hc : HasCompactSupport v) :
    HasCompactSupport (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖) :=
  (HasCompactSupport.fderiv ℝ hc).comp_left (g := fun L : ℝ × ℝ →L[ℝ] ℝ => ‖L‖) (by simp)

/-- `∫_0^1 t^{-1/2} dt = 2`, the `s`-integral of the two-leg Morrey estimate. -/
private lemma integral_rpow_neg_half : ∫ t in (0 : ℝ)..1, t ^ (-1 / 2 : ℝ) = 2 := by
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
  norm_num

private lemma integrable_norm_fderiv_pow4 {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v)
    (hc : HasCompactSupport v) :
    Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 4) := by
  have hcont : Continuous (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 4) :=
    (hv.continuous_fderiv (by norm_num)).norm.pow 4
  have hcs : HasCompactSupport (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 4) :=
    (HasCompactSupport.fderiv ℝ hc).comp_left
      (g := fun L : ℝ × ℝ →L[ℝ] ℝ => ‖L‖ ^ 4) (by simp)
  exact hcont.integrable_of_hasCompactSupport hcs

/-- **Second leg of the 2-D Morrey estimate.**  Averaging the segment identity (from `p+ζ` to `q`)
over the ball `B(0,a)` gives
`⨍_{ζ ∈ B(0,a)} |v (p+ζ) - v q| ≤ √2 (∫ ‖∇v‖⁴)^{1/4} (a + dist p q)/√a`.
Proof route: `‖(p+ζ) - q‖ ≤ a + dist p q`; Fubini in `(ζ,s)`; substitution `w = q + s((p+ζ)-q)`;
Hölder `(4, 4/3)` on each ball `B(q+s(p-q), sa)` of volume `4s²a²`; finally
`∫_0^1 s^{-1/2} ds = 2`. -/
theorem leg_two_bound {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (hseg : ∀ p z : ℝ × ℝ, v z - v p = ∫ t in (0 : ℝ)..1, (fderiv ℝ v (p + t • (z - p))) (z - p))
    (p q : ℝ × ℝ) {a : ℝ} (ha : 0 < a) :
    (1 / (4 * a ^ 2)) * ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, |v (p + ζ) - v q|
      ≤ Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)
        * ((a + dist p q) / Real.sqrt a) := by
  have hfderiv : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  have hcsn : HasCompactSupport (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖) :=
    hasCompactSupport_norm_fderiv hc
  have hint4 : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 4) :=
    integrable_norm_fderiv_pow4 hv hc
  set d : ℝ := dist p q with hd
  set G4 : ℝ := ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4 with hG4
  have hd0 : 0 ≤ d := by rw [hd]; exact dist_nonneg
  have hG40 : 0 ≤ G4 := by
    rw [hG4]
    exact integral_nonneg fun x => by positivity
  set B : Set (ℝ × ℝ) := Metric.ball (0 : ℝ × ℝ) a with hB
  set Λ : (ℝ × ℝ) → ℝ → ℝ := fun ζ t => ‖fderiv ℝ v (q + t • ((p + ζ) - q))‖ with hΛ
  have hΛcont : Continuous (Function.uncurry Λ) := by
    have hun : Function.uncurry Λ
        = fun x : (ℝ × ℝ) × ℝ => ‖fderiv ℝ v (q + x.2 • ((p + x.1) - q))‖ := by
      rw [hΛ]; rfl
    rw [hun]
    have h1 : Continuous fun x : (ℝ × ℝ) × ℝ => x.2 • ((p + x.1) - q) :=
      continuous_snd.smul ((continuous_const.add continuous_fst).sub continuous_const)
    have h2 : Continuous fun x : (ℝ × ℝ) × ℝ => q + x.2 • ((p + x.1) - q) :=
      continuous_const.add h1
    exact (hfderiv.comp h2).norm
  have hmble : MeasurableSet B := by rw [hB]; exact Metric.isOpen_ball.measurableSet
  -- Step 1: pointwise segment bound
  have hpt : ∀ ζ ∈ B, |v (p + ζ) - v q| ≤ (a + d) * ∫ t in (0 : ℝ)..1, Λ ζ t := by
    intro ζ hζ
    have hζlt : ‖ζ‖ < a := by
      have h := hζ
      rw [hB, Metric.mem_ball, dist_zero_right] at h
      exact h
    have hzq : ‖(p + ζ) - q‖ ≤ a + d := by
      have h1 : (p + ζ) - q = (p - q) + ζ := by abel
      calc ‖(p + ζ) - q‖ = ‖(p - q) + ζ‖ := by rw [h1]
        _ ≤ ‖p - q‖ + ‖ζ‖ := norm_add_le _ _
        _ = d + ‖ζ‖ := by rw [hd, dist_eq_norm]
        _ ≤ d + a := by linarith
        _ = a + d := by ring
    have hnn : 0 ≤ ∫ t in (0 : ℝ)..1, Λ ζ t := by
      refine intervalIntegral.integral_nonneg (by norm_num) ?_
      intro t ht
      rw [hΛ]
      positivity
    calc |v (p + ζ) - v q| ≤ ‖(p + ζ) - q‖ * ∫ t in (0 : ℝ)..1, Λ ζ t := by
          rw [hΛ]
          exact abs_sub_le_mul_integral_norm_fderiv hv hseg q (p + ζ)
      _ ≤ (a + d) * ∫ t in (0 : ℝ)..1, Λ ζ t := mul_le_mul_of_nonneg_right hzq hnn
  -- integrability of both sides on the ball
  have hleft_int : IntegrableOn (fun ζ : ℝ × ℝ => |v (p + ζ) - v q|) B := by
    have hcont : Continuous fun ζ : ℝ × ℝ => |v (p + ζ) - v q| :=
      ((hv.continuous.comp (continuous_const.add continuous_id)).sub continuous_const).abs
    rw [hB]
    exact (hcont.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℝ × ℝ) a)).mono_set
      Metric.ball_subset_closedBall
  have hright_int : IntegrableOn (fun ζ : ℝ × ℝ => (a + d) * ∫ t in (0 : ℝ)..1, Λ ζ t) B := by
    have hcont : Continuous fun ζ : ℝ × ℝ => (a + d) * ∫ t in (0 : ℝ)..1, Λ ζ t :=
      continuous_const.mul
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hΛcont 0 1)
    rw [hB]
    exact (hcont.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℝ × ℝ) a)).mono_set
      Metric.ball_subset_closedBall
  have hstep1 : ∫ ζ in B, |v (p + ζ) - v q|
      ≤ ∫ ζ in B, (a + d) * ∫ t in (0 : ℝ)..1, Λ ζ t :=
    setIntegral_mono_on hleft_int hright_int hmble hpt
  have hstep2 : ∫ ζ in B, (a + d) * ∫ t in (0 : ℝ)..1, Λ ζ t
      = (a + d) * ∫ ζ in B, (∫ t in (0 : ℝ)..1, Λ ζ t) := by
    rw [integral_const_mul]
  have hstep3 : ∫ ζ in B, (∫ t in (0 : ℝ)..1, Λ ζ t)
      = ∫ t in (0 : ℝ)..1, ∫ ζ in B, Λ ζ t := by
    rw [hB]
    exact integral_ball_integral_swap hΛcont ha
  -- Step 2: the per-t bound
  have hkey : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∫ ζ in B, Λ ζ t ≤ (4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (-1 / 2 : ℝ) * G4 ^ (1 / 4 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    set c : ℝ × ℝ := q + t • (p - q) with hc
    have hArg : ∀ y : ℝ × ℝ, c + t • y = q + t • ((p + y) - q) := by
      intro y
      rw [hc]
      simp only [smul_sub, smul_add]
      abel
    have hsub : ∫ y in Metric.ball (0 : ℝ × ℝ) a, ‖fderiv ℝ v (c + t • y)‖
        = (t ^ 2)⁻¹ * ∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ := by
      simpa only using setIntegral_comp_smul_add_ball (fun w : ℝ × ℝ => ‖fderiv ℝ v w‖) ht0 c
    have hlhs : ∫ ζ in B, Λ ζ t = (t ^ 2)⁻¹ * ∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ := by
      rw [hB, hΛ]
      have h1 : (∫ y in Metric.ball (0 : ℝ × ℝ) a, ‖fderiv ℝ v (q + t • ((p + y) - q))‖)
          = ∫ y in Metric.ball (0 : ℝ × ℝ) a, ‖fderiv ℝ v (c + t • y)‖ := by
        apply setIntegral_congr_fun measurableSet_ball
        intro y hy
        show ‖fderiv ℝ v (q + t • ((p + y) - q))‖ = ‖fderiv ℝ v (c + t • y)‖
        rw [hArg y]
      rw [h1]
      exact hsub
    -- Hölder on the ball `ball c (t*a)`
    have hvol : (volume (Metric.ball c (t * a))).toReal = 4 * (t * a) ^ 2 := by
      rw [vol_ball_prod c (by positivity), ENNReal.toReal_ofReal (by positivity)]
    have hlt : volume (Metric.ball c (t * a)) < ⊤ := by
      rw [vol_ball_prod c (by positivity)]
      exact ENNReal.ofReal_lt_top
    have hmem : MemLp (fun w : ℝ × ℝ => ‖fderiv ℝ v w‖) 4
        (volume.restrict (Metric.ball c (t * a))) :=
      (hfderiv.norm.memLp_of_hasCompactSupport hcsn).restrict _
    have hholder := integral_abs_le_L4_mul_vol hlt hmem
    have habs4 : (∫ w in Metric.ball c (t * a), |‖fderiv ℝ v w‖| ^ 4)
        = ∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ ^ 4 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro w hw
      show |‖fderiv ℝ v w‖| ^ 4 = ‖fderiv ℝ v w‖ ^ 4
      rw [abs_of_nonneg (norm_nonneg _)]
    have hholder' : ∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖
        ≤ (volume (Metric.ball c (t * a))).toReal ^ (3 / 4 : ℝ)
          * (∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ ^ 4) ^ (1 / 4 : ℝ) := by
      calc ∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖
          = ∫ w in Metric.ball c (t * a), |‖fderiv ℝ v w‖| := by
            apply setIntegral_congr_fun measurableSet_ball
            intro w hw
            show ‖fderiv ℝ v w‖ = |‖fderiv ℝ v w‖|
            rw [abs_of_nonneg (norm_nonneg _)]
        _ ≤ (volume (Metric.ball c (t * a))).toReal ^ (3 / 4 : ℝ)
              * (∫ w in Metric.ball c (t * a), |‖fderiv ℝ v w‖| ^ 4) ^ (1 / 4 : ℝ) := hholder
        _ = (volume (Metric.ball c (t * a))).toReal ^ (3 / 4 : ℝ)
              * (∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ ^ 4) ^ (1 / 4 : ℝ) := by
              rw [habs4]
    have h4le : (∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ ^ 4) ≤ G4 := by
      have h := setIntegral_le_integral (μ := volume) (s := Metric.ball c (t * a))
        (f := fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 4) hint4
        (Filter.Eventually.of_forall fun x => by positivity)
      rw [hG4]
      exact h
    calc ∫ ζ in B, Λ ζ t
        = (t ^ 2)⁻¹ * ∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ := hlhs
      _ ≤ (t ^ 2)⁻¹ * ((volume (Metric.ball c (t * a))).toReal ^ (3 / 4 : ℝ)
            * (∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ ^ 4) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hholder' (by positivity)
      _ = (t ^ 2)⁻¹ * ((4 * (t * a) ^ 2) ^ (3 / 4 : ℝ)
            * (∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ ^ 4) ^ (1 / 4 : ℝ)) := by
          rw [hvol]
      _ ≤ (t ^ 2)⁻¹ * ((4 * (t * a) ^ 2) ^ (3 / 4 : ℝ) * G4 ^ (1 / 4 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow (by positivity) h4le (by norm_num)
      _ = (4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (-1 / 2 : ℝ) * G4 ^ (1 / 4 : ℝ) := by
          rw [← mul_assoc, rpow_scale_identity ha ht0]
  -- Step 3: integrate the per-t bound
  have h7 : ∫ t in (0 : ℝ)..1, ∫ ζ in B, Λ ζ t
      ≤ (4 * a ^ 2) ^ (3 / 4 : ℝ) * G4 ^ (1 / 4 : ℝ) * 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hrpow : IntegrableOn (fun t : ℝ => t ^ (-1 / 2 : ℝ)) (Set.Ioc (0 : ℝ) 1) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -1 / 2)
    have hgint : Integrable (fun t : ℝ =>
        (4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (-1 / 2 : ℝ) * G4 ^ (1 / 4 : ℝ))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      Integrable.mul_const (Integrable.const_mul hrpow ((4 * a ^ 2) ^ (3 / 4 : ℝ)))
        (G4 ^ (1 / 4 : ℝ))
    have hmono := integral_mono_of_nonneg
      (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (f := fun t : ℝ => ∫ ζ in B, Λ ζ t)
      (g := fun t : ℝ => (4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (-1 / 2 : ℝ) * G4 ^ (1 / 4 : ℝ))
      (Filter.Eventually.of_forall fun t => integral_nonneg fun ζ => by rw [hΛ]; positivity)
      hgint
      ((ae_restrict_mem measurableSet_Ioc).mono (fun t ht => hkey t ht))
    refine hmono.trans (le_of_eq ?_)
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      integral_rpow_neg_half]
    ring
  -- Step 4: assembly
  have hmain : ∫ ζ in B, |v (p + ζ) - v q|
      ≤ (a + d) * (2 * (4 * a ^ 2) ^ (3 / 4 : ℝ) * G4 ^ (1 / 4 : ℝ)) := by
    calc ∫ ζ in B, |v (p + ζ) - v q|
        ≤ ∫ ζ in B, (a + d) * ∫ t in (0 : ℝ)..1, Λ ζ t := hstep1
      _ = (a + d) * ∫ ζ in B, (∫ t in (0 : ℝ)..1, Λ ζ t) := hstep2
      _ = (a + d) * ∫ t in (0 : ℝ)..1, ∫ ζ in B, Λ ζ t := by rw [hstep3]
      _ ≤ (a + d) * ((4 * a ^ 2) ^ (3 / 4 : ℝ) * G4 ^ (1 / 4 : ℝ) * 2) :=
          mul_le_mul_of_nonneg_left h7 (by positivity)
      _ = (a + d) * (2 * (4 * a ^ 2) ^ (3 / 4 : ℝ) * G4 ^ (1 / 4 : ℝ)) := by ring
  calc (1 / (4 * a ^ 2)) * ∫ ζ in B, |v (p + ζ) - v q|
      ≤ (1 / (4 * a ^ 2)) *
          ((a + d) * (2 * (4 * a ^ 2) ^ (3 / 4 : ℝ) * G4 ^ (1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = Real.sqrt 2 * G4 ^ (1 / 4 : ℝ) * ((a + d) / Real.sqrt a) := arith_final ha

end Work.FTS.StrongLWP.Sobolev.HolderHalf

/-- The same statement under the name obtained when the (duplicated) `namespace` line of the
original skeleton is kept; it is a definitional copy of
`Work.FTS.StrongLWP.Sobolev.HolderHalf.leg_two_bound` and is provided only for compatibility. -/
theorem leg_two_bound {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (hseg : ∀ p z : ℝ × ℝ, v z - v p = ∫ t in (0 : ℝ)..1, (fderiv ℝ v (p + t • (z - p))) (z - p))
    (p q : ℝ × ℝ) {a : ℝ} (ha : 0 < a) :
    (1 / (4 * a ^ 2)) * ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, |v (p + ζ) - v q|
      ≤ Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)
        * ((a + dist p q) / Real.sqrt a) :=
  _root_.Work.FTS.StrongLWP.Sobolev.HolderHalf.Work.FTS.StrongLWP.Sobolev.HolderHalf.leg_two_bound
    hv hc hseg p q ha

end Work.FTS.StrongLWP.Sobolev.HolderHalf
