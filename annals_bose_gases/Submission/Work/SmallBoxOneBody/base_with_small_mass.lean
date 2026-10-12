import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.SmallBoxOneBody.prof_support
import Submission.Work.SmallBoxOneBody.uncurry_prof_smooth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A bump-function base on `ℝ³` all of whose radius-`2` members have tiny `L²` mass

We build a `ContDiffBumpBase` on `ℝ³` out of the profile `Prof` of `ProfDef.lean`.
The radius-`R` member of the family is `y ↦ Prof ((‖y‖-1)/(R-1))`, which is `1` on
the closed unit ball, positive exactly on `B(0,R)` and `0` outside.  Because `Prof`
plunges to `e^{-50}` as soon as its argument exceeds `1/50`, the `L²` mass of the
radius-`2` member is at most `(16/3)((51/50)³ + 8e^{-100}) < 32/3`, so a factor
`1/64` of it is `< 1/6`.
-/

namespace Work.SmallBoxOneBody

open MeasureTheory Metric Set
open scoped ContDiff

/-- The family of profiles indexed by the outer radius `R`: the radius-`R` member is
`y ↦ Prof ((‖y‖-1)/(R-1))`. -/
noncomputable def baseToFun (R : ℝ) (y : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Prof ((‖y‖ - 1) / (R - 1))

lemma baseToFun_nonneg (R : ℝ) (y : EuclideanSpace ℝ (Fin 3)) : 0 ≤ baseToFun R y :=
  Prof_nonneg _

lemma baseToFun_le_one (R : ℝ) (y : EuclideanSpace ℝ (Fin 3)) : baseToFun R y ≤ 1 :=
  Prof_le_one _

lemma baseToFun_neg (R : ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    baseToFun R (-y) = baseToFun R y := by
  simp [baseToFun]

lemma baseToFun_eq_one (R : ℝ) (hR : 1 < R) (y : EuclideanSpace ℝ (Fin 3))
    (hy : ‖y‖ ≤ 1) : baseToFun R y = 1 :=
  Prof_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

/-- The volume of a closed ball in `ℝ³`, in the crude form `(16/3) r³`. -/
lemma volume_closedBall_toReal_le (r : ℝ) (hr : 0 ≤ r) :
    (volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) r)).toReal ≤ 16 / 3 * r ^ 3 := by
  rw [Measure.addHaar_closedBall_eq_addHaar_ball
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) 0 r]
  rw [InnerProductSpace.volume_ball_of_dim_odd
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 * 1 + 1)]
  rw [finrank_euclideanSpace_fin]
  norm_num
  have e1 : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr
  have e2 : (ENNReal.ofReal (Real.pi * 4 / 3)).toReal = Real.pi * 4 / 3 :=
    ENNReal.toReal_ofReal (by positivity)
  rw [e1, e2]
  nlinarith [Real.pi_lt_four, mul_nonneg (mul_nonneg hr hr) hr]

/-- The same bound for the open ball. -/
lemma volume_ball_toReal_le (r : ℝ) (hr : 0 ≤ r) :
    (volume (ball (0 : EuclideanSpace ℝ (Fin 3)) r)).toReal ≤ 16 / 3 * r ^ 3 := by
  rw [InnerProductSpace.volume_ball_of_dim_odd
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 * 1 + 1)]
  rw [finrank_euclideanSpace_fin]
  norm_num
  have e1 : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr
  have e2 : (ENNReal.ofReal (Real.pi * 4 / 3)).toReal = Real.pi * 4 / 3 :=
    ENNReal.toReal_ofReal (by positivity)
  rw [e1, e2]
  nlinarith [Real.pi_lt_four, mul_nonneg (mul_nonneg hr hr) hr]

/-- The radius-`2` member has `L²` mass `< 32/3`. -/
lemma baseToFun_two_integral_lt :
    ∫ y : EuclideanSpace ℝ (Fin 3), (baseToFun 2 y) ^ 2 < (32 : ℝ) / 3 := by
  have hbase : (fun y : EuclideanSpace ℝ (Fin 3) => (baseToFun 2 y) ^ 2)
      = fun y : EuclideanSpace ℝ (Fin 3) => (Prof (‖y‖ - 1)) ^ 2 := by
    funext y; norm_num [baseToFun]
  rw [hbase]
  -- the dominating function
  have hAint : Integrable
      ((closedBall (0 : EuclideanSpace ℝ (Fin 3)) (51 / 50)).indicator (fun _ => (1 : ℝ)))
      volume := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const (ne_of_lt (isCompact_closedBall 0 (51 / 50)).measure_lt_top)
  have hBint : Integrable
      ((ball (0 : EuclideanSpace ℝ (Fin 3)) 2).indicator (fun _ => (1 : ℝ))) volume := by
    rw [integrable_indicator_iff measurableSet_ball]
    exact integrableOn_const (ne_of_lt (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2).measure_lt_top))
  have hFcont : Continuous (fun y : EuclideanSpace ℝ (Fin 3) => (Prof (‖y‖ - 1)) ^ 2) :=
    ((Prof_smooth.continuous.comp (continuous_norm.sub continuous_const))).pow 2
  have hFsupp : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin 3) => (Prof (‖y‖ - 1)) ^ 2) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2)
    intro y hy
    have h2 : 2 ≤ ‖y‖ := by
      by_contra h
      push Not at h
      exact hy (by rw [mem_closedBall, dist_zero_right]; exact h.le)
    rw [Prof_of_one_le (by linarith : (1 : ℝ) ≤ ‖y‖ - 1)]
    norm_num
  have hFint : Integrable (fun y : EuclideanSpace ℝ (Fin 3) => (Prof (‖y‖ - 1)) ^ 2)
      volume := hFcont.integrable_of_hasCompactSupport hFsupp
  have hGint : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (51 / 50)).indicator (fun _ => (1 : ℝ)) y
        + Real.exp (-100) * (ball (0 : EuclideanSpace ℝ (Fin 3)) 2).indicator (fun _ => (1 : ℝ)) y)
      volume :=
    hAint.add (hBint.const_mul _)
  -- pointwise domination
  have hFG : ∀ y : EuclideanSpace ℝ (Fin 3),
      (Prof (‖y‖ - 1)) ^ 2 ≤
        (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (51 / 50)).indicator (fun _ => (1 : ℝ)) y
          + Real.exp (-100) *
            (ball (0 : EuclideanSpace ℝ (Fin 3)) 2).indicator (fun _ => (1 : ℝ)) y := by
    intro y
    have hexp : (Real.exp (-50)) ^ 2 = Real.exp (-100) := by
      rw [sq, ← Real.exp_add]; norm_num
    have hAnonneg : 0 ≤
        (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (51 / 50)).indicator (fun _ => (1 : ℝ)) y :=
      indicator_nonneg (fun _ _ => zero_le_one) y
    have hBnonneg : 0 ≤
        (ball (0 : EuclideanSpace ℝ (Fin 3)) 2).indicator (fun _ => (1 : ℝ)) y :=
      indicator_nonneg (fun _ _ => zero_le_one) y
    rcases lt_or_ge (‖y‖) (51 / 50) with h | h
    · have hyA : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) (51 / 50) := by
        rw [mem_closedBall, dist_zero_right]; exact h.le
      have h1 := Set.indicator_of_mem hyA (fun _ => (1 : ℝ))
      have h3 : (Prof (‖y‖ - 1)) ^ 2 ≤ 1 := by
        nlinarith [Prof_nonneg (‖y‖ - 1), Prof_le_one (‖y‖ - 1)]
      rw [h1]
      nlinarith [Real.exp_pos (-100)]
    · rcases lt_or_ge (‖y‖) 2 with h2 | h2
      · have hyB : y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 2 := by
          rw [mem_ball, dist_zero_right]; exact h2
        have h1 := Set.indicator_of_mem hyB (fun _ => (1 : ℝ))
        have h4 : (Prof (‖y‖ - 1)) ^ 2 ≤ (Real.exp (-50)) ^ 2 := by
          nlinarith [Prof_exp_bound (s := ‖y‖ - 1) (by linarith), Prof_nonneg (‖y‖ - 1),
            Real.exp_pos (-50)]
        rw [h1]
        nlinarith [h4, hexp, hAnonneg]
      · have h1 : (Prof (‖y‖ - 1)) ^ 2 = 0 := by
          rw [Prof_of_one_le (by linarith : (1 : ℝ) ≤ ‖y‖ - 1)]; norm_num
        rw [h1]
        nlinarith [hAnonneg, hBnonneg, Real.exp_pos (-100)]
  have hmono := integral_mono hFint hGint hFG
  have hGval : ∫ y : EuclideanSpace ℝ (Fin 3),
        ((closedBall (0 : EuclideanSpace ℝ (Fin 3)) (51 / 50)).indicator (fun _ => (1 : ℝ)) y
          + Real.exp (-100) *
            (ball (0 : EuclideanSpace ℝ (Fin 3)) 2).indicator (fun _ => (1 : ℝ)) y)
      = volume.real (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (51 / 50))
        + Real.exp (-100) * volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) 2) := by
    rw [integral_add hAint (hBint.const_mul _), integral_const_mul,
      integral_indicator_const (1 : ℝ) measurableSet_closedBall,
      integral_indicator_const (1 : ℝ) measurableSet_ball]
    simp [smul_eq_mul]
  have hvolA := volume_closedBall_toReal_le (51 / 50) (by norm_num)
  have hvolB := volume_ball_toReal_le 2 (by norm_num)
  have hexp101 : Real.exp (-100) ≤ 1 / 101 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (a := 101) (b := Real.exp 100) (by norm_num)
      (by linarith [Real.add_one_le_exp 100])
  calc ∫ y : EuclideanSpace ℝ (Fin 3), (Prof (‖y‖ - 1)) ^ 2
      ≤ volume.real (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (51 / 50))
        + Real.exp (-100) * volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) 2) := by
        rw [hGval] at hmono; exact hmono
    _ = (volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (51 / 50))).toReal
        + Real.exp (-100) * (volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 2)).toReal := by
        rw [Measure.real_def, Measure.real_def]
    _ ≤ 16 / 3 * (51 / 50) ^ 3 + Real.exp (-100) * (16 / 3 * 2 ^ 3) := by
        nlinarith [hvolA, hvolB, Real.exp_pos (-100)]
    _ < (32 : ℝ) / 3 := by
        nlinarith [hexp101]

/-- The uncurried family is `C^∞` on `R > 1`. -/
lemma baseToFun_uncurry_smooth :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry baseToFun)
      (Set.Ioi (1 : ℝ) ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3)))) :=
  uncurry_prof_smooth

/-- The radius-`R` member is supported exactly on `B(0,R)`. -/
lemma baseToFun_support (R : ℝ) (hR : 1 < R) :
    Function.support (baseToFun R) = Metric.ball 0 R :=
  prof_support R hR

theorem base_with_small_mass :
    ∃ X : ContDiffBumpBase (EuclideanSpace ℝ (Fin 3)),
      (1 / 64 : ℝ) * ∫ y, (X.toFun 2 y) ^ 2 < (1 : ℝ) / 6 := by
  refine ⟨{ toFun := baseToFun
            mem_Icc := fun R y => ⟨baseToFun_nonneg R y, baseToFun_le_one R y⟩
            symmetric := baseToFun_neg
            smooth := baseToFun_uncurry_smooth
            eq_one := baseToFun_eq_one
            support := baseToFun_support }, ?_⟩
  have hI : ∫ y : EuclideanSpace ℝ (Fin 3), (baseToFun 2 y) ^ 2 < (32 : ℝ) / 3 :=
    baseToFun_two_integral_lt
  calc (1 / 64 : ℝ) * ∫ y, (baseToFun 2 y) ^ 2
      < (1 / 64 : ℝ) * ((32 : ℝ) / 3) := mul_lt_mul_of_pos_left hI (by norm_num)
    _ = (1 : ℝ) / 6 := by norm_num

end Work.SmallBoxOneBody
