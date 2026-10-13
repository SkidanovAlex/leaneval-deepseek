import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.H2.Transport3Aux.num_int_1d_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `sin(2θ)`-weighted Hardy inequality on `[0,π/4]`, weak hypotheses

The statement is the one of `Work.FTS.H2.Transport3Aux.hardy_half_a`, but the function `f` is
only assumed to be continuous on `[0,π/2]` and differentiable on the *open* interval, with a
bounded derivative there (`|f'| ≤ C`); no continuity of `f'` is required.

The proof is the one of `hardy_half_a`: the power-weighted Hardy inequality with boundary term
`Work.FTS.H2.Transport3Aux.hardy_power_weak` (proved in `num_int_1d_aux` for exactly these weak
hypotheses), together with Jordan's inequality `(4/π)θ ≤ sin(2θ) ≤ 1` on `[0,π/4]`.  The only
extra input needed is that `θ ↦ (deriv f θ)^2 * w(θ)` is interval integrable for the two weights
`w = θ^{β+1}` and `w = sin(2θ)^{1-β}`, which follows by domination since `deriv f` is measurable
(`measurable_deriv`) and bounded on the open interval.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux.HW

set_option maxHeartbeats 1000000

/-- Interval integrability by domination on `(0,b)`: if `|G| ≤ D` on `(0,b)` for an interval
integrable `D`, and `G` is a.e. strongly measurable there, then `G` is interval integrable on
`[0,b]`.  This is the weak-hypothesis replacement for `ContinuousOn → IntervalIntegrable`
(a merely bounded `deriv f` need not be continuous, but it is always measurable). -/
private theorem intIntegrable_of_abs_le {b : ℝ} (hb : 0 ≤ b) {G D : ℝ → ℝ}
    (hD : IntervalIntegrable D volume 0 b)
    (hmeas : AEStronglyMeasurable G (volume.restrict (Set.Ioo (0 : ℝ) b)))
    (hbound : ∀ t ∈ Set.Ioo (0 : ℝ) b, |G t| ≤ D t) :
    IntervalIntegrable G volume 0 b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb, integrableOn_Ioc_iff_integrableOn_Ioo]
  have hD' : IntegrableOn D (Set.Ioo (0 : ℝ) b) volume := by
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
    exact hD
  refine Integrable.mono' hD' hmeas ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hbound)]
    with t ht
  simpa only [Real.norm_eq_abs] using ht

theorem hardy_half_a_weak {β C : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    (hder : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), HasDerivAt f (deriv f θ) θ)
    (hbdd : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), |deriv f θ| ≤ C) :
    (∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      ≤ 4 / β ^ 2 * (Real.pi / 4) ^ 2
          * (∫ θ in (0:ℝ)..(Real.pi / 4), (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
  have hbpos : (0:ℝ) < Real.pi / 4 := by positivity
  have hb0 : (0:ℝ) ≤ Real.pi / 4 := hbpos.le
  have hble : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hsub : Set.Icc (0:ℝ) (Real.pi / 4) ⊆ Set.Icc 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hcont' : ContinuousOn f (Set.Icc 0 (Real.pi / 4)) := hcont.mono hsub
  have hder' : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 4), HasDerivAt f (deriv f θ) θ :=
    fun θ hθ => hder θ ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hbdd' : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 4), |deriv f θ| ≤ C :=
    fun θ hθ => hbdd θ ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hcf : ContinuousOn (fun θ : ℝ => (f θ) ^ 2) (Set.uIcc 0 (Real.pi / 4)) := by
    rw [Set.uIcc_of_le hb0]
    exact hcont'.pow 2
  -- the power-weighted Hardy inequality on `[0,π/4]` with exponent `β-1`
  have hH := hardy_power_weak (a := β - 1) (b := Real.pi / 4) (by linarith) hbpos hcont' hder' hbdd'
  have hH' : (∫ t in (0:ℝ)..(Real.pi / 4), f t ^ 2 * t ^ (β - 1))
      ≤ (4 / β ^ 2) * (∫ t in (0:ℝ)..(Real.pi / 4), (deriv f t) ^ 2 * t ^ (β + 1))
        + (2 / β) * (Real.pi / 4) ^ β * (f (Real.pi / 4)) ^ 2 := by
    rw [show β - 1 + 1 = β from by ring, show β - 1 + 2 = β + 1 from by ring] at hH
    exact hH
  -- the two bounds on `(deriv f)²` on `(0,π/4)`
  have hK : (0:ℝ) ≤ max C 0 := le_max_right _ _
  have hdK : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 4), (deriv f θ) ^ 2 ≤ (max C 0) ^ 2 := by
    intro θ hθ
    have h1 : |deriv f θ| ≤ max C 0 := le_trans (hbdd' θ hθ) (le_max_left _ _)
    rw [sq_le_sq, abs_of_nonneg hK]
    exact h1
  -- integrability of the four integrands
  have hII_sin1 : IntervalIntegrable
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1)) volume 0 (Real.pi / 4) :=
    II_mul_cont (II_sin_rpow_interval (by linarith : -1 < β - 1) hb0 le_rfl hble) hcf
  have hII_pow1 : IntervalIntegrable
      (fun θ : ℝ => (f θ) ^ 2 * θ ^ (β - 1)) volume 0 (Real.pi / 4) :=
    II_mul_cont (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := Real.pi / 4)
      (r := β - 1) (by linarith)) hcf
  have hII_pow2 : IntervalIntegrable
      (fun θ : ℝ => (deriv f θ) ^ 2 * θ ^ (β + 1)) volume 0 (Real.pi / 4) := by
    refine intIntegrable_of_abs_le (D := fun t : ℝ => (max C 0) ^ 2 * t ^ (β + 1)) hb0
      ?_ ?_ ?_
    · exact ((intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := Real.pi / 4)
        (r := β + 1) (by linarith))).const_mul ((max C 0) ^ 2)
    · exact (((measurable_deriv f).pow_const 2).aestronglyMeasurable).mul
        (((continuousOn_id (s := Set.Ioo (0:ℝ) (Real.pi / 4))).rpow_const
          (fun t ht => Or.inl ht.1.ne')).aestronglyMeasurable measurableSet_Ioo)
    · intro t ht
      rw [abs_mul, abs_of_nonneg (sq_nonneg (deriv f t)),
        abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
      exact mul_le_mul_of_nonneg_right (hdK t ht) (Real.rpow_nonneg ht.1.le _)
  have hII_sin2 : IntervalIntegrable
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) volume 0 (Real.pi / 4) := by
    refine intIntegrable_of_abs_le
      (D := fun t : ℝ => (max C 0) ^ 2 * (Real.sin (2 * t)) ^ (1 - β)) hb0 ?_ ?_ ?_
    · exact ((II_sin_rpow_interval (p := 1 - β) (by linarith) hb0 le_rfl hble)).const_mul
        ((max C 0) ^ 2)
    · exact (((measurable_deriv f).pow_const 2).aestronglyMeasurable).mul
        ((((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
          (fun t ht => Or.inr (by linarith))).aestronglyMeasurable measurableSet_Ioo)
    · intro t ht
      have hs : (0:ℝ) ≤ (Real.sin (2 * t)) ^ (1 - β) :=
        Real.rpow_nonneg (le_of_lt (sin_two_pos_of_quarter ht)) _
      rw [abs_mul, abs_of_nonneg (sq_nonneg (deriv f t)), abs_of_nonneg hs]
      exact mul_le_mul_of_nonneg_right (hdK t ht) hs
  -- the two weight comparisons
  have hcmp1 : (∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      ≤ (4 / Real.pi) ^ (β - 1) * ∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2 * θ ^ (β - 1) := by
    have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 4),
        (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1)
          ≤ (4 / Real.pi) ^ (β - 1) * ((f θ) ^ 2 * θ ^ (β - 1)) := by
      intro θ hθ
      have h := sin_rpow_sub_le_theta (β := β) hβ1 hθ
      calc (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1)
          ≤ (f θ) ^ 2 * ((4 / Real.pi) ^ (β - 1) * θ ^ (β - 1)) :=
            mul_le_mul_of_nonneg_left h (sq_nonneg _)
        _ = (4 / Real.pi) ^ (β - 1) * ((f θ) ^ 2 * θ ^ (β - 1)) := by ring
    exact (intervalIntegral.integral_mono_on_of_le_Ioo hb0 hII_sin1
      (hII_pow1.const_mul _) hpt).trans_eq (intervalIntegral.integral_const_mul _ _)
  have hcmp2 : (∫ θ in (0:ℝ)..(Real.pi / 4), (deriv f θ) ^ 2 * θ ^ (β + 1))
      ≤ (Real.pi / 4) ^ (β + 1)
        * ∫ θ in (0:ℝ)..(Real.pi / 4), (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β) := by
    have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 4),
        (deriv f θ) ^ 2 * θ ^ (β + 1)
          ≤ (Real.pi / 4) ^ (β + 1)
            * ((deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) := by
      intro θ hθ
      have h := theta_rpow_le_sin_rpow (β := β) hβ.le hθ
      calc (deriv f θ) ^ 2 * θ ^ (β + 1)
          ≤ (deriv f θ) ^ 2 * ((Real.pi / 4) ^ (β + 1) * (Real.sin (2 * θ)) ^ (1 - β)) :=
            mul_le_mul_of_nonneg_left h (sq_nonneg _)
        _ = (Real.pi / 4) ^ (β + 1) * ((deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) := by
            ring
    exact (intervalIntegral.integral_mono_on_of_le_Ioo hb0 hII_pow2
      (hII_sin2.const_mul _) hpt).trans_eq (intervalIntegral.integral_const_mul _ _)
  -- assembly
  have hd : (0:ℝ) ≤ 4 / β ^ 2 := by positivity
  have hc1 : (0:ℝ) ≤ (4 / Real.pi) ^ (β - 1) := Real.rpow_nonneg (by positivity) _
  calc (∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      ≤ (4 / Real.pi) ^ (β - 1) * ∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2 * θ ^ (β - 1) :=
        hcmp1
    _ ≤ (4 / Real.pi) ^ (β - 1)
          * ((4 / β ^ 2) * (∫ θ in (0:ℝ)..(Real.pi / 4), (deriv f θ) ^ 2 * θ ^ (β + 1))
            + (2 / β) * (Real.pi / 4) ^ β * (f (Real.pi / 4)) ^ 2) :=
        mul_le_mul_of_nonneg_left hH' hc1
    _ ≤ (4 / Real.pi) ^ (β - 1)
          * ((4 / β ^ 2) * ((Real.pi / 4) ^ (β + 1)
              * (∫ θ in (0:ℝ)..(Real.pi / 4),
                  (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)))
            + (2 / β) * (Real.pi / 4) ^ β * (f (Real.pi / 4)) ^ 2) := by
        have hmid : (4 / β ^ 2) * (∫ θ in (0:ℝ)..(Real.pi / 4),
                (deriv f θ) ^ 2 * θ ^ (β + 1))
              + (2 / β) * (Real.pi / 4) ^ β * (f (Real.pi / 4)) ^ 2
            ≤ (4 / β ^ 2) * ((Real.pi / 4) ^ (β + 1)
                * (∫ θ in (0:ℝ)..(Real.pi / 4),
                    (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)))
              + (2 / β) * (Real.pi / 4) ^ β * (f (Real.pi / 4)) ^ 2 := by
          have h := mul_le_mul_of_nonneg_left hcmp2 hd
          linarith [h]
        exact mul_le_mul_of_nonneg_left hmid hc1
    _ = 4 / β ^ 2 * (Real.pi / 4) ^ 2
          * (∫ θ in (0:ℝ)..(Real.pi / 4),
              (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
        rw [show (4 / Real.pi) ^ (β - 1)
              * ((4 / β ^ 2) * ((Real.pi / 4) ^ (β + 1)
                  * (∫ θ in (0:ℝ)..(Real.pi / 4),
                      (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)))
                + (2 / β) * (Real.pi / 4) ^ β * (f (Real.pi / 4)) ^ 2)
            = (4 / Real.pi) ^ (β - 1) * (4 / β ^ 2) * (Real.pi / 4) ^ (β + 1)
                * (∫ θ in (0:ℝ)..(Real.pi / 4),
                    (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
              + (4 / Real.pi) ^ (β - 1) * (2 / β) * (Real.pi / 4) ^ β
                  * (f (Real.pi / 4)) ^ 2 from by ring,
          quarter_const_mul β, bdry_const_mul hβ.ne']

end Work.FTS.H2.Transport3Aux.HW
