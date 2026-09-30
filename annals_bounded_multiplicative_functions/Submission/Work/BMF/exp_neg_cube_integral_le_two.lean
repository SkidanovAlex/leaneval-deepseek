import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open MeasureTheory Set Filter

/-- The improper integral `∫_0^∞ exp(-w³) dw` is at most `2`.  We split at `1`: on `(0,1]` the
integrand is bounded by `1`, and on `(1,∞)` it is bounded by `exp(-w)`, whose integral there is
`exp(-1) < 1`. -/
lemma exp_neg_cube_integral_le_two :
    ∫ w in Set.Ioi (0 : ℝ), Real.exp (-(w ^ 3)) ≤ 2 := by
  have hcont : Continuous (fun w : ℝ => Real.exp (-(w ^ 3))) := by fun_prop
  have hIoc : IntegrableOn (fun w : ℝ => Real.exp (-(w ^ 3))) (Set.Ioc (0:ℝ) 1) :=
    hcont.integrableOn_Ioc
  have hIoi : IntegrableOn (fun w : ℝ => Real.exp (-(w ^ 3))) (Set.Ioi (1:ℝ)) := by
    refine Integrable.mono' (g := fun w : ℝ => Real.exp (-w)) (integrableOn_exp_neg_Ioi 1)
      hcont.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall (fun w hw => ?_)
    have hw1 : (1:ℝ) ≤ w := le_of_lt hw
    have hcube : w ≤ w ^ 3 := by
      have := pow_le_pow_right₀ hw1 (by norm_num : (1:ℕ) ≤ 3)
      simpa using this
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hdisj : Disjoint (Set.Ioc (0:ℝ) 1) (Set.Ioi (1:ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.mpr hx')
  have hsplit : (∫ w in Set.Ioi (0:ℝ), Real.exp (-(w ^ 3)))
      = (∫ w in Set.Ioc (0:ℝ) 1, Real.exp (-(w ^ 3)))
        + (∫ w in Set.Ioi (1:ℝ), Real.exp (-(w ^ 3))) := by
    have h := setIntegral_union (f := fun w : ℝ => Real.exp (-(w ^ 3)))
      (s := Set.Ioc (0:ℝ) 1) (t := Set.Ioi (1:ℝ)) hdisj measurableSet_Ioi hIoc hIoi
    rwa [Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)] at h
  rw [hsplit]
  have hb1 : (∫ w in Set.Ioc (0:ℝ) 1, Real.exp (-(w ^ 3))) ≤ 1 := by
    have hvol : volume.real (Set.Ioc (0:ℝ) 1) = 1 := by
      rw [Measure.real_def, Real.volume_Ioc]
      norm_num
    have hs : volume (Set.Ioc (0:ℝ) 1) < ⊤ := by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    have hnorm := norm_setIntegral_le_of_norm_le_const (f := fun w : ℝ => Real.exp (-(w ^ 3)))
      (s := Set.Ioc (0:ℝ) 1) (C := 1) hs (fun w hw => by
        rw [Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
        have : 0 ≤ w ^ 3 := pow_nonneg (le_of_lt hw.1) 3
        linarith)
    have hnonneg : 0 ≤ ∫ w in Set.Ioc (0:ℝ) 1, Real.exp (-(w ^ 3)) :=
      integral_nonneg_of_ae (Eventually.of_forall fun w => Real.exp_nonneg _)
    rw [Real.norm_of_nonneg hnonneg, hvol, mul_one] at hnorm
    exact hnorm
  have hb2 : (∫ w in Set.Ioi (1:ℝ), Real.exp (-(w ^ 3))) ≤ Real.exp (-1) := by
    have hg : IntegrableOn (fun w : ℝ => Real.exp (-w)) (Set.Ioi (1:ℝ)) :=
      integrableOn_exp_neg_Ioi 1
    have hmono := setIntegral_mono_on hIoi hg measurableSet_Ioi (fun w hw => by
      have hw1 : (1:ℝ) ≤ w := le_of_lt hw
      have hcube : w ≤ w ^ 3 := by
        have := pow_le_pow_right₀ hw1 (by norm_num : (1:ℕ) ≤ 3)
        simpa using this
      exact Real.exp_le_exp.mpr (by linarith))
    rwa [integral_exp_neg_Ioi] at hmono
  have hexp : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  linarith

end Work.BMF
