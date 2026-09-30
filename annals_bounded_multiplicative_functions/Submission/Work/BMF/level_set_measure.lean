import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset Real MeasureTheory

/-- Level-set measure bound: if a nonnegative measurable `F ≤ 3` satisfies
`η * X ≤ ∫_{X}^{2X} F` with `η > 0` and `X ≥ 0`, then the set
`{x | η/2 ≤ F x} ∩ (X, 2X]` has measure at least `η * X / 6`.

The proof decomposes `(X, 2X]` into the region where `F ≥ η/2` (where `F ≤ 3`)
and its complement (where `F < η/2`). -/
theorem level_set_measure (F : ℝ → ℝ) (η X : ℝ) (hFmeas : Measurable F) (hη : 0 < η)
    (hX0 : 0 ≤ X) (hFnn : ∀ x, 0 ≤ F x) (hFle : ∀ x, F x ≤ 3)
    (hint : η * X ≤ ∫ x in X..(2 * X), F x) :
    η * X / 6 ≤ (volume ({x | η / 2 ≤ F x} ∩ Set.Ioc X (2 * X))).toReal := by
  have hle : X ≤ 2 * X := by linarith
  set t : Set ℝ := {x | η / 2 ≤ F x} with ht_def
  set s : Set ℝ := Set.Ioc X (2 * X) with hs_def
  set A : Set ℝ := {x | η / 2 ≤ F x} ∩ Set.Ioc X (2 * X) with hA_def
  have ht_meas : MeasurableSet t := hFmeas measurableSet_Ici
  have hs_meas : MeasurableSet s := measurableSet_Ioc
  have hA_meas : MeasurableSet A := by rw [hA_def]; exact ht_meas.inter hs_meas
  have hs_lt : volume s < ⊤ := by rw [hs_def, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hsv : volume s = ENNReal.ofReal X := by rw [hs_def, Real.volume_Ioc]; congr 1; ring
  have hFint : IntegrableOn F s volume := by
    refine IntegrableOn.of_bound hs_lt (hFmeas.aestronglyMeasurable.restrict) 3 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn x)]; exact hFle x
  have hAsub : A ⊆ s := by rw [hA_def, hs_def]; exact Set.inter_subset_right
  have hA_lt : volume A < ⊤ := lt_of_le_of_lt (measure_mono hAsub) hs_lt
  have hst : s ∩ t = A := by rw [hA_def, hs_def, ht_def, Set.inter_comm]
  have hdecomp : (∫ x in A, F x) + (∫ x in s \ t, F x) = ∫ x in s, F x := by
    have := integral_inter_add_sdiff₀ (μ := volume) ht_meas.nullMeasurableSet hFint
    rw [← hst]; exact this
  have hAb : ∫ x in A, F x ≤ 3 * (volume A).toReal := by
    have h := setIntegral_mono_on (μ := volume) (hFint.mono_set hAsub)
        (integrableOn_const (C := (3:ℝ))) hA_meas (fun x _ => hFle x)
    rw [setIntegral_const, Measure.real_def, smul_eq_mul] at h
    linarith [h]
  have hBt : ∫ x in s \ t, F x ≤ (η / 2) * (volume (s \ t)).toReal := by
    have hst_meas : MeasurableSet (s \ t) := hs_meas.diff ht_meas
    have hst_lt : volume (s \ t) < ⊤ := lt_of_le_of_lt (measure_mono Set.sdiff_subset) hs_lt
    have hFi : IntegrableOn F (s \ t) volume := hFint.mono_set Set.sdiff_subset
    have h := setIntegral_mono_on (μ := volume) hFi
        (integrableOn_const (C := η / 2)) hst_meas (fun x hx => ?_)
    · rw [setIntegral_const, Measure.real_def, smul_eq_mul] at h
      linarith [h]
    · have hxnt : ¬ (η / 2 ≤ F x) := by
        intro hcon; exact hx.2 (by rw [ht_def]; exact hcon)
      exact le_of_lt (lt_of_not_ge hxnt)
  have hBvol : (volume (s \ t)).toReal ≤ X := by
    have hb : volume (s \ t) ≤ ENNReal.ofReal X :=
      le_trans (measure_mono Set.sdiff_subset) (le_of_eq hsv)
    have := ENNReal.toReal_mono (show (ENNReal.ofReal X) ≠ ⊤ by simp) hb
    rwa [ENNReal.toReal_ofReal hX0] at this
  have hp : η * X ≤ 3 * (volume A).toReal + (η / 2) * (volume (s \ t)).toReal := by
    calc η * X ≤ ∫ x in X..(2 * X), F x := hint
      _ = ∫ x in s, F x := by rw [hs_def, intervalIntegral.integral_of_le hle]
      _ = (∫ x in A, F x) + (∫ x in s \ t, F x) := hdecomp.symm
      _ ≤ 3 * (volume A).toReal + (η / 2) * (volume (s \ t)).toReal := add_le_add hAb hBt
  have h3 : 3 * (volume A).toReal + (η / 2) * (volume (s \ t)).toReal ≤ 3 * (volume A).toReal + η * X / 2 := by
    have hη2 : (0:ℝ) ≤ η / 2 := by linarith
    have hb := mul_le_mul_of_nonneg_left hBvol hη2
    rw [show (η/2) * X = η * X / 2 by ring] at hb
    linarith
  have h4 : η * X / 6 ≤ (volume A).toReal := by
    have := le_trans hp h3
    linarith
  exact h4

end Work.BMF
