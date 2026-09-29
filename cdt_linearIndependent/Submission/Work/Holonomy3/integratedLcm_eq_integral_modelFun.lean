import Mathlib
import Submission.Work.Holonomy3.model_deps

open MeasureTheory intervalIntegral
open scoped BigOperators
open Submission.CDT.IntegratedLcm

/-!
# The paper's integrated lcm cost `I_ξ^m(ξ)` as the integral of the model function

`Submission.CDTPlan.integratedLcm ξ m ξ` is by definition

`∫_{min ξ 1}^1 (t-ξ)⁺ dt + ∫_{max ξ 1}^m harmonicFun ξ t dt + ∫_{max ξ 1}^m correctionFun ξ t dt`

while the model function `modelFun ξ` of Lemma `lcm-2` is `max (t-ξ) 0` for `t ≤ 1` and
`harmonicFun ξ t + correctionFun ξ t` for `t > 1`.  Since `m ≥ 1`, the two are the same:

* for `ξ ≤ 1` the intervals `[ξ,1]` and `[1,m]` tile `[ξ,m]`, and on the two pieces `modelFun ξ`
  agrees with `(t-ξ)⁺` resp. with `harmonicFun ξ + correctionFun ξ`;
* for `1 ≤ ξ` the first integral is `∫_1^1 = 0` and the ranges of integration coincide,
  `modelFun ξ` and `harmonicFun ξ + correctionFun ξ` agreeing on `[ξ,m] ⊆ [1,∞)`.

The two branches of the *definition* of `modelFun` also agree at `t = 1` for every `ξ` (both equal
`(1-ξ)⁺`), which is why the closed intervals above may be used.
-/

namespace Submission.CDT.IntegratedLcm

/-- The two branches of the definition of `modelFun` agree at every `t ≥ 1` (at `t = 1` both
equal `max (1 - w) 0`). -/
theorem modelFun_eq_harm_add_cor_of_one_le (w t : ℝ) (ht : 1 ≤ t) :
    modelFun w t = harmonicFun w t + correctionFun w t := by
  rcases lt_or_eq_of_le ht with h | h
  · exact modelFun_of_lt w t h
  · subst h
    rw [modelFun_of_le_one w 1 le_rfl]
    have hh : harmonicFun w 1 = 0 := by simp [harmonicFun]
    rw [hh, zero_add]
    unfold correctionFun
    have hmax : max 0 (w - 1) = max 1 w - 1 := by
      rcases le_total 1 w with hw | hw
      · rw [max_eq_right (by linarith : (0:ℝ) ≤ w - 1), max_eq_right hw]
      · rw [max_eq_left (by linarith : w - 1 ≤ 0), max_eq_left hw]
        norm_num
    rw [hmax]
    have hfl : ⌊(1 + (max 1 w - 1)) / max 1 w⌋₊ = 1 := by
      rw [show 1 + (max 1 w - 1) = max 1 w by ring,
        div_self (ne_of_gt (lt_of_lt_of_le one_pos (le_max_left 1 w)))]
      exact Nat.floor_one
    rw [hfl]
    norm_num

theorem intervalIntegrable_modelFun_of_le_one (w a : ℝ) (ha : a ≤ 1) :
    IntervalIntegrable (modelFun w) volume a 1 := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le ha]
  have h1 : IntegrableOn (fun t : ℝ => max (t - w) 0) (Set.Icc a 1) volume :=
    Continuous.integrableOn_Icc (by fun_prop)
  refine (h1.mono_set (fun t ht => ⟨ht.1.le, ht.2⟩)).congr_fun ?_ measurableSet_Ioc
  intro t ht
  exact (modelFun_of_le_one w t ht.2).symm

theorem intervalIntegrable_modelFun_of_one_le (w v : ℝ) (hv : 1 ≤ v) :
    IntervalIntegrable (modelFun w) volume 1 v := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hv]
  exact integrableOn_modelFun_one w v

theorem intervalIntegrable_harmonicFun_of_one_le (w u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable (harmonicFun w) volume u v := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le huv]
  exact (integrableOn_harmonicFun w v).mono_set (fun t ht => ⟨lt_of_le_of_lt hu ht.1, ht.2⟩)

theorem intervalIntegrable_correctionFun_of_one_le (w u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable (correctionFun w) volume u v := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le huv]
  exact (integrableOn_correctionFun w v).mono_set (fun t ht => ⟨lt_of_le_of_lt hu ht.1, ht.2⟩)

end Submission.CDT.IntegratedLcm

namespace Work.Holonomy3

/-- The paper's integrated lcm cost `I_ξ^m(ξ)` equals the integral of the model function
`modelFun ξ` over `[ξ, m]`.  (For `ξ ≤ 1` the model function vanishes on `[0,ξ]` and equals
`max (t - ξ) 0` on `[ξ,1]`; for `ξ ≥ 1` it equals `harmonicFun ξ + correctionFun ξ` on `[ξ,m]`.
In both cases this is exactly the definition of `I_ξ^m(ξ)`.) -/
theorem integratedLcm_eq_integral_modelFun {m : ℕ} (hm : 0 < m) {ξ : ℝ} (h0 : 0 ≤ ξ)
    (hξm : ξ ≤ (m : ℝ)) :
    Submission.CDTPlan.integratedLcm ξ (m : ℝ) ξ
      = ∫ t in ξ..(m : ℝ), Submission.CDT.IntegratedLcm.modelFun ξ t := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : (1 : ℕ) ≤ m := by omega
    exact_mod_cast this
  change Submission.CDT.IntegratedLcm.integratedLcm ξ (m : ℝ) ξ
      = ∫ t in ξ..(m : ℝ), Submission.CDT.IntegratedLcm.modelFun ξ t
  rcases le_total ξ 1 with hξ1 | h1ξ
  · -- `ξ ≤ 1`: the intervals `[ξ,1]` and `[1,m]` tile `[ξ,m]`.
    have hmin : min ξ 1 = ξ := min_eq_left hξ1
    have hmax : max ξ 1 = 1 := max_eq_right hξ1
    have hLHS : Submission.CDT.IntegratedLcm.integratedLcm ξ (m : ℝ) ξ
        = (∫ t in ξ..1, max (t - ξ) 0)
          + (∫ t in 1..(m : ℝ), Submission.CDT.IntegratedLcm.harmonicFun ξ t)
          + (∫ t in 1..(m : ℝ), Submission.CDT.IntegratedLcm.correctionFun ξ t) := by
      rw [Submission.CDT.IntegratedLcm.integratedLcm, hmin, hmax]
    have hA : IntervalIntegrable (Submission.CDT.IntegratedLcm.modelFun ξ) volume ξ 1 :=
      Submission.CDT.IntegratedLcm.intervalIntegrable_modelFun_of_le_one ξ ξ hξ1
    have hB : IntervalIntegrable (Submission.CDT.IntegratedLcm.modelFun ξ) volume 1 (m : ℝ) :=
      Submission.CDT.IntegratedLcm.intervalIntegrable_modelFun_of_one_le ξ (m : ℝ) hm1
    have hadd : (∫ t in ξ..1, Submission.CDT.IntegratedLcm.modelFun ξ t)
        + (∫ t in 1..(m : ℝ), Submission.CDT.IntegratedLcm.modelFun ξ t)
        = ∫ t in ξ..(m : ℝ), Submission.CDT.IntegratedLcm.modelFun ξ t :=
      integral_add_adjacent_intervals hA hB
    have hc1 : (∫ t in ξ..1, Submission.CDT.IntegratedLcm.modelFun ξ t)
        = ∫ t in ξ..1, max (t - ξ) 0 :=
      integral_congr fun t ht => by
        rw [Set.uIcc_of_le hξ1] at ht
        exact Submission.CDT.IntegratedLcm.modelFun_of_le_one ξ t ht.2
    have hc2 : (∫ t in 1..(m : ℝ), Submission.CDT.IntegratedLcm.modelFun ξ t)
        = ∫ t in 1..(m : ℝ),
            (Submission.CDT.IntegratedLcm.harmonicFun ξ t
              + Submission.CDT.IntegratedLcm.correctionFun ξ t) :=
      integral_congr fun t ht => by
        rw [Set.uIcc_of_le hm1] at ht
        exact Submission.CDT.IntegratedLcm.modelFun_eq_harm_add_cor_of_one_le ξ t ht.1
    have hc3 : (∫ t in 1..(m : ℝ),
            (Submission.CDT.IntegratedLcm.harmonicFun ξ t
              + Submission.CDT.IntegratedLcm.correctionFun ξ t))
        = (∫ t in 1..(m : ℝ), Submission.CDT.IntegratedLcm.harmonicFun ξ t)
          + (∫ t in 1..(m : ℝ), Submission.CDT.IntegratedLcm.correctionFun ξ t) :=
      integral_add (Submission.CDT.IntegratedLcm.intervalIntegrable_harmonicFun ξ (m : ℝ) hm1)
        (Submission.CDT.IntegratedLcm.intervalIntegrable_correctionFun ξ (m : ℝ) hm1)
    have hthis : ∫ t in ξ..(m : ℝ), Submission.CDT.IntegratedLcm.modelFun ξ t
        = (∫ t in ξ..1, max (t - ξ) 0)
          + ((∫ t in 1..(m : ℝ), Submission.CDT.IntegratedLcm.harmonicFun ξ t)
            + (∫ t in 1..(m : ℝ), Submission.CDT.IntegratedLcm.correctionFun ξ t)) := by
      rw [← hadd, hc1, hc2, hc3]
    rw [hLHS, hthis]
    ring
  · -- `1 ≤ ξ`: the first integral is empty and `modelFun ξ = harmonicFun ξ + correctionFun ξ`.
    have hmin : min ξ 1 = 1 := min_eq_right h1ξ
    have hmax : max ξ 1 = ξ := max_eq_left h1ξ
    have hLHS : Submission.CDT.IntegratedLcm.integratedLcm ξ (m : ℝ) ξ
        = (∫ t in (1 : ℝ)..1, max (t - ξ) 0)
          + (∫ t in ξ..(m : ℝ), Submission.CDT.IntegratedLcm.harmonicFun ξ t)
          + (∫ t in ξ..(m : ℝ), Submission.CDT.IntegratedLcm.correctionFun ξ t) := by
      rw [Submission.CDT.IntegratedLcm.integratedLcm, hmin, hmax]
    have hz : (∫ t in (1 : ℝ)..1, max (t - ξ) 0) = 0 := integral_same
    have hR : (∫ t in ξ..(m : ℝ), Submission.CDT.IntegratedLcm.modelFun ξ t)
        = ∫ t in ξ..(m : ℝ),
            (Submission.CDT.IntegratedLcm.harmonicFun ξ t
              + Submission.CDT.IntegratedLcm.correctionFun ξ t) :=
      integral_congr fun t ht => by
        rw [Set.uIcc_of_le hξm] at ht
        exact Submission.CDT.IntegratedLcm.modelFun_eq_harm_add_cor_of_one_le ξ t
          (le_trans h1ξ ht.1)
    have hsp : (∫ t in ξ..(m : ℝ),
            (Submission.CDT.IntegratedLcm.harmonicFun ξ t
              + Submission.CDT.IntegratedLcm.correctionFun ξ t))
        = (∫ t in ξ..(m : ℝ), Submission.CDT.IntegratedLcm.harmonicFun ξ t)
          + (∫ t in ξ..(m : ℝ), Submission.CDT.IntegratedLcm.correctionFun ξ t) :=
      integral_add
        (Submission.CDT.IntegratedLcm.intervalIntegrable_harmonicFun_of_one_le ξ ξ (m : ℝ) h1ξ hξm)
        (Submission.CDT.IntegratedLcm.intervalIntegrable_correctionFun_of_one_le ξ ξ (m : ℝ) h1ξ hξm)
    rw [hLHS, hz, zero_add, hR, hsp]

end Work.Holonomy3
