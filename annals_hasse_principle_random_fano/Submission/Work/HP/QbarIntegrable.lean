import Mathlib
import Submission.Work.HP.QbarCoords

/-!
# Integrability of the coordinate integrand `qbCo`

The integrand `qbCo d` is bounded by `1` and vanishes outside the square `[-1,1]²`,
which has finite Lebesgue measure; hence it is integrable.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Work.HP

theorem qbarCo_integrable (d : ℕ) : Integrable (qbCo d) volume := by
  have hfun : qbCo d = fun p : ℝ × ℝ =>
      (if max (p.1 ^ 2) (p.2 ^ 2) ≤ 1 then (Real.sqrt (max (p.1 ^ 2) (p.2 ^ 2))) ^ d else 0) := rfl
  rw [hfun]
  set S : Set (ℝ × ℝ) := Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1 with hS
  have hSmeas : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hSfin : volume S < ⊤ := by
    change (volume.prod volume) S < ⊤
    rw [hS, Measure.prod_prod, Real.volume_Icc]
    exact WithTop.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hg : Integrable (S.indicator fun _ : ℝ × ℝ => (1:ℝ)) volume := by
    rw [integrable_indicator_iff hSmeas]
    exact integrableOn_const hSfin.ne
  refine hg.mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    apply Measurable.ite
    · exact measurableSet_le (by fun_prop) measurable_const
    · fun_prop
    · exact measurable_const
  · filter_upwards with p
    have key : (max (p.1 ^ 2) (p.2 ^ 2) ≤ 1) ↔ p ∈ S := by
      rw [hS, Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
      constructor
      · intro hc
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
          nlinarith [le_max_left (p.1^2) (p.2^2), le_max_right (p.1^2) (p.2^2), hc]
      · rintro ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩
        exact max_le (by nlinarith) (by nlinarith)
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, ite_eq_left (key.mpr hp)]
      have hmax1 : max (p.1^2) (p.2^2) ≤ 1 := key.mpr hp
      have hspos : 0 ≤ Real.sqrt (max (p.1^2) (p.2^2)) := Real.sqrt_nonneg _
      have hle1 : Real.sqrt (max (p.1^2) (p.2^2)) ≤ 1 := Real.sqrt_le_one.mpr hmax1
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hspos d)]
      exact pow_le_one₀ hspos hle1
    · have h0 : (if max (p.1 ^ 2) (p.2 ^ 2) ≤ 1 then (Real.sqrt (max (p.1 ^ 2) (p.2 ^ 2))) ^ d else 0) = 0 :=
        ite_eq_right (fun h => hp (key.mp h))
      rw [Set.indicator_of_notMem hp, h0, norm_zero]

end Work.HP
