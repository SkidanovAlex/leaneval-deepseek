import Mathlib
import Submission.Commons.MeasureTheory.IntervalIntegral.integral_indicator_Ici
import Submission.Commons.MeasureTheory.IntervalIntegral.integrableOn_div_floor
import Submission.Commons.MeasureTheory.IntervalIntegral.integrableOn_sum_Icc_floor
import Submission.Commons.Analysis.Floor.sum_Icc_floor_eq
import Submission.Commons.Analysis.Floor.integral_sum_Icc_floor

open MeasureTheory intervalIntegral
open scoped BigOperators

/-
# The paper's Definition `integrated lcm` (Calegari–Dimitrov–Tang, §"The cost of an integration")

The paper defines the "cost of an integration"
```
I_u^v(w) = ∫_{min(u,1)}^1 (t-w)⁺ dt
        + ∫_{max(u,1)}^v (Σ_{h=1}^{⌊(t-1)/max(1,w)⌋} 1/h) dt
        + ∫_{max(u,1)}^v (t/⌊(t+max(0,w-1))/max(1,w)⌋ - w)⁺ dt
```
for `0 ≤ max(u,1) ≤ v` and `w ≤ v`; it is the integral of the *model* function `modelFun w` of
Lemma `lcm-2` (2): with `n = ⌊tD⌋`, `k = D`, `l = ⌊wD⌋` the right-hand side of Lemma `lcm-2` (2)
divided by `D` is
`H h₀ + (n/D/⌊(n+(l-k)⁺)/max(k,l)⌋ - w)⁺` with `h₀ = ⌊(n-k)/max(k,l)⌋ = ⌊(t-1)/max(1,w)⌋` up to
`O(1)` (the floor arguments differ by `O(1/D)`) and `⌊(n+(l-k)⁺)/max(k,l)⌋` likewise matching
`⌊(t+max(0,w-1))/max(1,w)⌋ · D` up to `O(1)`.

Main result: **`integratedLcm_zero_left`**: for `1 ≤ v`,
`I_0^v(w) = ∫_0^v modelFun w`.

NB (warned about in the docstring of `modelFun`): the analogue `I_u^v(w) = ∫_{min(u,1)}^v modelFun w`
holds only for `u ≤ 1`; for `u ≥ 1` the region `[1,u]` is dropped by the definition — it is exactly
the region where the paper uses the *trivial* estimate for the primes `p ≤ ξD` instead of
Lemma `lcm-2`.  For `u ≥ 1` one has `I_u^v(w) = ∫_u^v modelFun w`, again by the definition.
-/

namespace Submission.CDT.IntegratedLcm

noncomputable def harmonicFun (w : ℝ) : ℝ → ℝ :=
  fun t => ∑ h ∈ Finset.Icc 1 ⌊(t - 1) / max 1 w⌋₊, (1:ℝ)/h

noncomputable def correctionFun (w : ℝ) : ℝ → ℝ :=
  fun t => max (t / ((⌊(t + max 0 (w - 1)) / max 1 w⌋₊ : ℕ) : ℝ) - w) 0

noncomputable def modelFun (w : ℝ) : ℝ → ℝ := fun t =>
  if t ≤ 1 then max (t - w) 0 else harmonicFun w t + correctionFun w t

noncomputable def integratedLcm (u v w : ℝ) : ℝ :=
  (∫ t in min u 1..1, max (t - w) 0)
  + (∫ t in max u 1..v, harmonicFun w t)
  + (∫ t in max u 1..v, correctionFun w t)

theorem modelFun_of_le_one (w t : ℝ) (ht : t ≤ 1) : modelFun w t = max (t - w) 0 := if_pos ht

theorem modelFun_of_lt (w t : ℝ) (ht : 1 < t) :
    modelFun w t = harmonicFun w t + correctionFun w t := if_neg (not_le.mpr ht)

theorem harmonicFun_nonneg (w t : ℝ) : 0 ≤ harmonicFun w t := by
  refine Finset.sum_nonneg fun h hh => ?_
  rw [Finset.mem_Icc] at hh
  have : (0:ℝ) < h := by exact_mod_cast hh.1
  positivity

theorem correctionFun_nonneg (w t : ℝ) : 0 ≤ correctionFun w t := le_max_right _ _

theorem modelFun_nonneg (w t : ℝ) : 0 ≤ modelFun w t := by
  rw [modelFun]
  split
  · exact le_max_right _ _
  · exact add_nonneg (harmonicFun_nonneg w t) (correctionFun_nonneg w t)

theorem integrableOn_harmonicFun (w v : ℝ) :
    IntegrableOn (harmonicFun w) (Set.Ioc 1 v) volume := by
  refine (Commons.MeasureTheory.IntervalIntegral.integrableOn_sum_Icc_floor
    (fun h => (1:ℝ)/h) (B := max 1 w) (v := v) (by positivity)).mono_set ?_
  exact fun t ht => ⟨le_of_lt ht.1, ht.2⟩

theorem integrableOn_correctionFun (w v : ℝ) :
    IntegrableOn (correctionFun w) (Set.Ioc 1 v) volume := by
  refine (Commons.MeasureTheory.IntervalIntegral.integrableOn_div_floor
    (max 0 (w - 1)) w (B := max 1 w) (by positivity) v).mono_set ?_
  exact fun t ht => ⟨le_of_lt ht.1, ht.2⟩

theorem intervalIntegrable_harmonicFun (w v : ℝ) (hv : 1 ≤ v) :
    IntervalIntegrable (harmonicFun w) volume 1 v := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hv]
  exact integrableOn_harmonicFun w v

theorem intervalIntegrable_correctionFun (w v : ℝ) (hv : 1 ≤ v) :
    IntervalIntegrable (correctionFun w) volume 1 v := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hv]
  exact integrableOn_correctionFun w v

theorem integrableOn_modelFun_zero_one (w : ℝ) :
    IntegrableOn (modelFun w) (Set.uIoc 0 1) volume := by
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have h1 : IntegrableOn (fun t : ℝ => max (t - w) 0) (Set.Icc 0 1) volume :=
    Continuous.integrableOn_Icc (by fun_prop)
  refine (h1.mono_set (fun t ht => ⟨ht.1.le, ht.2⟩)).congr_fun ?_ measurableSet_Ioc
  intro t ht
  exact (modelFun_of_le_one w t ht.2).symm

theorem integrableOn_modelFun_one (w v : ℝ) :
    IntegrableOn (modelFun w) (Set.Ioc 1 v) volume := by
  have h23 : IntegrableOn (fun t => harmonicFun w t + correctionFun w t) (Set.Ioc 1 v) volume :=
    (integrableOn_harmonicFun w v).add (integrableOn_correctionFun w v)
  refine h23.congr_fun ?_ measurableSet_Ioc
  intro t ht
  exact (modelFun_of_lt w t ht.1).symm

/-- For `u = 0` the paper's `integrated lcm` is the integral of the single model function over
`[0, v]`. -/
theorem integratedLcm_zero_left (v w : ℝ) (hv : 1 ≤ v) :
    integratedLcm 0 v w = ∫ t in 0..v, modelFun w t := by
  have hmax : max (0:ℝ) 1 = 1 := max_eq_right (by norm_num)
  have hmin : min (0:ℝ) 1 = 0 := min_eq_left (by norm_num)
  have hf2 : IntervalIntegrable (harmonicFun w) volume 1 v := intervalIntegrable_harmonicFun w v hv
  have hf3 : IntervalIntegrable (correctionFun w) volume 1 v :=
    intervalIntegrable_correctionFun w v hv
  have h01 : IntervalIntegrable (modelFun w) volume 0 1 := by
    rw [intervalIntegrable_iff]; exact integrableOn_modelFun_zero_one w
  have h1v : IntervalIntegrable (modelFun w) volume 1 v := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hv]; exact integrableOn_modelFun_one w v
  have hcongr1 : (∫ t in 0..1, modelFun w t) = ∫ t in 0..1, max (t - w) 0 :=
    integral_congr fun t ht => by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      exact modelFun_of_le_one w t ht.2
  have hcongr2 : (∫ t in 1..v, modelFun w t)
      = ∫ t in 1..v, (harmonicFun w t + correctionFun w t) :=
    integral_congr_ae (Filter.Eventually.of_forall fun t ht => by
      rw [Set.uIoc_of_le hv] at ht
      exact modelFun_of_lt w t ht.1)
  have hadd : (∫ t in 0..1, modelFun w t) + (∫ t in 1..v, modelFun w t)
      = ∫ t in 0..v, modelFun w t := integral_add_adjacent_intervals h01 h1v
  have hIL : integratedLcm 0 v w
      = (∫ t in 0..1, max (t - w) 0) + (∫ t in 1..v, harmonicFun w t)
        + (∫ t in 1..v, correctionFun w t) := by
    unfold integratedLcm
    rw [hmin, hmax]
  rw [hcongr1, hcongr2, integral_add hf2 hf3] at hadd
  linarith [hadd]

/-- `I_0^v(w) ≥ 0`. -/
theorem integratedLcm_zero_left_nonneg (v w : ℝ) (hv : 1 ≤ v) : 0 ≤ integratedLcm 0 v w := by
  rw [integratedLcm_zero_left v w hv]
  exact intervalIntegral.integral_nonneg (le_trans zero_le_one hv) fun t _ => modelFun_nonneg w t

/-- The harmonic part of `I` evaluated in closed form: the integral of `Σ_{h ≤ ⌊(t-1)/B⌋} 1/h` over
`[1,v]` is the finite sum `Σ_{h ≤ ⌊(v-1)/B⌋} (1/h)·(v - max(1, 1+hB))⁺` with `B = max 1 w`.  This
completes the evaluation of the paper's Definition `integrated lcm`. -/
theorem integral_harmonicFun (v w : ℝ) (hv : 1 ≤ v) :
    (∫ t in 1..v, harmonicFun w t)
      = ∑ h ∈ Finset.Icc 1 ⌊(v - 1) / max 1 w⌋₊,
          (1/(h:ℝ)) * max (v - max 1 (1 + (h:ℝ) * max 1 w)) 0 := by
  unfold harmonicFun
  exact Commons.Analysis.Floor.integral_sum_Icc_floor (fun h => (1:ℝ)/h)
    (B := max 1 w) (by positivity) hv

end Submission.CDT.IntegratedLcm
