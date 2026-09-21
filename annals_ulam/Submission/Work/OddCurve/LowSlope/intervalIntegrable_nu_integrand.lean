import Mathlib
import Submission.Work.OddRadon.intervalIntegrable_one_sub_sq_rpow

namespace Work.OddCurve.LowSlope

open MeasureTheory intervalIntegral Set

/-- The restricted Lebesgue measure on `(0,1]` is the restriction to the open interval `(0,1)`:
the two sets differ by the null set `{1}`. -/
lemma restrict_uIoc_zero_one_eq_restrict_Ioo :
    volume.restrict (uIoc (0 : ℝ) 1) = volume.restrict (Set.Ioo (0 : ℝ) 1) := by
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine Measure.restrict_congr_set (ae_eq_set.mpr ⟨?_, ?_⟩)
  · rw [Set.Ioc_sdiff_Ioo_same (by norm_num : (0 : ℝ) < 1)]
    exact measure_singleton 1
  · rw [Set.sdiff_eq_empty.mpr (Set.Ioo_subset_Ioc_self)]
    exact measure_empty

/-- `(1 - ν ^ 2) ^ r` is interval integrable on `(-1, 1)` whenever `-1 < r`: the two endpoint
singularities are `(1 ∓ ν) ^ r`, each integrable for `-1 < r`. -/
theorem intervalIntegrable_one_sub_sq_rpow_Ioo {r : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun ν : ℝ => (1 - ν ^ 2) ^ r) volume (-1 : ℝ) 1 := by
  set c : ℝ := max 1 (2 ^ r) with hc
  have hc1 : (1 : ℝ) ≤ c := le_max_left _ _
  have hc2 : (2 : ℝ) ^ r ≤ c := le_max_right _ _
  -- a uniform bound for `x ^ r` on `[1,2]`
  have hbound : ∀ x : ℝ, 1 ≤ x → x ≤ 2 → x ^ r ≤ c := by
    intro x hx1 hx2
    rcases le_or_gt 0 r with hr0 | hr0
    · exact le_trans (Real.rpow_le_rpow (by linarith) hx2 hr0) hc2
    · have h := Real.rpow_le_rpow_of_nonpos (x := (1 : ℝ)) (y := x) (z := r)
        (by norm_num) hx1 (le_of_lt hr0)
      rw [Real.one_rpow] at h
      exact le_trans h hc1
  have hleft : IntervalIntegrable (fun ν : ℝ => (1 - ν ^ 2) ^ r) volume (-1 : ℝ) 0 := by
    have hpow : IntervalIntegrable (fun ν : ℝ => (1 + ν) ^ r) volume (-1 : ℝ) 0 := by
      have h : IntervalIntegrable (fun ν : ℝ => (1 + ν) ^ r) volume (0 : ℝ) (-1 : ℝ) := by
        have h' := (Work.OddRadon.intervalIntegrable_one_sub_pow_rpow hr).comp_sub_left 0
        simpa using h'
      exact h.symm
    have hg : IntervalIntegrable (fun ν : ℝ => c * (1 + ν) ^ r) volume (-1 : ℝ) 0 :=
      hpow.const_mul c
    refine hg.mono_fun' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 0)]
      refine ((continuous_const.sub (continuous_id.pow 2)).continuousOn.rpow_const ?_)
      intro x hx
      rw [Set.mem_Ioc] at hx
      have hx2 : x ^ 2 < 1 := by nlinarith [hx.1, hx.2]
      refine Or.inl ?_
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
      linarith
    · refine ae_restrict_of_forall_mem measurableSet_uIoc (fun ν hν => ?_)
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 0), Set.mem_Ioc] at hν
      have h1 : 0 ≤ 1 - ν := by linarith [hν.2]
      have h2 : 0 ≤ 1 + ν := by linarith [hν.1]
      have hnn : 0 ≤ 1 - ν ^ 2 := by nlinarith [hν.1, hν.2]
      change ‖(1 - ν ^ 2) ^ r‖ ≤ c * (1 + ν) ^ r
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hnn r),
        show (1 : ℝ) - ν ^ 2 = (1 - ν) * (1 + ν) by ring,
        Real.mul_rpow h1 h2]
      exact mul_le_mul_of_nonneg_right (hbound (1 - ν) (by linarith) (by linarith))
        (Real.rpow_nonneg h2 r)
  have hright : IntervalIntegrable (fun ν : ℝ => (1 - ν ^ 2) ^ r) volume (0 : ℝ) 1 := by
    have hpow : IntervalIntegrable (fun ν : ℝ => (1 - ν) ^ r) volume (0 : ℝ) 1 :=
      Work.OddRadon.intervalIntegrable_one_sub_pow_rpow hr
    have hg : IntervalIntegrable (fun ν : ℝ => c * (1 - ν) ^ r) volume (0 : ℝ) 1 :=
      hpow.const_mul c
    refine hg.mono_fun' ?_ ?_
    · rw [restrict_uIoc_zero_one_eq_restrict_Ioo]
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      refine ((continuous_const.sub (continuous_id.pow 2)).continuousOn.rpow_const ?_)
      intro x hx
      rw [Set.mem_Ioo] at hx
      have hx2 : x ^ 2 < 1 := by nlinarith [hx.1, hx.2]
      refine Or.inl ?_
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
      linarith
    · refine ae_restrict_of_forall_mem measurableSet_uIoc (fun ν hν => ?_)
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Ioc] at hν
      have h1 : 0 ≤ 1 - ν := by linarith [hν.2]
      have h2 : 0 ≤ 1 + ν := by linarith [hν.1]
      have hnn : 0 ≤ 1 - ν ^ 2 := by nlinarith [hν.1, hν.2]
      change ‖(1 - ν ^ 2) ^ r‖ ≤ c * (1 - ν) ^ r
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hnn r),
        show (1 : ℝ) - ν ^ 2 = (1 - ν) * (1 + ν) by ring,
        Real.mul_rpow h1 h2, mul_comm ((1 - ν) ^ r) ((1 + ν) ^ r)]
      exact mul_le_mul_of_nonneg_right (hbound (1 + ν) (by linarith) (by linarith))
        (Real.rpow_nonneg h1 r)
  exact hleft.trans hright

/-- For `x > 0`, `x ^ k / √x = x ^ (k - 1/2)`. -/
lemma pow_div_sqrt_eq_rpow {x : ℝ} (hx : 0 < x) (k : ℕ) :
    x ^ k / Real.sqrt x = x ^ ((k : ℝ) - 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, Real.rpow_sub hx]

/-- The `ν`-integrand of the substitution `t = ρ(cν)·(cν)` is interval integrable on `(-1,1)`:
the factor `(1-ν²)^(n-1) / √(1-ν²)` has at worst a `(1∓ν)^(-1/2)` singularity at the two endpoints,
which is integrable, and `φ` is bounded on `[-1,1]`. -/
theorem intervalIntegrable_nu_integrand (n : ℕ) (hn : 1 ≤ n) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Set.Icc (-1 : ℝ) 1)) :
    IntervalIntegrable
      (fun ν : ℝ => (1 - ν ^ 2) ^ (n - 1) * φ ν / Real.sqrt (1 - ν ^ 2)) volume (-1 : ℝ) 1 := by
  have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr : (-1 : ℝ) < (n : ℝ) - 3 / 2 := by linarith
  have hbase : IntervalIntegrable (fun ν : ℝ => (1 - ν ^ 2) ^ ((n : ℝ) - 3 / 2)) volume
      (-1 : ℝ) 1 := intervalIntegrable_one_sub_sq_rpow_Ioo hr
  have hφ' : ContinuousOn φ (uIcc (-1 : ℝ) 1) := by
    rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hg : IntervalIntegrable (fun ν : ℝ => (1 - ν ^ 2) ^ ((n : ℝ) - 3 / 2) * φ ν) volume
      (-1 : ℝ) 1 := hbase.mul_continuousOn hφ'
  refine hg.congr_ae ?_
  -- the two integrands agree except at `ν = 1`, which is a null set
  have hdiff : uIoc (-1 : ℝ) 1 \ Set.Ioo (-1 : ℝ) 1 = {(1 : ℝ)} := by
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Set.Ioc_sdiff_Ioo_same (by norm_num : (-1 : ℝ) < 1)
  have hnull : volume (uIoc (-1 : ℝ) 1 \ Set.Ioo (-1 : ℝ) 1) = 0 := by
    rw [hdiff]
    exact measure_singleton 1
  have hmem : ∀ᵐ ν ∂volume, ν ∉ (uIoc (-1 : ℝ) 1 \ Set.Ioo (-1 : ℝ) 1) :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  show ∀ᵐ ν ∂(volume.restrict (uIoc (-1 : ℝ) 1)),
    (1 - ν ^ 2) ^ ((n : ℝ) - 3 / 2) * φ ν = (1 - ν ^ 2) ^ (n - 1) * φ ν / Real.sqrt (1 - ν ^ 2)
  rw [ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hmem] with ν hν hνs
  have hνIoo : ν ∈ Set.Ioo (-1 : ℝ) 1 := by
    by_contra h
    exact hν ⟨hνs, h⟩
  rw [Set.mem_Ioo] at hνIoo
  have hx : 0 < 1 - ν ^ 2 := by nlinarith [hνIoo.1, hνIoo.2]
  have hkey : (1 - ν ^ 2) ^ (n - 1) / Real.sqrt (1 - ν ^ 2) = (1 - ν ^ 2) ^ ((n : ℝ) - 3 / 2) := by
    rw [pow_div_sqrt_eq_rpow hx (n - 1)]
    congr 1
    rw [Nat.cast_sub hn]
    ring
  rw [← hkey]
  ring

end Work.OddCurve.LowSlope
