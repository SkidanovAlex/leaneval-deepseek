import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Commons.Analysis.Convolution

open MeasureTheory

theorem integrableOn_Ioi_rpow_max_one (n : ℕ) (hn : 1 ≤ n) (A' : ℝ) (hA' : (n : ℝ) < A') :
    MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (n - 1) * (max 1 t) ^ (-A')) (Set.Ioi (0 : ℝ)) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrableOn_union]
  constructor
  · -- On `(0, 1]` the factor `(max 1 t) ^ (-A')` equals `1`.
    have hcont : ContinuousOn (fun t : ℝ => t ^ (n - 1)) (Set.Icc (0 : ℝ) 1) :=
      (continuous_pow (n - 1)).continuousOn
    have hIcc : IntegrableOn (fun t : ℝ => t ^ (n - 1)) (Set.Icc (0 : ℝ) 1) :=
      hcont.integrableOn_Icc
    have hIoc : IntegrableOn (fun t : ℝ => t ^ (n - 1)) (Set.Ioc (0 : ℝ) 1) :=
      hIcc.mono_set Set.Ioc_subset_Icc_self
    refine hIoc.congr_fun (fun t ht => ?_) measurableSet_Ioc
    rw [max_eq_left ht.2, Real.one_rpow, mul_one]
  · -- On `(1, ∞)` the factor `(max 1 t) ^ (-A')` equals `t ^ (-A')`, so the integrand is
    -- `t ^ ((n : ℝ) - 1 - A')`, which is integrable since `(n : ℝ) - 1 - A' < -1`.
    have hbase : IntegrableOn (fun t : ℝ => t ^ (((n : ℝ) - 1) - A')) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hbase.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [max_eq_right (le_of_lt ht), ← Real.rpow_natCast t (n - 1), Nat.cast_sub hn,
      ← Real.rpow_add ht0]
    ring_nf

end Commons.Analysis.Convolution