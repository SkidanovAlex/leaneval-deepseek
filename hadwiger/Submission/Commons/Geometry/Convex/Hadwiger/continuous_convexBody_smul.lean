import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Commons.Geometry.Convex.Hadwiger

open scoped Pointwise

theorem continuous_convexBody_smul
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] (X : ConvexBody V) :
    Continuous (fun t : ℝ => t • X) := by
  rw [Metric.continuous_iff]
  intro t₀ ε hε
  obtain ⟨R, hRpos, hR⟩ := X.isBounded.exists_pos_norm_le
  refine ⟨ε / R, div_pos hε hRpos, ?_⟩
  intro t ht
  have ht_abs : |t - t₀| < ε / R := by
    simpa [Real.dist_eq] using ht
  have htr : |t - t₀| * R < ε := (lt_div_iff₀ hRpos).mp ht_abs
  let r : ℝ := |t - t₀| * R
  have hr : 0 ≤ r := mul_nonneg (abs_nonneg _) (le_of_lt hRpos)
  have h_le : Metric.hausdorffDist (t • (X : Set V)) (t₀ • (X : Set V)) ≤ r := by
    refine Metric.hausdorffDist_le_of_mem_dist hr ?_ ?_
    · intro x hx
      rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
      refine ⟨t₀ • y, ?_, ?_⟩
      · exact Set.mem_smul_set.mpr ⟨y, hy, rfl⟩
      · rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hR y hy) (abs_nonneg _)
    · intro x hx
      rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
      refine ⟨t • y, ?_, ?_⟩
      · exact Set.mem_smul_set.mpr ⟨y, hy, rfl⟩
      · rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, abs_sub_comm]
        exact mul_le_mul_of_nonneg_left (hR y hy) (abs_nonneg _)
  have hdist_le : dist (t • X) (t₀ • X) ≤ r := by
    rw [← ConvexBody.hausdorffDist_coe]
    simpa [ConvexBody.coe_smul] using h_le
  exact lt_of_le_of_lt hdist_le htr

end Commons.Geometry.Convex.Hadwiger