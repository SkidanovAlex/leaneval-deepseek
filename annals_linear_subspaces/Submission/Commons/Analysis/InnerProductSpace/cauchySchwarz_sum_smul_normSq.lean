import Mathlib

open scoped BigOperators

namespace Commons.Analysis.InnerProductSpace

lemma cauchySchwarz_sum_smul_normSq {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a : ι → ℝ) (b : ι → E) :
    ‖(Finset.univ.sum fun i => a i • b i)‖ ^ 2 ≤
      (Finset.univ.sum fun i => (a i) ^ 2) * (Finset.univ.sum fun i => ‖b i‖ ^ 2) := by
  classical
  calc
    ‖(Finset.univ.sum fun i => a i • b i)‖ ^ 2
        ≤ (Finset.univ.sum fun i => |a i| * ‖b i‖) ^ 2 := by
            have htri : ‖(Finset.univ.sum fun i => a i • b i)‖ ≤
                Finset.univ.sum fun i => |a i| * ‖b i‖ := by
              calc
                ‖(Finset.univ.sum fun i => a i • b i)‖
                    ≤ Finset.univ.sum fun i => ‖a i • b i‖ := norm_sum_le _ _
                _ = Finset.univ.sum fun i => |a i| * ‖b i‖ := by simp [norm_smul]
            exact (sq_le_sq₀ (by positivity) (by positivity)).2 htri
    _ ≤ (Finset.univ.sum fun i => |a i| ^ 2) * (Finset.univ.sum fun i => ‖b i‖ ^ 2) := by
            simpa using (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
              (fun i : ι => |a i|) (fun i : ι => ‖b i‖))
    _ = (Finset.univ.sum fun i => (a i) ^ 2) * (Finset.univ.sum fun i => ‖b i‖ ^ 2) := by
            simp [sq_abs]

end Commons.Analysis.InnerProductSpace
