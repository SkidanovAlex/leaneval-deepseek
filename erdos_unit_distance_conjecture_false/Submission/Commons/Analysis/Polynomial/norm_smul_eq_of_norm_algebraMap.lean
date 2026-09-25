import Mathlib.Analysis.Normed.Field.Basic

namespace Commons.Analysis.Polynomial

lemma norm_smul_eq_of_norm_algebraMap {K L : Type*} [NormedField K] [NormedField L] [Algebra K L]
    (h : ∀ k : K, ‖algebraMap K L k‖ = ‖k‖) (k : K) (x : L) : ‖k • x‖ = ‖k‖ * ‖x‖ := by
  rw [Algebra.smul_def, norm_mul, h]

end Commons.Analysis.Polynomial