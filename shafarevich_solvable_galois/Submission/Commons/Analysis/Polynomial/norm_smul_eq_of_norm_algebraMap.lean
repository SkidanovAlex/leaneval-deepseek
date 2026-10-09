import Mathlib.Analysis.Normed.Field.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Polynomial

lemma norm_smul_eq_of_norm_algebraMap {K L : Type*} [NormedField K] [NormedField L] [Algebra K L]
    (h : ∀ k : K, ‖algebraMap K L k‖ = ‖k‖) (k : K) (x : L) : ‖k • x‖ = ‖k‖ * ‖x‖ := by
  rw [Algebra.smul_def, norm_mul, h]

end Commons.Analysis.Polynomial