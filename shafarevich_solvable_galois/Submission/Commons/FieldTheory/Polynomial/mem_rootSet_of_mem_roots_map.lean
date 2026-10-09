import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Polynomial

lemma mem_rootSet_of_mem_roots_map {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : Polynomial K} (hf : f ≠ 0) {β : L} (hβ : β ∈ (f.map (algebraMap K L)).roots) :
    β ∈ f.rootSet L := by
  rw [Polynomial.mem_rootSet']
  refine ⟨Polynomial.ne_zero_of_mem_roots hβ, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  exact Polynomial.isRoot_of_mem_roots hβ

end Commons.FieldTheory.Polynomial