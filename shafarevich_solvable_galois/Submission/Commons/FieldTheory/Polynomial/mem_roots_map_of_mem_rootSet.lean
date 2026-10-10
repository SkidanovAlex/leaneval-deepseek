import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Polynomial

lemma mem_roots_map_of_mem_rootSet {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : Polynomial K} (hf : f ≠ 0) {β : L} (hβ : β ∈ f.rootSet L) :
    β ∈ (f.map (algebraMap K L)).roots := by
  rw [_root_.Polynomial.mem_roots_map_of_injective (RingHom.injective (algebraMap K L)) hf,
    ← _root_.Polynomial.aeval_def]
  exact _root_.Polynomial.aeval_eq_zero_of_mem_rootSet hβ

end Commons.FieldTheory.Polynomial