import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Polynomial

lemma mem_adjoin_rootSet_of_mem_adjoin {K : Type*} [Field K] {f₂ : Polynomial K}
    (hf₂0 : f₂ ≠ 0) {α β : AlgebraicClosure K}
    (hβ : β ∈ (f₂.map (algebraMap K (AlgebraicClosure K))).roots)
    (h : α ∈ IntermediateField.adjoin K ({β} : Set (AlgebraicClosure K))) :
    α ∈ IntermediateField.adjoin K (f₂.rootSet (AlgebraicClosure K)) := by
  obtain ⟨hmap0, hroot⟩ := Polynomial.mem_roots'.mp hβ
  have haev : (Polynomial.aeval β) f₂ = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact hroot
  have hβroot : β ∈ f₂.rootSet (AlgebraicClosure K) := by
    rw [Polynomial.mem_rootSet']
    exact ⟨hmap0, haev⟩
  refine (IntermediateField.adjoin_le_iff.mpr ?_) h
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact IntermediateField.subset_adjoin K _ hβroot

end Commons.FieldTheory.Polynomial