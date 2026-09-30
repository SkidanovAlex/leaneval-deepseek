import Mathlib
import Submission.Work.BW.sieg2AdjDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open NumberField

namespace Work.BW

noncomputable section

/-- For a function on the infinite places of a number field, the product over the index of the
mixed embedding (a real place contributes one coordinate, a complex place contributes two)
equals the product over the places weighted by their multiplicity. -/
lemma prod_index_eq_prod_mult_place {F : Type*} [Field F] [NumberField F]
    (g : NumberField.InfinitePlace F → ℝ) :
    ∏ s : NumberField.mixedEmbedding.index F, g (stdPlace s) =
      ∏ w : NumberField.InfinitePlace F, g w ^ w.mult := by
  rw [Fintype.prod_sum_type]
  simp only [stdPlace_inl]
  rw [Fintype.prod_prod_type]
  simp only [stdPlace_inr]
  rw [NumberField.InfinitePlace.prod_eq_prod_mul_prod]
  simp only [NumberField.InfinitePlace.mult_isReal, NumberField.InfinitePlace.mult_isComplex,
    Fin.prod_univ_two, pow_one, pow_two]

theorem prod_index_eq_prod_mult {F : Type*} [Field F] [NumberField F] {M : ℕ}
    (f : Fin M × NumberField.InfinitePlace F → ℝ) :
    ∏ p : Fin M × NumberField.mixedEmbedding.index F, f (p.1, Work.BW.stdPlace p.2) =
      ∏ i : Fin M, ∏ w : NumberField.InfinitePlace F, (f (i, w)) ^ w.mult := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl ?_
  intro i _
  exact prod_index_eq_prod_mult_place (fun w => f (i, w))

end

end Work.BW
