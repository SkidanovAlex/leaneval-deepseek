import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

open Polynomial WeierstrassCurve.Affine

/-- Integrality criterion for a root of a monic quadratic: if `y` satisfies
`y ^ 2 + c1 * y + c0 = 0` with `c1, c0` in a subalgebra `S`, then `y` is integral over `S`.
The witnessing polynomial is `X ^ 2 + C c1 * X + C c0`, which is monic since the degree of
`C c1 * X + C c0` is at most `1`. -/
lemma isIntegral_of_quadratic {K : Type*} [Field K] {L : Type*} [Field L] [Algebra L K]
    (S : Subalgebra L K) (c1 c0 : K) (h1 : c1 ∈ S) (h0 : c0 ∈ S) {y : K}
    (h : y ^ 2 + c1 * y + c0 = 0) : IsIntegral S y := by
  refine ⟨X ^ 2 + C (⟨c1, h1⟩ : S) * X + C (⟨c0, h0⟩ : S), ?_, ?_⟩
  · have H : degree (C (⟨c1, h1⟩ : S) * X + C (⟨c0, h0⟩ : S)) < (2 : WithBot ℕ) := by
      refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by norm_num)
      · exact lt_of_le_of_lt degree_C_le (by norm_num)
    rw [add_assoc]
    exact monic_X_pow_add H
  · rw [← aeval_def]
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
    simpa using h

/-
Route: `genY E` satisfies the monic quadratic
`X² + (a₁ genX + a₃) X - (genX³ + a₂ genX² + a₄ genX + a₆)` over `L[genX]` (from
`genX_genY_relation`/`Relations`), and `infW E` satisfies the monic quadratic
`X² + (a₁ u + a₃ u²) X - (u + a₂u² + a₄u³ + a₆u⁴)` over `L[infU]` (from `infU_infW_relation`).
Both are instances of `isIntegral_of_quadratic`, the coefficients being polynomials in
`genX E` resp. `infU E` with coefficients in `L`.
-/
theorem Integral (L : Type*) [Field L] (E : WeierstrassCurve L) :
    IsIntegral (Algebra.adjoin L ({Work.MotC2.genX E} : Set (Work.MotC2.Func E))) (Work.MotC2.genY E) ∧
    IsIntegral (Algebra.adjoin L ({Work.MotC2.infU E} : Set (Work.MotC2.Func E))) (Work.MotC2.infW E) := by
  constructor
  · refine isIntegral_of_quadratic (Algebra.adjoin L ({genX E} : Set (Func E)))
      (algebraMap L (Func E) E.a₁ * genX E + algebraMap L (Func E) E.a₃)
      (-((genX E) ^ 3 + algebraMap L (Func E) E.a₂ * (genX E) ^ 2 +
          algebraMap L (Func E) E.a₄ * genX E + algebraMap L (Func E) E.a₆)) ?_ ?_ ?_
    · exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ E.a₁)
          (Algebra.subset_adjoin (Set.mem_singleton _)))
        (Subalgebra.algebraMap_mem _ E.a₃)
    · exact neg_mem (add_mem (add_mem (add_mem
          (pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) 3)
          (mul_mem (Subalgebra.algebraMap_mem _ E.a₂)
            (pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) 2)))
        (mul_mem (Subalgebra.algebraMap_mem _ E.a₄)
          (Algebra.subset_adjoin (Set.mem_singleton _))))
        (Subalgebra.algebraMap_mem _ E.a₆))
    · linear_combination (norm := first | refl_ring1 | ring1) genY_sq_relation E
  · refine isIntegral_of_quadratic (Algebra.adjoin L ({infU E} : Set (Func E)))
      (algebraMap L (Func E) E.a₁ * infU E + algebraMap L (Func E) E.a₃ * (infU E) ^ 2)
      (-(infU E + algebraMap L (Func E) E.a₂ * (infU E) ^ 2 +
          algebraMap L (Func E) E.a₄ * (infU E) ^ 3 +
          algebraMap L (Func E) E.a₆ * (infU E) ^ 4)) ?_ ?_ ?_
    · exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ E.a₁)
          (Algebra.subset_adjoin (Set.mem_singleton _)))
        (mul_mem (Subalgebra.algebraMap_mem _ E.a₃)
          (pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) 2))
    · exact neg_mem (add_mem (add_mem (add_mem
          (Algebra.subset_adjoin (Set.mem_singleton _))
          (mul_mem (Subalgebra.algebraMap_mem _ E.a₂)
            (pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) 2)))
        (mul_mem (Subalgebra.algebraMap_mem _ E.a₄)
          (pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) 3)))
        (mul_mem (Subalgebra.algebraMap_mem _ E.a₆)
          (pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) 4)))
    · linear_combination (norm := first | refl_ring1 | ring1) infW_sq_relation E

end Work.MotC2
