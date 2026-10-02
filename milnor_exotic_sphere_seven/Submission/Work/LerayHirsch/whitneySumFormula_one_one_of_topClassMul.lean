import Mathlib
import Submission.Work.Whitney.chernProductSum_eq_fin
import Submission.Work.Whitney.Cup
import Submission.Work.Thom.chernClass
import Submission.Work.LineBundles.WhitneyOneOne

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The Whitney sum formula in ranks `(1,1)` from WHITNEY's `TopClassMul`

`Work.Whitney.TopClassMul` is the top-degree multiplicativity
`c_{m+n}(E ⊕ F) = c_m(E) ⌣ c_n(F)`.  In ranks `(1,1)` it reads `c₂(L ⊕ M) = c₁(L) ⌣ c₁(M)`;
combined with the degree-`2` collapse of the right-hand side,
`Work.LerayHirsch.chernProductSum_two_eq_cupChern`, this is the degree-`2` input of
`Work.LineBundles.whitneySumFormula_one_one_of_topClassMul`, which produces the `(1,1)` case
`Work.LerayHirsch.WhitneySumFormula 1 1` of the Whitney sum formula (degrees `0,1,2,≥3` are then
bookkeeping, carried out in `Work.Gen.whitneySumFormulaOneOne`).
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]

/-- The degree bookkeeping of `Work.Thom.cohTransport` depends on its equality argument only
through its proof. -/
theorem cohTransport_congr_proof {B : Type} [TopologicalSpace B] {n n' : ℕ} {x : Coh ℤ n B}
    (h h' : n = n') : cohTransport h x = cohTransport h' x := by
  rw [Subsingleton.elim h h']

/-- **The degree-`2` collapse of the right-hand side of the Whitney formula for two line
bundles.**  The summands `c_0(L)⌣c_2(M)` and `c_2(L)⌣c_0(M)` vanish (a line bundle has no second
Chern class), so only `c₁(L)⌣c₁(M)` survives. -/
theorem chernProductSum_two_eq_cupChern
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (M : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) :
    Work.Whitney.chernProductSum L M 2
      = Work.Whitney.cupChern 1 1 (chernClass 1 1 L) (chernClass 1 1 M) := by
  rw [Work.Whitney.chernProductSum_eq_fin, Finset.sum_eq_single (1 : Fin 3)]
  · rw [Work.Whitney.cupChern_def]
    exact cohTransport_congr_proof _ _
  · intro a _ ha
    fin_cases a
    · -- a = 0: the second factor is `c_2(M) = 0`
      simp only [Nat.mul_zero, Nat.sub_zero,
        chernClass_succ_of_gt M (by norm_num : 1 < 2),
        Work.Cohomology.cupH'_zero_right, Work.Thom.cohTransport_zero]
    · exact absurd rfl ha
    · -- a = 2: the first factor is `c_2(L) = 0`
      simp only [chernClass_succ_of_gt L (by norm_num : 1 < 2),
        Work.Cohomology.cupH'_zero_left, Work.Thom.cohTransport_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The `(1,1)` case of the Whitney sum formula from WHITNEY's top-degree multiplicativity.** -/
theorem whitneySumFormula_one_one_of_topClassMul
    (h : Work.Whitney.TopClassMul) : Work.LerayHirsch.WhitneySumFormula 1 1 := by
  refine Work.LineBundles.whitneySumFormula_one_one_of_topClassMul (fun L M => ?_)
  rw [h L M, chernProductSum_two_eq_cupChern L M]

end

end Work.LerayHirsch
