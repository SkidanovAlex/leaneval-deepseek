import Mathlib
import Submission.Work.LerayHirsch.LineSum
import Submission.Work.LerayHirsch.WhitneyParacompact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The *split* case of the Whitney sum formula

This module names the remaining input of the Whitney sum formula of this chapter, in the form in
which the **flag bundle** (`Work.LerayHirsch.SplittingPrinciple`) reduces it:

`Work.LerayHirsch.WhitneySumFormulaSplit` — the Whitney formula `(1, n)` for a line bundle `L` and an
explicit iterated direct sum `M 0 ⊕ … ⊕ M (n-1)` of line bundles
(`Work.LerayHirsch.lineSumCore n M`).

The point of the name is that the *general* line-bundle case `∀ N, WhitneySumFormula 1 N` — over a
paracompact Hausdorff base, in the form `Work.LerayHirsch.WhitneySumFormulaPar 1 N` — follows from
this split case by pulling back along the flag bundle of the second summand and using the
injectivity of the pullback in cohomology
(`Work.LerayHirsch.whitneySumFormulaPar_one_of_splitLines`).  This is the content of item 4 of the
deliverable of this chapter: the flag bundle reduces the Whitney formula to its split case.

Two other inputs are needed to *reach* the split case, and they belong to other areas:

* the multiplicativity of the top Chern class (`Work.Whitney.TopClassMul`) and the Euler–Chern
  identity `c_k(E) = e(Λ^k E)` produce, for a direct sum of line bundles,
  `c_k(⊕_j M_j) = e_k(c₁(M_j))` (the `k`-th elementary symmetric function of the first Chern
  classes);
* the degree-`1` case `c₁(L ⊕ M) = c₁(L) + c₁(M)` of `Submission/Work/LineBundles/`.

Neither of these is proved in this chapter.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The split case of the Whitney sum formula**: for a complex line bundle `L` and an iterated
direct sum `M 0 ⊕ … ⊕ M (n-1)` of complex line bundles over a paracompact Hausdorff base, the
Whitney formula `(1, n)` holds:

`c_k(L ⊕ (M 0 ⊕ … ⊕ M (n-1))) = Σ_{i+j=k} c_i(L) ⌣ c_j(M 0 ⊕ … ⊕ M (n-1))`.

The iterated sum is `Work.LerayHirsch.lineSumCore n M` (`Submission/Work/LerayHirsch/LineSum.lean`),
so no reindexing of the summands is needed. -/
def WhitneySumFormulaSplit : Prop :=
  ∀ {P : Type} [TopologicalSpace P] [ParacompactSpace P] [T2Space P] {ι ι' : Type}
    [Fintype ι] [Fintype ι']
    (n : ℕ) (L : VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1)) ι)
    (M : Fin n → VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1)) ι') (k : ℕ),
    Work.Thom.chernClass (1 + n) k (Work.Whitney.whitneySum L (lineSumCore n M))
      = Work.Whitney.chernProductSum L (lineSumCore n M) k

end

end Work.LerayHirsch
