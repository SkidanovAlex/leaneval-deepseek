import Mathlib
import Submission.Work.Pi6.SQM.Defs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-! Guidance from the project lead (the requester):

SQM piece (small). Pull-back of cochains along a map of simplicial sets f commutes with cup1m, cup2 (area SQ) and cup3
(SQM/Defs.lean). Model: the library's Work.Cohomology.cupNatural (Cohomology/cupNatural.lean). Evaluate both sides on a
simplex σ (genEval), use that the pull-back evaluates on f.app σ and that f commutes with X.map of every face map
(naturality of f). Three near-identical proofs; do cup1m first.

# Naturality of `∪₁`, `∪₂`, `∪₃` under a map of simplicial sets

All three products are *generator-defined*: `Work.Cohomology.cup_ext` reduces an identity of cochains to an identity of
their values (`genEval`) on every simplex, and each product's value on `σ` is an explicit sum of products of values of
the arguments on `X.map (some face map).op σ`.  Pulling back along `f : X ⟶ Y` evaluates on `f.app σ`
(`Work.Cohomology.genEval_dualMap`), and `f` commutes with `X.map θ.op` for every `θ` in the simplex category
(`CategoryTheory.NatTrans.naturality_apply`), so the two sides normalise to the same expression.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval)

/-- **Naturality of `∪₁`, `∪₂`, `∪₃`** under maps of simplicial sets (pull-back of cochains). -/
theorem cupINatural : Work.Pi6.SQM.CupINatural := by
  intro X Y f n m u v
  refine ⟨?_, ?_, ?_⟩
  · apply Work.Cohomology.cup_ext F2 X
    intro σ
    simp only [Work.Cohomology.genEval_dualMap, Work.Pi6.SQ.genEval_cup1m,
      Work.Cohomology.genEval_cup1, CategoryTheory.NatTrans.naturality_apply]
  · apply Work.Cohomology.cup_ext F2 X
    intro σ
    simp only [Work.Cohomology.genEval_dualMap, Work.Pi6.SQ.genEval_cup2,
      CategoryTheory.NatTrans.naturality_apply]
  · apply Work.Cohomology.cup_ext F2 X
    intro σ
    simp only [Work.Cohomology.genEval_dualMap, Work.Pi6.SQM.genEval_cup3, Work.Pi6.SQM.cup3Val,
      CategoryTheory.NatTrans.naturality_apply]

end

end Work.Pi6.SQM
