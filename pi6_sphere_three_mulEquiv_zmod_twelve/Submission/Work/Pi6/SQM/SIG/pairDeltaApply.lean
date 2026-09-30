import Mathlib
import Submission.Work.Pi6.SQM.SIG.Basic
import Submission.Work.StemsB.pairDelta_mixedCup_general_R
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.SQM.SIG

open CategoryTheory AlgebraicTopology

/-- The connecting map of the pair, computed on a class by a cochain lift: if `s` is a cochain on
`X` whose restriction to `A` is a cocycle and `z` is the relative cocycle with underlying cochain
`δs`, then `δ([s|_A]) = [z]`.  Use `ShortComplex.ShortExact.δ_eq` applied to the short exact
sequence `Work.Cohomology.pairShort`/`pairShort_shortExact` (with `x₃` the restriction of `s`,
`x₂ = s`, `x₁ = z`, and `hz` giving `x₁ ≫ f = x₂ ≫ d`).  The ℤ analogue is already proved as
`Work.Cohomology.pairδ_classOf_lift` in
`Submission/Work/ThomBordism/transgressionCapPairConnecting.lean`. -/
theorem pairDeltaApply (X : TopCat) (A : Set X) (n : ℕ)
    (s : Work.Cohomology.Cochain Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX X) n)
    (z : Work.Cohomology.relKern Work.Pi6.SQ.F2 X A (n + 1))
    (hz : z.1 = Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX X) s)
    (hzc : Work.Cohomology.relDiffLM Work.Pi6.SQ.F2 X A (n + 1) z = 0)
    (h : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX ↥A)
      (Work.Pi6.SQM.SIG.pb (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A)) s) = 0) :
    Work.Cohomology.pairδ Work.Pi6.SQ.F2 X A n
        (Work.Pi6.SQM.cls
          (Work.Pi6.SQM.SIG.pb (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A)) s) h) =
      Work.Cohomology.relClassOf Work.Pi6.SQ.F2 X A z hzc := by
  obtain ⟨hmem, hcoc, hδ⟩ :=
    Work.StemsB.pairδ_cohomologyClassOf_lift_R Work.Pi6.SQ.F2 X A n
      (Work.Pi6.SQM.SIG.pb (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A)) s) h s rfl
  have heq : (⟨((Work.Cohomology.singularCochainComplex Work.Pi6.SQ.F2 X).d n (n+1)).hom s,
        hmem⟩ : Work.Cohomology.relKern Work.Pi6.SQ.F2 X A (n + 1)) = z := by
    apply Subtype.ext
    show ((Work.Cohomology.singularCochainComplex Work.Pi6.SQ.F2 X).d n (n+1)).hom s = z.1
    rw [Work.Cohomology.singularCochain_d_apply Work.Pi6.SQ.F2 X s]
    exact hz.symm
  rw [hδ]
  exact Work.StemsB.relClassOf_congr_R Work.Pi6.SQ.F2 X A heq hcoc hzc

end Work.Pi6.SQM.SIG
