import Mathlib
import Submission.Work.Pi6.SQM.SIG.Basic
import Submission.Work.Cohomology.relCupHNatural
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.SQM.SIG

/-- Naturality of `relClassOf` under the contravariant pair map.  Already available in the
workspace as `Work.Cohomology.homologyMap_relComplexMap_relClassOf` together with
`Work.Cohomology.relClassOf_proof_irrel` (both in `Submission/Work/Cohomology/relCupHNatural.lean`),
so a thin wrapper suffices. -/
theorem relClassOfNatural :
    ∀ {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
      (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ) (a : Work.Cohomology.relKern Work.Pi6.SQ.F2 X₂ A₂ n)
      (ha : Work.Cohomology.relDiffLM Work.Pi6.SQ.F2 X₂ A₂ n a = 0)
      (ha' : Work.Cohomology.relDiffLM Work.Pi6.SQ.F2 X₁ A₁ n
        (Work.Cohomology.relMapLM Work.Pi6.SQ.F2 A₁ A₂ f h n a) = 0),
      HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap Work.Pi6.SQ.F2 A₁ A₂ f h) n
          (Work.Cohomology.relClassOf Work.Pi6.SQ.F2 X₂ A₂ a ha) =
        Work.Cohomology.relClassOf Work.Pi6.SQ.F2 X₁ A₁
          (Work.Cohomology.relMapLM Work.Pi6.SQ.F2 A₁ A₂ f h n a) ha' := by
  intro X₁ X₂ A₁ A₂ f h n a ha ha'
  rw [Work.Cohomology.homologyMap_relComplexMap_relClassOf Work.Pi6.SQ.F2 A₁ A₂ f h a ha]

end Work.Pi6.SQM.SIG
