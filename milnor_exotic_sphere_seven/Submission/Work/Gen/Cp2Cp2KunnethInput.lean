import Mathlib
import Submission.Work.Kunneth.cp2cp2ModelCpp
import Submission.Work.Kunneth.cp2cp2H8Span
import Submission.Work.Gen.CP2CP2NumbersOf
import Submission.Work.Gen.Cp2Cp2TangentClasses

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Künneth input of `Work.Gen.cp2cp2_model_of_whitney`, discharged

The KUNNETH subproject supplies `Work.Kunneth.cp2cp2ModelCpp : Work.Projective.CP2CP2Model cppSSet`
for exactly the simplicial set `Work.Gen.cppSSet` (both are
`TopCat.toSSet.obj (TopCat.of (CP 2 × CP 2))`), with `a`, `b` the pullbacks of the hyperplane class
`Work.Gen.uCoh 2` along the two projections, `p₁`, `p₂` *defined* as the pullback expressions, and
the generation of the fundamental class as `Work.Kunneth.cppC_generates`.

This module records that the *second* of the two inputs of the deliverable
(`Submission/Work/Gen/README.md`, SESSION 8/9) is therefore **available**: the lemma below is the
`h1`/`h2`/`hc` triple that `Work.Gen.cp2cp2_model_of_whitney` and `Work.Gen.generators8_of` ask for,
with the model `Work.Projective.CP2CP2Model Work.Gen.cppSSet` in place.
-/

open CategoryTheory

namespace Work.Gen

noncomputable section

open Work.Projective

/-- **The Künneth input of the deliverable, discharged.**  The witness is the KUNNETH model of the
space `ℂP² × ℂP²`; the two identities are definitional because that model's `p₁`, `p₂` are *defined*
as the pullback expressions. -/
theorem cp2cp2KunnethInput :
    ∃ M : CP2CP2Model cppSSet, Submodule.span ℤ {M.c} = ⊤ ∧
      M.p₁ = (3 : ℤ) • ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
        + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)) ∧
      M.p₂ = (9 : ℤ) • Work.Cohomology.cupH'
        ℤ (TopCat.toSSet.obj (TopCat.of (CP 2 × CP 2))) 4 4
        ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
        ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2)) :=
  ⟨Work.Kunneth.cp2cp2ModelCpp, Work.Kunneth.cppC_generates, rfl, rfl⟩

end

end Work.Gen
