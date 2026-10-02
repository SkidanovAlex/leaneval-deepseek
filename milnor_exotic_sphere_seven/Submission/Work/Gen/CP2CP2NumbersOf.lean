import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Gen.CP2CP2Smooth8
import Submission.Work.Projective.CP2CP2
import Submission.Work.Gen.CP4NumbersOf

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# AREA GEN — the numbers `(σ, p₁², p₂) = (1, 18, 9)` of `ℂP² × ℂP²`

The second generator.  Its cohomology ring (`ℂP² × ℂP²`'s Künneth ring, with the intersection
numbers of `a², ab, b²`) is the interface `Work.Projective.CP2CP2Model`; producing that data for the
concrete space is the KUNNETH subproject's job.  What AREA GEN contributes is the **single point of
contact**: given a `CP2CP2Model` for the concrete `SSet` and the two Chern-class identities for the
**defined** tangent bundle (`p₁(T) = the model's p₁`, `p₂(T) = the model's p₂`), the numbers and the
dimension-`8` Hirzebruch identity follow from the model's already-proved lemmas.
-/

open scoped Manifold ContDiff

namespace Work.Gen

open Work.Projective

noncomputable section

/-- The singular simplicial set of `ℂP² × ℂP²`, in the form used by
`Work.Projective.CP2CP2Model` and by `Work.Drive.Smooth8.sset`. -/
abbrev cppSSet : SSet := TopCat.toSSet.obj (TopCat.of (CP 2 × CP 2))

/-- **The numbers of `ℂP² × ℂP²` and the dimension-`8` Hirzebruch identity**, from the Künneth-ring
model of the concrete space and the identification of the **defined** tangent-bundle classes with the
model's `p₁`, `p₂`. -/
theorem cp2cp2NumbersOf
    (M : CP2CP2Model cppSSet)
    (hc : Submodule.span ℤ {M.c} = ⊤)
    (h1 : Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2) = M.p₁)
    (h2 : Work.Thom.p2Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2) = M.p₂) :
    (cp2cp2Smooth8Of M.c hc).sigma = 1 ∧ (cp2cp2Smooth8Of M.c hc).p1Sq = 18 ∧
      (cp2cp2Smooth8Of M.c hc).p2Num = 9 ∧ (cp2cp2Smooth8Of M.c hc).Hirzebruch := by
  have hsig : (cp2cp2Smooth8Of M.c hc).sigma = 1 := CP2CP2Model.sigma M
  have hp1 : (cp2cp2Smooth8Of M.c hc).p1Sq = 18 := by
    show Work.SignatureBordism.p₁SqNumber cppSSet M.c
      (Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2)) = 18
    rw [h1]
    exact CP2CP2Model.p1SqNumber M
  have hp2 : (cp2cp2Smooth8Of M.c hc).p2Num = 9 := by
    show Work.SignatureBordism.p₂Number cppSSet M.c
      (Work.Thom.p2Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2)) = 9
    rw [h2]
    exact CP2CP2Model.p2Number M
  exact ⟨hsig, hp1, hp2, by
    show 45 * (cp2cp2Smooth8Of M.c hc).sigma
      = 7 * (cp2cp2Smooth8Of M.c hc).p2Num - (cp2cp2Smooth8Of M.c hc).p1Sq
    rw [hsig, hp1, hp2]; norm_num⟩

end

end Work.Gen
