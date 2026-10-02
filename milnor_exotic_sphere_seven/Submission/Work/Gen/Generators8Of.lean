import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Gen.CP4NumbersOf
import Submission.Work.Gen.CP2CP2NumbersOf

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
# AREA GEN — the final assembly of `Work.Drive.Generators8`

**This is the single point of contact of AREA GEN.**  Everything the area produces (the two
manifolds as `Work.Drive.Smooth8`, the tangent-bundle presentations, the Euler sequence, the ring
structure `Work.Gen.uSq_span`/`Work.Gen.uSqGenerates`, and the number computations
`Work.Gen.cp4NumbersOf` / `Work.Gen.cp2cp2NumbersOf`) is assembled here into

`Work.Drive.Generators8` — two closed connected oriented `C^∞` `8`-manifolds satisfying
`45σ = 7p₂ - p₁²` for the **defined** classes `Work.Thom.p1Tangent'`/`p2Tangent'`, with linearly
independent `(p₁², p₂)`-number vectors — from exactly two remaining inputs:

* `h2`, `h4`: the two Chern-class identities `p₁(TℂP⁴) = 5u²`, `p₂(TℂP⁴) = 10u⁴` for the *defined*
  tangent bundle.  These are the Euler sequence `TℂP⁴ ⊕ ε² ≅ (O(1) ⊕ O(-1))⁵`
  (`Work.Gen.eulerSequence_iso`) together with the Whitney sum formula
  (`Submission/Work/Whitney/`), transported to `p1Tangent'`/`p2Tangent'` by
  `Work.Gen.TangentPresentation` and `Work.Gen.cp4ChernPresentation`.  The child module
  `Work.Gen.EulerChern` carries the proof; it is what turns this lemma unconditional.
* `M`, `hc`, `h1`, `h2'`: a `Work.Projective.CP2CP2Model` for the concrete space (Künneth for
  `H^*(ℂP² × ℂP²;ℤ)`, the KUNNETH subproject) together with `p₁(T(ℂP² × ℂP²)) = M.p₁`,
  `p₂(T(ℂP² × ℂP²)) = M.p₂` (the product tangent bundle + the Whitney sum formula) and the
  generation of `H₈` by `M.c` (`Work.Gen.Cp2Cp2FundamentalClass`).

The independence of the two number vectors is the arithmetic `25·9 ≠ 10·18`.
-/

open scoped Manifold ContDiff

namespace Work.Gen

open Work.Projective

noncomputable section

/-- **THE FINAL ASSEMBLY**: `Work.Drive.Generators8` from the two characteristic-class inputs.
The first generator is `ℂP⁴` with the generating fundamental class `Work.Projective.cp4C` (the
normalisation `⟨u⁴, cp4C⟩ = ±1` is `Work.Gen.kronH_uFourth_pm_one`), the second is `ℂP² × ℂP²`
with the model's fundamental class. -/
theorem Generators8Of
    (h2 : Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 4)
      = (5 : ℤ) • uSq 4)
    (h4 : Work.Thom.p2Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 4)
      = (10 : ℤ) • uFourth 4)
    (M : CP2CP2Model cppSSet)
    (hc : Submodule.span ℤ {M.c} = ⊤)
    (h1 : Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2) = M.p₁)
    (h2' : Work.Thom.p2Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2) = M.p₂) :
    Work.Drive.Generators8 := by
  obtain ⟨s1, s1a, s1b, s1h⟩ :=
    cp4NumbersOf h2 h4 cp4C cp4C_span (m := Work.Cohomology.kronH ℤ cp4SSet 8 (uFourth 4) cp4C)
      kronH_uFourth_pm_one rfl
  obtain ⟨s2, s2a, s2b, s2h⟩ := cp2cp2NumbersOf M hc h1 h2'
  refine ⟨cp4Smooth8Of cp4C cp4C_span, cp2cp2Smooth8Of M.c hc, s1h, s2h, ?_⟩
  show (cp4Smooth8Of cp4C cp4C_span).p1Sq * (cp2cp2Smooth8Of M.c hc).p2Num
    ≠ (cp4Smooth8Of cp4C cp4C_span).p2Num * (cp2cp2Smooth8Of M.c hc).p1Sq
  rw [s1a, s1b, s2a, s2b]
  rcases kronH_uFourth_pm_one with h | h <;> rw [h] <;> norm_num

end

end Work.Gen
