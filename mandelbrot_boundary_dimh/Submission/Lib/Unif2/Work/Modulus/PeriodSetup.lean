import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.Work.Modulus.Defs
import Submission.Lib.Unif2.Work.Modulus.puncturedHarmonic

import Submission.Lib.Unif2.Conjugate

/-!
# The period homomorphism of the conjugate of the Green function

This module sets up, for the punctured surface `U = X ∖ {z₀}` and the harmonic function `E|_U`, the
machinery of `Submission.Conjugate`: the *conjugate étale space* of `E` over `U`, the fact that its
first projection is a covering map, and the resulting **period homomorphism**

`Work.Modulus.greenPeriodHom hE u₀ : Additive (FundamentalGroup U u₀) →+ ℝ`,

whose value on a loop is the drift of the harmonic conjugate of `E` around that loop.  The
holomorphic modulus `exp (-(E + iE*))` is single-valued precisely when this homomorphism takes
values in `2πℤ`, which is the content of the "periods of the Green function are multiples of `2π`"
step of uniformization.  Two results are proved elsewhere in this directory:
`Work.Modulus.greenPeriodHom_two_pi_zmultiples` (the period of a loop that is null-homotopic in `X`
is a multiple of `2π`, the "residue on a filling disc" computation) and
`Work.Modulus.hasTrivialModulusMonodromy_of_periods` (if *all* periods are multiples of `2π`, the
multivalued modulus descends to a single-valued holomorphic function).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

noncomputable section

open Filter Set
open Classical

namespace Work.Modulus

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The Green function restricted to the punctured surface `X ∖ {z₀}`. -/
def greenPunctured (z₀ : X) (E : X → ℝ) : (puncturedOpens z₀) → ℝ := fun u => E u.1

/-- The topology on `U × ℝ` (the conjugate étale space of `E` over the punctured surface). -/
def greenConjTopology (z₀ : X) (E : X → ℝ) : TopologicalSpace ((puncturedOpens z₀) × ℝ) :=
  Submission.conjTopology (greenPunctured z₀ E)

/-- The harmonicity of `E` on the punctured surface, in the form used by the conjugate machinery. -/
theorem greenPunctured_harmonic {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) :
    Submission.HarmonicOnX (greenPunctured z₀ E) Set.univ :=
  puncturedHarmonic (X := X) (z₀ := z₀) (E := E) hE

/-- The first projection of the conjugate étale space of `E` over the punctured surface is a
covering map. -/
theorem green_isCoveringMap {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) :
    @IsCoveringMap ((puncturedOpens z₀) × ℝ) (puncturedOpens z₀) (greenConjTopology z₀ E)
      inferInstance Prod.fst :=
  @Submission.isCoveringMap_fst_conjTopology (puncturedOpens z₀) _ _ _ (greenPunctured z₀ E)
    (greenPunctured_harmonic hE)

/-- The translation action on the conjugate étale space of `E` is continuous. -/
theorem green_continuous_conjShift {z₀ : X} {E : X → ℝ} (c : ℝ) :
    @Continuous ((puncturedOpens z₀) × ℝ) ((puncturedOpens z₀) × ℝ)
      (greenConjTopology z₀ E) (greenConjTopology z₀ E) (Submission.conjShift c) :=
  @Submission.continuous_conjShift (puncturedOpens z₀) _ _ _ (greenPunctured z₀ E) c

/-- **The period homomorphism of the conjugate of the Green function.**  Its value on a loop of the
punctured surface is the drift of the harmonic conjugate of `E` around that loop; the multivalued
function `Φ = exp (-(E + iE*))` is single-valued exactly when all these values are multiples of
`2π`. -/
noncomputable def greenPeriodHom {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) (u₀ : puncturedOpens z₀) :
    Additive (FundamentalGroup (puncturedOpens z₀) u₀) →+ ℝ :=
  Submission.conjPeriodHom (X := puncturedOpens z₀) (htop := greenConjTopology z₀ E) u₀
    (Submission.conjFiberPt u₀ 0) (green_isCoveringMap hE)
    (fun c => green_continuous_conjShift (z₀ := z₀) (E := E) c)

theorem greenPeriodHom_apply {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) (u₀ : puncturedOpens z₀)
    (γ : FundamentalGroup (puncturedOpens z₀) u₀) :
    greenPeriodHom hE u₀ (Additive.ofMul γ) =
      Submission.conjPeriod (X := puncturedOpens z₀) (htop := greenConjTopology z₀ E) u₀
        (Submission.conjFiberPt u₀ 0) (green_isCoveringMap hE) γ := rfl

end Work.Modulus
