import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.ModelGeometry

set_option synthInstance.maxHeartbeats 400000

/-!
# The model Thom class of the trivial bundle, over `ℚ`

`Work.Thom.ModelThom B n` (`Submission/Work/Thom/ModelThomDefs.lean`) states that the pair
`(B × ℝⁿ, B × Sⁿ⁻¹)` carries a class `τ` for which the *specific* cup map
`x ↦ π^*(x) ⌣ τ` is bijective in every degree.  It is proved over `ℤ`
(`Work.Thom.modelThom_all`), from the integral line-bundle Thom class, and that proof is
irreducibly `ℤ`-specific: `Work.Thom.ModelThom` has the coefficient ring hard-wired to `ℤ`, and
`H^*(X;ℤ) ⊗ ℚ ≠ H^*(X;ℚ)`, so the integral class cannot be transported.

This file fixes the **rational** statement, `Work.StemsB.ModelThomRat B n`, which is what the
rational (`ℚ`-coefficient) Wang transgression — the form the blueprint's C2 odd step consumes —
needs.  The route to it is recorded in `MODELTHOM_RAT_PLAN.md`: the rank-one case by the
"difference + connecting map" argument, then the ℚ port of the suspension-step induction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.StemsB

open CategoryTheory

noncomputable section

/-- `H^n(B;ℚ)`. -/
abbrev CohRat (n : ℕ) (B : Type) [TopologicalSpace B] :
    ModuleCat ℚ := Work.Cohomology.singularCohomology ℚ n (TopCat.of B)

/-- `H^n(B,A;ℚ)`. -/
abbrev RelCohRat (n : ℕ) (B : Type) [TopologicalSpace B] (A : Set B) :
    ModuleCat ℚ := Work.Cohomology.relCohomology ℚ (TopCat.of B) A n

/-- The projection `B × ℝⁿ → B`. -/
def projFstRat (B : Type) [TopologicalSpace B] (n : ℕ) :
    C(B × EuclideanSpace ℝ (Fin n), B) := ⟨Prod.fst, continuous_fst⟩

/-- **The model Thom class of rank `n` over `B`, over `ℚ`.**  The pair is
`(B × ℝⁿ, {p | p.2 ∈ Sⁿ⁻¹})`, and the class `τ` is required to make the *specific* cup map
`x ↦ π^*(x) ⌣ τ` bijective in every degree.  This is `Work.Thom.ModelThom B n` with `ℤ` replaced
by `ℚ`. -/
def ModelThomRat (B : Type) [TopologicalSpace B] (n : ℕ) : Prop :=
  ∃ τ : RelCohRat n (B × EuclideanSpace ℝ (Fin n)) {p | p.2 ∈ Work.Thom.mSph n},
    ∀ k, Function.Bijective (fun x : CohRat k B =>
      (Work.Thom.mixedCupC ℚ {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ Work.Thom.mSph n} k n)
        ((Work.Thom.CohMap (projFstRat B n) ℚ k).hom x) τ)

end

end Work.StemsB
