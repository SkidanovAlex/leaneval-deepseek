import Mathlib
import ChallengeDeps
import Submission.Work.Motivic.Defs
import Submission.Work.CrauderKatz.BlowUp.exists_cInv_ne_zero_of_openImmersion_missingDivisor
import Submission.Work.MotA.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# `divCount` is the exceptional weight of the inverse of a basic-open immersion

The bridge between the commutative-algebraic definition `Work.MotA.divCount` and the invariant
`Work.Motivic.excCount`: for `F ≠ 0` the birational map `𝔸ⁿ ⤏ D(F)` inverse to the open immersion
of the basic open `D(F)` has exceptional divisors exactly the codimension-one points of `𝔸ⁿ` at
which `F` vanishes, so its weighted exceptional count is `divCount 𝕜 n F z`.

The mathematical input is
`Work.CrauderKatz.BlowUp.exDiv_partialIsoOfDense_symm` (the exceptional divisors of the inverse of
a dense open immersion are the codimension-one points off the open), together with
`Work.MotA.mem_basicOpen_iff` (`x ∉ D(F) ↔ F ∈ x.asIdeal`).
-/

noncomputable section

namespace Work.MotA

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants

/-- The inverse of the open immersion of a basic open has exactly the codimension-one points where
`F` vanishes as exceptional divisors. -/
theorem exDiv_basicOpenBirationalMap (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F : MvPolynomial (Fin n) 𝕜) (hF : F ≠ 0) [IrreducibleSpace ↑(basicOpen 𝕜 n F)] :
    exDiv (basicOpenBirationalMap 𝕜 n F hF) =
      {x : polySpec 𝕜 n | Order.coheight x = 1 ∧ F ∈ x.asIdeal} := by
  rw [basicOpenBirationalMap,
    Work.CrauderKatz.BlowUp.exDiv_partialIsoOfDense_symm (basicOpen_dense 𝕜 n F hF)]
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by
      by_contra h
      exact h2 ((mem_basicOpen_iff (𝕜 := 𝕜) (n := n) (F := F) (x := x)).mpr h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1,
      fun hmem => ((mem_basicOpen_iff (𝕜 := 𝕜) (n := n) (F := F) (x := x)).mp hmem) h2⟩

/-- The weight of the exceptional divisors of the birational map inverse to the open immersion
`D(F) ↪ 𝔸ⁿ` is `divCount 𝕜 n F z`. -/
theorem excCount_basicOpenBirationalMap (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F : MvPolynomial (Fin n) 𝕜) (hF : F ≠ 0)
    [IrreducibleSpace ↑(basicOpen 𝕜 n F)] {Z : Scheme.{0}} [Z.Over (Spec (.of 𝕜))] (z : Z) :
    excCount 𝕜 z (basicOpenBirationalMap 𝕜 n F hF) = divCount 𝕜 n F z := by
  rw [excCount, divCount, exDiv_basicOpenBirationalMap 𝕜 n F hF]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  tauto

end Work.MotA
