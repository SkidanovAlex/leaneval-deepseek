import Mathlib
import Submission.NumberField.TameTowerReduction
import Submission.Work.TameArithmetic.Defs
import Submission.Work.TameArithmetic.infinite_galoisGroup_of_presentation

/-!
# `Work.TameArithmetic.MartinetWall` -- the `MartinetTameWall` exit

**The point of this file.**  The seed's `Submission.NumberField.MartinetTameWall` is the
infinitude of the maximal pro-`2` extension of `ℚ` unramified outside `S` and at the infinite
places.  On this exit the *abstract-model* condition `IsProTwoModel` of `Assembly.lean` is not
needed at all: an abstract group only has to be *injected* into the Galois group, never to have
its own finite quotients realized arithmetically.  Concretely, `TamePro2Presentation` alone already
makes the presented group `G = FreeGroup (Fin 5) ⧸ ⟪rel⟫` a quotient-free subgroup of
`Γ = Gal(K/ℚ)`, and Golod--Shafarevich applied to the *presented* group (`4·6 = 24 < 25 = 5²`,
Chapter B, proved in this workspace) forces `G`, hence `Γ`, to be infinite.

Hence the single remaining arithmetic input of the `MartinetTameWall` exit is

  `Work.TameArithmetic.TameRelationBound`

-- the Shafarevich--Koch relation bound (a pro-`2` presentation with five generators and at most
six relators) -- and the whole route is

  `TameRelationBound → MartinetTameWall → Submission.exists_totallyReal_discr_le`
  (`Submission.NumberField.exists_totallyReal_discr_le_of_martinetTameWall`, proved in the seed).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open scoped Classical
open scoped NumberField
open NumberField

namespace Work.TameArithmetic

/-- **The Shafarevich--Koch relation bound implies THE WALL.**

From the pro-`2` presentation datum `P` of a maximal tame pro-`2` extension `K` of `ℚ` we obtain
that `Γ = Gal(K/ℚ)` is infinite (`infinite_galoisGroup_of_presentation`), and the level properties
required by `MartinetTameWall` are the clauses of `IsMaximalTamePro2`. -/
theorem martinetTameWall_of_relationBound (h : TameRelationBound) :
    Submission.NumberField.MartinetTameWall := by
  obtain ⟨K, iK, iAK, iGK, hmax, ⟨P⟩⟩ := h
  letI : Field K := iK
  letI : Algebra ℚ K := iAK
  letI : IsGalois ℚ K := iGK
  refine Submission.NumberField.martinetTameWall_of_infinite_maximal_proP
    (F := ℚ) (S := primesS) primesS_prime primesS_odd ?_
    (infinite_galoisGroup_of_presentation hmax P)
  intro L hnumL hfdL hgalL
  -- pin the algebra structure on `↥L` to `L.algebra'`, which is the one used in the statement of
  -- `Submission.NumberField.MartinetTameWall` (and in `Submission.NumberField.martinetTameWall_of_...`)
  letI : Algebra ℚ ↥L := L.algebra'
  haveI : NumberField ↥L := hnumL
  haveI : FiniteDimensional ℚ ↥L := hfdL
  haveI : IsGalois ℚ ↥L := hgalL
  exact hmax.2.2 ↥L L.val (fun _ _ hxy => Subtype.ext hxy)

/-- **The benchmark statement from the relation bound alone**: the tame Martinet route with the
abstract-model condition dispensed with. -/
theorem exists_totallyReal_discr_le_of_relationBound (h : TameRelationBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d :=
  Submission.NumberField.exists_totallyReal_discr_le_of_martinetTameWall
    (martinetTameWall_of_relationBound h)

end Work.TameArithmetic
