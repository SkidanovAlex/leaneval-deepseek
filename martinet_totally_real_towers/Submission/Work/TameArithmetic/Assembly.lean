import Mathlib
import Submission.NumberField.TameGolodShafarevichReduction
import Submission.GroupTheory.GolodShafarevichFromCommons
import Submission.Work.TameArithmetic.Defs
import Submission.Work.TameArithmetic.residuallyFinite_presentedGroup
import Submission.Work.TameArithmetic.card_le_of_generating_presentedGroup
import Submission.Work.TameArithmetic.isPGroup_two_quotient_of_model
import Submission.Work.TameArithmetic.realization_of_model
import Submission.Work.TameArithmetic.isProTwoModel_of_realization

/-!
# `Work.TameArithmetic.Assembly` -- the tame Golod--Shafarevich route

**STATUS.**  Everything here is proved from the single named arithmetic input
`Work.TameArithmetic.TameArithmeticInput` (which packages the Shafarevich--Koch relation bound and
the abstract-model condition, see `Defs.lean`): the theorem

  `tameGolodShafarevichInput_of_arithmeticInput : TameArithmeticInput →
      Submission.NumberField.TameGolodShafarevichInput`

discharges the arithmetic input of the source paper's tame route in exactly the shape in which
`Submission.NumberField.exists_totallyReal_discr_le_of_tameGolodShafarevich` consumes it.

## The proof

Unpack `TameArithmeticInput`: a maximal tame pro-`2` extension `K` of `ℚ` (for
`S = primesS = {17,41,73,89,97}`), a pro-`2` presentation `P` of `Γ = Gal(K/ℚ)` with five
generators and at most six relators, and the model condition for
`G = presentedGroup P = FreeGroup (Fin 5) ⧸ ⟪P.rel⟫`.

* the generator type is `α = Fin 5`, so `0 < |α|` and `|α| = 5`;
* `4 · |P.rel| ≤ 4 · 6 = 24 ≤ 25 = |α|²` -- the counting of the tame route
  (`four_mul_le_sq_of_rel_card_le_six`);
* `α` is minimal: any generating finset of `G` has at least `5` elements, because `G ↠ (ℤ/2)^5`
  (the multiquadratic certificate, through the universal property of `K`) --
  `card_le_of_generating_presentedGroup`;
* `G` is residually finite -- `residuallyFinite_presentedGroup` (it is a dense finitely generated
  subgroup of the pro-`2` group `Γ = K ≃ₐ[ℚ] K`, which is residually finite as `K/ℚ` is algebraic
  and Galois);
* every finite quotient of `G` is a `2`-group -- `isPGroup_two_quotient_of_model`;
* every finite quotient of `G` is realized as the Galois group of a finite Galois extension of `ℚ`
  with `S`-supported different which is unramified at the infinite places (hence totally real) --
  `realization_of_model`.

Together with `Submission.GroupTheory.finitePGroupGolodShafarevich_of_commons` (Chapter B, proved
in this workspace) this gives the benchmark statement
`Submission.exists_totallyReal_discr_le` via
`Submission.NumberField.exists_totallyReal_discr_le_of_tameGolodShafarevich`.
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

/-- **The arithmetic input of the tame route implies the seed's `TameGolodShafarevichInput`.**

The witness is the presented group `G = FreeGroup (Fin 5) ⧸ ⟪P.rel⟫` of the pro-`2` presentation
of `Γ = Gal(K/ℚ)`: five generators, at most six relators, `4 · 6 ≤ 5²`, minimal generating set,
residually finite, all finite quotients `2`-groups, and each finite quotient realized by a finite
Galois extension of `ℚ` that is `S`-tame and unramified at the infinite places. -/
theorem tameGolodShafarevichInput_of_arithmeticInput (h : TameArithmeticInput) :
    Submission.NumberField.TameGolodShafarevichInput := by
  obtain ⟨K, iK, iAK, iGK, hmax, hP⟩ := h
  obtain ⟨P, hmodel⟩ := hP
  letI : Field K := iK
  letI : Algebra ℚ K := iAK
  letI : IsGalois ℚ K := iGK
  have halb : Algebra.IsAlgebraic ℚ K := hmax.1
  have hsub : TameSubClause K := hmax.2.2
  have hmin : ∀ S : Finset (presentedGroup P),
      Subgroup.closure (S : Set (presentedGroup P)) = ⊤ → 5 ≤ S.card :=
    card_le_of_generating_presentedGroup hmax P
  refine ⟨primesS, primesS_prime, primesS_odd, Fin 5, inferInstance, inferInstance, P.rel,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.succ_pos 4
  · exact four_mul_le_sq_of_rel_card_le_six P.rel_card
  · exact hmin
  · exact residuallyFinite_presentedGroup halb P
  · exact isPGroup_two_quotient_of_model hsub hmodel
  · exact realization_of_model hsub hmodel


/-- **The arithmetic input in the form of the goal's own realization clauses.**  If `K` is a
maximal tame pro-`2` extension of `ℚ`, `P` a pro-`2` presentation of `Γ = Gal(K/ℚ)` with five
generators and at most six relators, and every finite quotient of the presented group is a
`2`-group realized by an `S`-tame totally real Galois extension of `ℚ`, then the seed's
`TameGolodShafarevichInput` holds.

The point of this form is that it shows exactly where the arithmetic is: the two realization
clauses are *equivalent* to `IsProTwoModel K (presentedGroup P)`
(`realization_of_model` one way, `isProTwoModel_of_realization` back), so the whole arithmetic
content of the input is the **Shafarevich--Koch relation bound**, i.e. the existence of the
pro-`2` presentation `P` with `5` generators and at most `6` relators. -/
theorem tameGolodShafarevichInput_of_realizationData
    (h : ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : IsGalois ℚ K),
      Work.TameArithmetic.IsMaximalTamePro2 K ∧
        ∃ P : Work.TameArithmetic.TamePro2Presentation K,
          (∀ (N : Subgroup (Work.TameArithmetic.presentedGroup P)) [N.Normal],
            Finite (Work.TameArithmetic.presentedGroup P ⧸ N) →
              IsPGroup 2 (Work.TameArithmetic.presentedGroup P ⧸ N)) ∧
          (∀ (N : Subgroup (Work.TameArithmetic.presentedGroup P)) [N.Normal],
            Finite (Work.TameArithmetic.presentedGroup P ⧸ N) →
              ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra ℚ L)
                (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
                IsUnramifiedAtInfinitePlaces ℚ L ∧
                (∀ P' : Ideal (NumberField.RingOfIntegers L), P'.IsPrime → P' ≠ ⊥ →
                  P' ∣ differentIdeal (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers L) →
                  ∃ q ∈ Work.TameArithmetic.primesS,
                    P'.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) ∧
                Nonempty ((L ≃ₐ[ℚ] L) ≃* (Work.TameArithmetic.presentedGroup P ⧸ N)))) :
    Submission.NumberField.TameGolodShafarevichInput := by
  obtain ⟨K, iK, iAK, iGK, hmax, P, hquot, hreal⟩ := h
  letI : Field K := iK
  letI : Algebra ℚ K := iAK
  letI : IsGalois ℚ K := iGK
  exact tameGolodShafarevichInput_of_arithmeticInput
    ⟨K, iK, iAK, iGK, hmax, P, isProTwoModel_of_realization hmax hquot hreal⟩

/-- **The benchmark statement from the arithmetic input**, by the proved reduction
`Submission.NumberField.exists_totallyReal_discr_le_of_tameGolodShafarevich` and the finite
`p`-group Golod--Shafarevich inequality `Submission.GroupTheory.finitePGroupGolodShafarevich_of_commons`
(Chapter B, proved in this workspace). -/
theorem exists_totallyReal_discr_le_of_arithmeticInput (h : TameArithmeticInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d :=
  Submission.NumberField.exists_totallyReal_discr_le_of_tameGolodShafarevich
    (Submission.GroupTheory.finitePGroupGolodShafarevich_of_commons 2)
    (tameGolodShafarevichInput_of_arithmeticInput h)

end Work.TameArithmetic
