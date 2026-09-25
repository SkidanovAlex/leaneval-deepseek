import Mathlib
import Submission.Work.TameArithmetic.Defs

/-!
# `Work.TameArithmetic.isProTwoModel_of_realization`

The **realization direction** of the model condition: if every finite quotient of an abstract group
`G` is realized as the Galois group of a finite Galois extension `L/ℚ` which is unramified at the
infinite places and has `S`-supported relative different (`S = Work.TameArithmetic.primesS`), and
if moreover every finite quotient of `G` is a `2`-group, then `G` models the maximal tame pro-`2`
extension `K` of `ℚ` in the sense of `Work.TameArithmetic.IsProTwoModel K G`.

This is the converse of `Work.TameArithmetic.realization_of_model` / 
`Work.TameArithmetic.isPGroup_two_quotient_of_model`, and it is what turns an honest construction of
the finite quotients of `G` (with the correct arithmetic) into the abstract model condition used by
the tame Golod--Shafarevich assembly `Work.TameArithmetic.Assembly`.

The two ingredients are:

* the `2`-group hypothesis `hquot` propagates through the isomorphism `(L ≃ₐ[ℚ] L) ≃* (G ⧸ N)` to
  give `IsPGroup 2 (L ≃ₐ[ℚ] L)`, so that the *universal clause* of `K` (which requires a pro-`2`
  extension) applies to `L`;
* the universal clause `TameUnivClause K` then supplies a `ℚ`-algebra homomorphism `φ : L →ₐ[ℚ] K`,
  and `φ` is automatically injective because `L` is a field (this is the only place where the
  field structure of `L` enters the embedding requirement).

Note that no arithmetic is used here beyond the universal property of `K`: the `S`-supportedness of
the different and the unramifiedness at `∞` of `L` are hypotheses of the universal clause.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.TameArithmetic

theorem isProTwoModel_of_realization {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    (hmax : Work.TameArithmetic.IsMaximalTamePro2 K) {G : Type} [Group G]
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N))
    (hreal : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra ℚ L)
        (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
        IsUnramifiedAtInfinitePlaces ℚ L ∧
        (∀ P : Ideal (NumberField.RingOfIntegers L), P.IsPrime → P ≠ ⊥ →
          P ∣ differentIdeal (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers L) →
          ∃ q ∈ Work.TameArithmetic.primesS, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) ∧
        Nonempty ((L ≃ₐ[ℚ] L) ≃* (G ⧸ N))) :
    Work.TameArithmetic.IsProTwoModel K G := by
  intro N _ hfin
  obtain ⟨L, iF, iNF, iA, iFD, iGal, hunram, hdiff, heq⟩ := hreal N hfin
  letI := iF
  letI := iNF
  letI := iA
  letI := iFD
  letI := iGal
  obtain ⟨e⟩ := heq
  -- `L ≃ₐ[ℚ] L` is a `2`-group, being isomorphic to the finite `2`-group `G ⧸ N`.
  have hp : IsPGroup 2 (L ≃ₐ[ℚ] L) := IsPGroup.of_equiv (hquot N hfin) e.symm
  -- The universal property of `K` provides the embedding of `L` into `K`.
  obtain ⟨φ, -⟩ := hmax.2.1 L hp hdiff hunram
  exact ⟨L, iF, iA, iFD, iGal, φ, φ.injective, ⟨e⟩⟩

end Work.TameArithmetic
