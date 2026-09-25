import Mathlib
import Submission.Work.TameArithmetic.Defs

namespace Work.TameArithmetic

/-- **The realization clause of the model condition.**  Every finite quotient `G ⧸ N` of a group
`G` modelling the maximal tame pro-`2` extension `K` of `ℚ` is realized as the Galois group
`Gal(L/ℚ)` of a finite Galois extension `L/ℚ` embedded in `K` with `S`-supported relative
different, unramified at the infinite places.  This is immediate from
`IsProTwoModel K G` (which supplies `L` and the embedding `L →ₐ[ℚ] K`) together with
`TameSubClause K` (which supplies the arithmetic properties of every finite Galois subextension
of `K`, namely: pro-`2`, different supported over `S = primesS`, unramified at `∞`). -/
theorem realization_of_model {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    (hsub : Work.TameArithmetic.TameSubClause K) {G : Type} [Group G]
    (hmodel : Work.TameArithmetic.IsProTwoModel K G) :
    ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra ℚ L)
        (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
        IsUnramifiedAtInfinitePlaces ℚ L ∧
        (∀ P : Ideal (NumberField.RingOfIntegers L), P.IsPrime → P ≠ ⊥ →
          P ∣ differentIdeal (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers L) →
          ∃ q ∈ Work.TameArithmetic.primesS, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) ∧
        Nonempty ((L ≃ₐ[ℚ] L) ≃* (G ⧸ N)) := by
  intro N _ hN
  obtain ⟨L, iL, iAL, iFD, iGal, φ, hinj, heq⟩ := hmodel N hN
  have hnum : NumberField L := NumberField.of_module_finite ℚ L
  have h := hsub L φ hinj
  exact ⟨L, iL, hnum, iAL, iFD, iGal, h.2.2, h.2.1, heq⟩

end Work.TameArithmetic
