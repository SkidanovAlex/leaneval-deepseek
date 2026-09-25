import Mathlib
import Submission.Work.CMRealSubfield.RealSubfield.finrank_eq_two_mul_finrank_maximalRealSubfield

/-!
# The basic CM facts, in the exact forms the reduction consumes

For a CM field `K` with maximal real subfield `K⁺ = NumberField.maximalRealSubfield K`:

* `finrank_maximalRealSubfield_subtype` : `[K : K⁺] = 2`;
* `isTotallyReal_maximalRealSubfield` : `K⁺` is totally real;
* `isTotallyComplex_of_isCMField` : `K` is totally complex (so a CM field is never totally real,
  `not_isTotallyReal_of_isCMField`) — in particular the CM case of the reduction is not
  degenerate: the witness `L` genuinely is not totally real and the maximal real subfield is
  genuinely smaller.
-/

set_option linter.style.haveILetI false

open NumberField

namespace Work.CMRealSubfield

/-- A CM field is a quadratic extension of its maximal real subfield. -/
theorem finrank_maximalRealSubfield_subtype (K : Type*) [Field K] [NumberField K]
    [NumberField.IsCMField K] :
    Module.finrank (NumberField.maximalRealSubfield K) K = 2 :=
  Algebra.IsQuadraticExtension.finrank_eq_two (NumberField.maximalRealSubfield K) K

/-- The maximal real subfield of a number field is totally real (Mathlib's instance
`NumberField.isTotallyReal_maximalRealSubfield`, restated as a named theorem). -/
theorem isTotallyReal_maximalRealSubfield (K : Type*) [Field K] [CharZero K]
    [Algebra.IsAlgebraic ℚ K] :
    NumberField.IsTotallyReal (NumberField.maximalRealSubfield K) :=
  NumberField.isTotallyReal_maximalRealSubfield

/-- A CM field is totally complex (the class field of `IsCMField`). -/
theorem isTotallyComplex_of_isCMField (K : Type*) [Field K] [CharZero K]
    [NumberField.IsCMField K] : NumberField.IsTotallyComplex K :=
  NumberField.IsCMField.isTotallyComplex K

/-- A CM field is never totally real: it has a complex place. -/
theorem not_isTotallyReal_of_isCMField (K : Type*) [Field K] [NumberField K]
    [NumberField.IsCMField K] : ¬ NumberField.IsTotallyReal K := by
  intro h
  haveI := h
  have h1 : Module.finrank ℚ K = InfinitePlace.nrRealPlaces K :=
    NumberField.IsTotallyReal.finrank K
  have h3 : InfinitePlace.nrRealPlaces K = 0 :=
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero K
  exact (Module.finrank_pos (R := ℚ) (M := K)).ne' (by rw [h1, h3])

/-- **A checkable sufficient condition for the intermediate wall on a Galois level.**
If `K/ℚ` is Galois and totally complex, and all complex embeddings of `K` induce the *same*
complex conjugation `σ ∈ Gal(K/ℚ)`, then `K` is CM (Mathlib's
`NumberField.IsCMField.of_forall_isConj`), so `[K : K⁺] = 2` and the real-subfield reduction
applies to `K`. -/
theorem isCMField_of_forall_isConj (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] [IsGalois ℚ K] {σ : K ≃ₐ[ℚ] K}
    (hσ : ∀ φ : K →+* ℂ, NumberField.ComplexEmbedding.IsConj φ σ) :
    NumberField.IsCMField K :=
  NumberField.IsCMField.of_forall_isConj K hσ

/-- A totally complex **abelian** extension of `ℚ` is CM (Mathlib's
`NumberField.IsCMField.of_isAbelianGalois`); in particular every level of an abelian tower of
totally complex fields satisfies the hypothesis of the real-subfield reduction. -/
theorem isCMField_of_isAbelianGalois (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] [IsAbelianGalois ℚ K] : NumberField.IsCMField K :=
  NumberField.IsCMField.of_isAbelianGalois K

/-- **The CM-extension form.**  A totally complex quadratic extension `L` of a totally real
field `F` is CM (Mathlib's `NumberField.IsCMField.ofCMExtension`), and by
`NumberField.CMExtension.equivMaximalRealSubfield` the base `F` is (isomorphic to) the maximal
real subfield `L⁺`.  This is the form in which CM fields are usually constructed. -/
theorem isCMField_of_isQuadraticExtension (F K : Type*) [Field F] [NumberField.IsTotallyReal F]
    [Field K] [NumberField K] [NumberField.IsTotallyComplex K] [Algebra F K]
    [Algebra.IsQuadraticExtension F K] : NumberField.IsCMField K :=
  NumberField.IsCMField.ofCMExtension F K

end Work.CMRealSubfield
