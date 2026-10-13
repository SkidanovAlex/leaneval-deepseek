import Mathlib
import Submission.Work.DSG4b.GonfDefs
import Submission.Work.DSG4b.uRingKey.uRingFibre
import Submission.Work.DSG4b.minpolyQuotient.exists_mul_eq_zero_of_eval_eq_zero
import Submission.Work.DSG4b.finiteDimReduced.isField_localizationAtPrime_of_finiteDimensional_reduced

universe a

namespace Work.DSG4b.uRingKey

/-- **Key fibre fact of the `U`-part.**  Let `R` be a local ring, `S` a local `R`-algebra with
`𝔪_R S = 𝔪_S` and perfect residue field `L`, and `A = Work.DSG4b.uRing S` the quotient of
`MvPolynomial (AlgebraicClosure L) S` by the relations `uPoly S α (X_α)` (monic lifts of the minimal
polynomials over `L`), with canonical evaluation `Work.DSG4b.uEv S : A →+* AlgebraicClosure L`,
`X_α ↦ α`.  Then every element of `ker (uEv S)` is annihilated modulo the ideal `𝔪_R A` by an
element outside `ker (uEv S)`; equivalently, the localisation of `A ⧸ 𝔪_R A` at the image of
`ker (uEv S)` is `AlgebraicClosure L`, so that `𝔪_R B = 𝔪_B` for `B = (A)_{ker (uEv S)}`.

Route: `A ⧸ 𝔪_R A ≅ M := L[X_α : α ∈ K] ⧸ (minpoly L α)(X_α)` (coefficients reduce along
`IsLocalRing.residue S`, using `Work.DSG4b.uPoly_map`), and the companion lemma
`Work.DSG4b.minpolyQuotient.exists_mul_eq_zero_of_eval_eq_zero` gives the assertion for `M`; the
map `M → A ⧸ 𝔪_R A` is surjective and compatible with the evaluations. -/
theorem uRing_ker_exists_mul_mem (R : Type a) [CommRing R] [IsLocalRing R]
    (S : Type a) [CommRing S] [IsLocalRing S] (φ : R →+* S)
    (hmax : (IsLocalRing.maximalIdeal R).map φ = IsLocalRing.maximalIdeal S)
    [PerfectField (IsLocalRing.ResidueField S)] :
    ∀ a ∈ RingHom.ker (uEv S), ∃ s, s ∉ RingHom.ker (uEv S) ∧
      s * a ∈ (IsLocalRing.maximalIdeal R).map ((uRingAlg S).comp φ) := by
  intro a ha
  -- the fibre `uFibre S ≅ uRing S ⧸ 𝔪_R uRing S`
  have hker : RingHom.ker (uRed S)
      = (IsLocalRing.maximalIdeal R).map ((uRingAlg S).comp φ) := uRed_ker_eq_aux R S φ hmax
  have hsurj : Function.Surjective (uRed S) := uRed_surjective S
  have hcomp : uEv S = (uFibreEval S).comp (uRed S) := uEv_eq_uFibreEval_comp_uRed S
  -- the companion statement for the fibre, evaluated at the elements `α`
  have hmain : ∀ m : uFibre S, uFibreEvalAlg S m = 0 →
      ∃ t, uFibreEvalAlg S t ≠ 0 ∧ t * m = 0 :=
    Work.DSG4b.minpolyQuotient.exists_mul_eq_zero_of_eval_eq_zero
      (IsLocalRing.ResidueField S) (uClosure S) (uFibreEvalAlg S)
      (fun α => uFibreEvalAlg_mk_X S α)
  -- the image of `a` in the fibre is killed by the evaluation
  have hzero : uFibreEvalAlg S (uRed S a) = 0 := by
    change uFibreEval S (uRed S a) = 0
    rw [← RingHom.comp_apply, ← hcomp]
    exact RingHom.mem_ker.mp ha
  obtain ⟨t, ht, htm⟩ := hmain (uRed S a) hzero
  obtain ⟨s, hs⟩ := hsurj t
  refine ⟨s, ?_, ?_⟩
  · -- `s ∉ ker (uEv S)` because its image `t` is not killed by the fibre evaluation
    intro hs0
    refine ht ?_
    have h1 : uFibreEvalAlg S t = uEv S s := by
      change uFibreEval S t = uEv S s
      rw [← hs, hcomp]
      rfl
    rw [h1]; exact hs0
  · -- `s * a ∈ 𝔪_R A` because its image in the fibre is `t * (image of a) = 0`
    rw [← hker, RingHom.mem_ker]
    have h2 : uRed S (s * a) = t * uRed S a := by rw [map_mul, hs]
    rw [h2, htm]

end Work.DSG4b.uRingKey
