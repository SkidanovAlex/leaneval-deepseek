import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_abelian_local_base
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

namespace Commons.NumberTheory.NumberField.Completion

/-!
# The local norm index theorem (abelian case)

For a finite **abelian** Galois extension `E` of the local field `F = Q.adicCompletion K`
(the completion of a number field `K` at a finite place `Q`), the index of the norm group
`N_{E/F}(Eˣ)` in `Fˣ` equals the local degree `[E : F]`:

`Nat.card (Fˣ ⧸ range N_{E/F}) = Module.finrank F E`.

This is the abelian case of the norm index theorem of local class field theory
(Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. VII; Serre, *Local Fields*).

The computation is the shared-commons theorem
`natCard_quotient_units_range_norm_eq_card_of_abelian_local_base` (the general-base-field
abelian case, proved via the fundamental class / Tate's theorem route to local class field
theory together with the p-group case), applied with the base field `B = Q.adicCompletion K`,
together with the fundamental Galois-theoretic identity
`Nat.card (E ≃ₐ[F] E) = Module.finrank F E` of `IsGalois.card_aut_eq_finrank`.
-/

/-- **The abelian local norm index theorem.** -/
theorem natCard_quotient_units_range_norm_eq_finrank_of_abelian_local
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type*} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E]
    (hcomm : ∀ a b : E ≃ₐ[Q.adicCompletion K] E, a * b = b * a) :
    Nat.card ((Q.adicCompletion K)ˣ ⧸
        MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          E →* Q.adicCompletion K))) =
      Module.finrank (Q.adicCompletion K) E := by
  rw [natCard_quotient_units_range_norm_eq_card_of_abelian_local_base (K := K) Q
      (B := Q.adicCompletion K) (E := E) hcomm,
    IsGalois.card_aut_eq_finrank]

end Commons.NumberTheory.NumberField.Completion
