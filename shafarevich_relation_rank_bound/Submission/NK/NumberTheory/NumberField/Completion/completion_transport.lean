import Mathlib
import Submission.NK.NumberTheory.NumberField.Completion.place_transport

/-!
# Transport of the `Q`-adic completion along an isomorphism of number fields

Last ingredient of §10 step 2 of `NOTE_session18_divisibility_route.md`:  the isometry
`valuation_ringOfIntegersRingEquiv` (`place_transport.lean`) shows that a `ℚ`-algebra isomorphism
`e : K ≃ₐ[ℚ] K₀` of number fields carries the `Q`-adic valued field `K` to the `Q₀`-adic valued
field `K₀`.  Here we deduce that the completions are isomorphic:
`Q.adicCompletion K ≃+* Q₀.adicCompletion K₀` for `Q₀ = heightOneSpectrumMap e Q`.

Route: the composite `WithVal (Q.valuation K) →+* Q₀.adicCompletion K₀` is continuous (its
valuation is transported by the isometry), hence extends to the completion
(`UniformSpace.Completion.extensionHom`); doing the same in the other direction and comparing on the
dense image gives the ring equivalence.
-/

universe u v

open IsDedekindDomain
open scoped WithZero

namespace Commons.NumberTheory.NumberField.Completion

variable {K K₀ : Type*} [Field K] [NumberField K] [Field K₀] [NumberField K₀]

/-- The continuous ring hom `WithVal (Q.valuation K) →+* Q₀.adicCompletion K₀` obtained from the
isomorphism `e` and the canonical embedding of `K₀` in its completion. -/
noncomputable def completionMapHom (e : K ≃ₐ[ℚ] K₀)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    WithVal (Q.valuation K) →+* (heightOneSpectrumMap e Q).adicCompletion K₀ :=
  (algebraMap K₀ ((heightOneSpectrumMap e Q).adicCompletion K₀)).comp
    ((e : K →+* K₀).comp (WithVal.equiv (Q.valuation K)).toRingHom)

/-- The canonical embedding of a number field in its `Q`-adic completion preserves the valuation.

The two `rfl`-step unfoldings are: `algebraMap K (adicCompletion K Q) y` is the `WithVal`-coercion
into the underlying completion (`AdicValuation.lean`), and the valuation on `adicCompletion K Q` is
`Valued.v.comap (adicCompletion.equiv K Q).toRingHom`. -/
lemma val_algebraMap_adicCompletion (Q : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers K)) (y : K) :
    Valued.v (algebraMap K (Q.adicCompletion K) y) = Q.valuation K y := by
  rw [show algebraMap K (Q.adicCompletion K) y =
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion
        ((WithVal.equiv (Q.valuation K)).symm y : (Q.valuation K).Completion) from rfl]
  rw [show Valued.v (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion
      ((WithVal.equiv (Q.valuation K)).symm y : (Q.valuation K).Completion)) =
      Valued.v ((WithVal.equiv (Q.valuation K)).symm y : (Q.valuation K).Completion) from rfl]
  rw [Valued.valuedCompletion_apply]
  rw [show Valued.v ((WithVal.equiv (Q.valuation K)).symm y : WithVal (Q.valuation K)) =
      (Q.valuation K) (((WithVal.equiv (Q.valuation K)).symm y : WithVal (Q.valuation K)).ofVal)
      from rfl]
  rw [WithVal.equiv_symm_apply]

/-- **The valuation of `completionMapHom` is the valuation of the source.**  This is the whole
arithmetic content of the continuity of the completion map, and it follows from the isometry
`valuation_ringOfIntegersRingEquiv` plus `val_algebraMap_adicCompletion`. -/
lemma completionMapHom_val (e : K ≃ₐ[ℚ] K₀)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : WithVal (Q.valuation K)) :
    Valued.v (completionMapHom e Q x) = Valued.v x := by
  rw [completionMapHom, RingHom.comp_apply, RingHom.comp_apply,
    val_algebraMap_adicCompletion]
  rw [show (WithVal.equiv (Q.valuation K)).toRingHom x = x.ofVal from
    WithVal.equiv_apply (Q.valuation K) x]
  rw [show Valued.v x = (Q.valuation K) (x : WithVal (Q.valuation K)).ofVal from rfl]
  exact valuation_ringOfIntegersRingEquiv e Q x.ofVal

/-! ## What remains

`completionMapHom` is continuous (the valuation of the image is `Valued.v x`, by
`valuation_ringOfIntegersRingEquiv`, so the `Valued`-balls pull back), hence extends to the
completion by `UniformSpace.Completion.extensionHom`; the same in the other direction and a
comparison on the dense image (`Continuous.ext_on`-style, since both composites are continuous and
agree on the image of `WithVal.equiv`) give mutually inverse ring homs, and `RingEquiv.ofBijective`
finishes.  The only friction encountered is the unfolding of
`algebraMap K₀ (adicCompletion K₀ Q₀)` as the canonical `WithVal`-coercion into the completion
(`AdicValuation.lean`: `algebraMap := Completion.coeRingHom.comp (algebraMap S (WithVal …))`);
with `Valued.valuedCompletion_apply` the valuation computation is then `rfl`-level.
See `NOTE_session18_divisibility_route.md` §16. -/

end Commons.NumberTheory.NumberField.Completion
