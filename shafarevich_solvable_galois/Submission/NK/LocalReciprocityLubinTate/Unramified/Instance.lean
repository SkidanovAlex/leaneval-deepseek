import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.LocalReciprocityLubinTate.Unramified.isNonarchimedeanLocalField_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local field structure of `Q.adicCompletion K`, as global instances

`NK.LocalReciprocityLubinTate.Unramified.isNonarchimedeanLocalField_adicCompletion` proves

`∃ inst : ValuativeRel (Q.adicCompletion K), letI := inst; IsNonarchimedeanLocalField (Q.adicCompletion K)`.

This file *extracts* the witness of that existence statement and registers the two pieces
`ValuativeRel (Q.adicCompletion K)` and `IsNonarchimedeanLocalField (Q.adicCompletion K)` as global
instances, so that the whole vocabulary of the chapter
(`residueCard`, `IsUniformizer`, `principalUnits`, `higherUnits`, `maximalIdealOfIntegers`, ...)
becomes available at `Q.adicCompletion K` by ordinary typeclass synthesis.

Before this file, statements such as "`π` is a uniformiser of `Q.adicCompletion K`" did not
typecheck at all: `IsUniformizer` is an abbreviation for `Valuation.IsUniformizer (ValuativeRel.valuation F)`,
and `ValuativeRel.valuation F` needed the instance.  This was the single blocking step for the
assembly of the Lubin–Tate tower over `Q.adicCompletion K`.

The instances are universe-polymorphic (`K : Type u`), matching the consumer
`NK.LocalCFT.ArtinReciprocity`, which is stated for fields in arbitrary universes.

## Main results

* `NK.LocalReciprocityLubinTate.Unramified.instValuativeRelAdicCompletion`;
* `NK.LocalReciprocityLubinTate.Unramified.instIsNonarchimedeanLocalFieldAdicCompletion`.

## Note on the choice of valuation

The witness valuation is `ValuativeRel.ofValuation (Valued.v : Valuation (Q.adicCompletion K) ℤᵐ⁰)`,
i.e. the equivalence class of the canonical `Q`-adic valuation of the completion.  Every statement
below is invariant under this choice (`ValuativeRel` is an equivalence class of valuations, and
`IsNonarchimedeanLocalField`, `IsUniformizer`, `residueCard` and the higher unit filtration are all
determined by it), but the particular witness matters for *statements that mention the valuation
explicitly*, e.g. `Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one`.
-/

open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalReciprocityLubinTate.Unramified

universe u

noncomputable section

/-- **The valuative relation of a `p`-adic field**: the equivalence class of the canonical
`Q`-adic valuation on the completion `Q.adicCompletion K` of a number field at a finite prime. -/
noncomputable instance instValuativeRelAdicCompletion (K : Type u) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ValuativeRel (Q.adicCompletion K) :=
  (isNonarchimedeanLocalField_adicCompletion K Q).choose

/-- **The completion of a number field at a finite prime is a non-archimedean local field**, as a
global instance.  Mathlib provides this for `ℚ_[p]` only through
`NK.LocalReciprocityLubinTate.isNonarchimedeanLocalField_padic`; for the completions of a general
number field the three defining conditions are proved in
`NK.LocalReciprocityLubinTate.Unramified.isNonarchimedeanLocalField_adicCompletion`. -/
instance instIsNonarchimedeanLocalFieldAdicCompletion (K : Type u) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsNonarchimedeanLocalField (Q.adicCompletion K) :=
  (isNonarchimedeanLocalField_adicCompletion K Q).choose_spec

/-- **The completion of a number field at a finite prime has characteristic zero.**

This is a re-export of `Commons.NumberTheory.NumberField.charZero_adicCompletion` as an *instance*, so
that the Lubin–Tate layer of the chapter — which is developed for characteristic-zero local fields —
applies to `Q.adicCompletion K` without a `haveI` at every statement. -/
instance instCharZeroAdicCompletion (K : Type u) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    CharZero (Q.adicCompletion K) :=
  Commons.NumberTheory.NumberField.charZero_adicCompletion Q

end

end NK.LocalReciprocityLubinTate.Unramified
