import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Basic
import Submission.NK.LocalField.globalCFT_localField_locallyCompactSpace
import Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The completion of a number field at a finite place is a non-archimedean local field

For a number field `K` and a height-one prime `Q` of its ring of integers, the `Q`-adic
completion `F = Q.adicCompletion K` carries a canonical (rank one, discrete) valuation
`Valued.v : Valuation F ℤᵐ⁰`, induced by the completion of the `Q`-adic valuation of `K`.
The valuative relation on `F` is the equivalence class of this valuation, obtained by
`ValuativeRel.ofValuation`.

This file records that, with respect to that valuative relation:

* the topology of `F` is the valuative topology (`IsValuativeTopology`);
* `F` is locally compact: its ring of integers is compact, being a complete discrete
  valuation ring with finite residue field;
* the valuation is nontrivial (a uniformiser exists).

These are precisely the three defining conditions of `IsNonarchimedeanLocalField`, so
`F` is a non-archimedean local field.

## Main result

* `NK.LocalReciprocityLubinTate.Unramified.isNonarchimedeanLocalField_adicCompletion`.
-/

set_option linter.style.haveILetI false

open scoped WithZero

namespace NK.LocalReciprocityLubinTate.Unramified

open IsDedekindDomain.HeightOneSpectrum

universe u

/-- The completion of a number field at a finite place, equipped with the valuative relation
induced by its `Q`-adic valuation, is a non-archimedean local field. -/
theorem isNonarchimedeanLocalField_adicCompletion (K : Type u) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ inst : ValuativeRel (Q.adicCompletion K),
      letI := inst
      IsNonarchimedeanLocalField (Q.adicCompletion K) := by
  -- The valuative relation is the one induced by the canonical valuation of the completion.
  let inst0 : ValuativeRel (Q.adicCompletion K) :=
    ValuativeRel.ofValuation (Valued.v : Valuation (Q.adicCompletion K) ℤᵐ⁰)
  letI : ValuativeRel (Q.adicCompletion K) := inst0
  -- The two valuations coincide, so they are compatible.
  haveI hcompat : (Valued.v : Valuation (Q.adicCompletion K) ℤᵐ⁰).Compatible :=
    Valuation.Compatible.ofValuation (Valued.v : Valuation (Q.adicCompletion K) ℤᵐ⁰)
  -- The topology of the completion is the valuative topology of this valuation.
  haveI htop : IsValuativeTopology (Q.adicCompletion K) :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle (Valued.v : Valuation (Q.adicCompletion K) ℤᵐ⁰)
      (fun {s} => Valued.is_topological_valuation s)
  -- The completion is locally compact: its ring of integers is compact.
  haveI hlc : LocallyCompactSpace (Q.adicCompletion K) :=
    NK.LocalField.locallyCompactSpace_adicCompletion Q
  -- The valuation is nontrivial (equivalently, the completion is not a discrete field).
  haveI hnt : ValuativeRel.IsNontrivial (Q.adicCompletion K) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (Valued.v : Valuation (Q.adicCompletion K) ℤᵐ⁰)).mpr
      (inferInstance : (Valued.v : Valuation (Q.adicCompletion K) ℤᵐ⁰).IsNontrivial)
  exact ⟨inst0, IsNonarchimedeanLocalField.mk⟩

end NK.LocalReciprocityLubinTate.Unramified
