import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Tools
import Submission.NK.LocalReciprocityLubinTate.Unramified.subring_subset_integer_of_isCompact

/-!
# The group of units of a `p`-adic completion is the group `U^0` of the unit filtration

For a number field `K` and a finite place `Q`, the units of the completion `F = Q.adicCompletion K`
are the first term `U^0` of the higher unit filtration used everywhere in the chapter:

`NK.LocalReciprocityLubinTate.adicUnits K Q = NK.LocalReciprocityLubinTate.higherUnits F 0`.

The two sides are the images in `Fˣ` of the units of two rings of integers of `F`:

* `adicUnits K Q` is the image of `(Q.adicCompletionIntegers K)ˣ`, where the ring of integers of the
  completion is the unit ball `{x | Valued.v x ≤ 1}` of the canonical (`ℤᵐ⁰`-valued) valuation of
  the completion;
* `higherUnits F 0 = (principalUnits F 0).map ... = 𝒪[F]ˣ ↪ Fˣ`, where `𝒪[F]` is the unit ball
  `{x | valuation F x ≤ 1}` of the *valuative relation* with which `F` is equipped as a
  nonarchimedean local field.

These two unit balls are equal: both are compact subrings of `F`, and a compact subring of a field
with a valuative topology lies in the unit ball of every compatible valuation
(`NK.LocalReciprocityLubinTate.Unramified.subring_subset_integer_of_isCompact`, applied once for
each of the two valuations).  This is the content of
`adicCompletionIntegers_toSubring_eq_integer` below; the statement of the present lemma is then a
formal consequence.
-/

set_option linter.style.haveILetI false

open scoped ValuativeRel

namespace NK.LocalReciprocityLubinTate.Unramified

universe u

/-- **The ring of integers of the `Q`-adic completion is the unit ball of its valuative relation.**

`(Q.adicCompletionIntegers K).toSubring` is the unit ball for the canonical valuation `Valued.v`
of the completion (with values in `ℤᵐ⁰`), while `(ValuativeRel.valuation F).integer` is the unit ball
for the valuative relation `≤ᵥ` with which `F` is equipped as a nonarchimedean local field.  The two
agree because each is a compact subring, hence contained in the unit ball of the other valuation
(`subring_subset_integer_of_isCompact`). -/
theorem adicCompletionIntegers_toSubring_eq_integer {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (Q.adicCompletionIntegers K).toSubring =
      ((ValuativeRel.valuation (Q.adicCompletion K)).integer :
        Subring (Q.adicCompletion K)) := by
  -- the unit ball of the canonical valuation of the completion is compact
  have hAcomp : IsCompact ((Q.adicCompletionIntegers K).toSubring :
      Set (Q.adicCompletion K)) := by
    have hcs : CompactSpace (Q.adicCompletionIntegers K) :=
      Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers K Q
    rw [isCompact_iff_compactSpace]
    change CompactSpace (Q.adicCompletionIntegers K)
    exact hcs
  -- ... and so is the unit ball of the valuative relation (it is a closed ball of a local field)
  have hBcomp : IsCompact (((ValuativeRel.valuation (Q.adicCompletion K)).integer :
      Subring (Q.adicCompletion K)) : Set (Q.adicCompletion K)) := by
    have h := IsNonarchimedeanLocalField.isCompact_closedBall (Q.adicCompletion K)
      (1 : ValuativeRel.ValueGroupWithZero (Q.adicCompletion K))
    change IsCompact ({x : Q.adicCompletion K |
      (ValuativeRel.valuation (Q.adicCompletion K)) x ≤ 1} : Set (Q.adicCompletion K))
    exact h
  refine Subring.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · -- the compact unit ball `A` of `Valued.v` lies in the unit ball of the valuative relation
    exact subring_subset_integer_of_isCompact (v := ValuativeRel.valuation (Q.adicCompletion K))
      ((Q.adicCompletionIntegers K).toSubring) hAcomp hx
  · -- conversely: the compact unit ball `B` of the valuative relation lies in the unit ball of
    -- `Valued.v`, for which we pass to the (equivalent) valuative relation induced by `Valued.v`
    set B : Subring (Q.adicCompletion K) :=
      ((ValuativeRel.valuation (Q.adicCompletion K)).integer)
    have hxB : x ∈ (B : Set (Q.adicCompletion K)) := hx
    have hBc : IsCompact (B : Set (Q.adicCompletion K)) := hBcomp
    letI inst0 : ValuativeRel (Q.adicCompletion K) := ValuativeRel.ofValuation
      (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)))
    haveI hcompat : (Valued.v (R := Q.adicCompletion K)
        (Γ₀ := WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    haveI htop : IsValuativeTopology (Q.adicCompletion K) :=
      IsValuativeTopology.of_mem_nhds_zero_iff_vle _
        (fun {s} => Valued.is_topological_valuation s)
    exact subring_subset_integer_of_isCompact
      (v := (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))))
      B hBc hxB

theorem adicUnits_eq_higherUnits_zero {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NK.LocalReciprocityLubinTate.adicUnits K Q =
      NK.LocalReciprocityLubinTate.higherUnits (Q.adicCompletion K) 0 := by
  have hAB := adicCompletionIntegers_toSubring_eq_integer Q
  rw [NK.LocalReciprocityLubinTate.adicUnits,
      NK.LocalReciprocityLubinTate.higherUnits,
      NK.LocalReciprocityLubinTate.principalUnits_zero]
  -- Both sides are the image of the units of a subring of `F`; the coercion `↥R` of a
  -- `ValuationSubring` is its underlying `Subring`, so the goal is stated with the two
  -- `Subring`s exposed, on which `hAB` rewrites.
  change (⊤ : Subgroup (↥((Q.adicCompletionIntegers K).toSubring))ˣ).map
      (Units.map (algebraMap ↥((Q.adicCompletionIntegers K).toSubring)
        (Q.adicCompletion K)).toMonoidHom) =
    (⊤ : Subgroup (↥((ValuativeRel.valuation (Q.adicCompletion K)).integer))ˣ).map
      (Units.map (Subring.subtype
        ((ValuativeRel.valuation (Q.adicCompletion K)).integer)).toMonoidHom)
  rw [hAB]
  rfl

end NK.LocalReciprocityLubinTate.Unramified
