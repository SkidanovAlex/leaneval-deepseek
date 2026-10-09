/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local units are compact at all but finitely many places

For a number field `K` and a place `v` of `K`, the group `𝒪_vˣ` of local units is all of `K_vˣ`
at an archimedean place (which is *not* compact), while at a nonarchimedean place it is the
group of units of the compact valuation ring `𝒪_v` of the completion `K_v`, hence compact.

Because a number field has only finitely many archimedean places, the local units are compact at
*all but finitely many* places: they are compact at every finite place.  This is the statement
proved here, and it is exactly the input needed to know that the restricted product defining the
idèles is a product of compact groups outside a finite set (so that the "unitary idèles" have a
chance of being compact).

## Main result

* `NK.GlobalCFT.LocalField.globalCFT_localUnits_isCompact_eventually`: the local units are compact for all
  but finitely many places of `K`.
-/

set_option autoImplicit false

open scoped NumberField

open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.LocalField

/-- **The local units at a finite place are compact.**  The ring of integers `𝒪_v` of the
`v`-adic completion of a number field is compact (`compactSpace_adicCompletionIntegers`), and the
units of a compact submonoid of a topological monoid form a compact subset of the unit group
(`Submonoid.units_isCompact`). -/
private theorem isCompact_localUnits_ofFinite {K : Type*} [Field K] [NumberField K]
    (q : HeightOneSpectrum (𝓞 K)) :
    IsCompact ((NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q) :
      Set ((q.adicCompletion K)ˣ))) := by
  have hc : CompactSpace (q.adicCompletionIntegers K) :=
    Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers K q
  -- the valuation ring, as a subset of the completion, is compact
  have hS : IsCompact ((q.adicCompletionIntegers K : Set (q.adicCompletion K))) := by
    have h := (Subtype.isCompact_iff (p := fun x : q.adicCompletion K =>
      x ∈ q.adicCompletionIntegers K) (s := Set.univ)).mp isCompact_univ
    simpa using h
  -- and the units of a compact submonoid are compact in the unit group
  have hunits := Submonoid.units_isCompact hS
  simpa [NK.GlobalCFT.Place.localUnits_ofFinite] using hunits

/-- **The local units are compact at all but finitely many places**: they are compact at every
nonarchimedean place, and there are only finitely many archimedean places. -/
theorem globalCFT_localUnits_isCompact_eventually {K : Type*} [Field K] [NumberField K] :
    ∀ᶠ v in Filter.cofinite, IsCompact (NK.GlobalCFT.Place.localUnits K v :
      Set ((NK.GlobalCFT.Place.localField K v)ˣ)) := by
  rw [Filter.eventually_cofinite]
  -- the places where the local units fail to be compact are archimedean, and there are only
  -- finitely many of those
  refine (Set.finite_range (fun w : InfinitePlace K =>
    (NK.GlobalCFT.Place.ofInfinite w : NK.GlobalCFT.Place K))).subset ?_
  intro v hv
  by_cases hinv : NK.GlobalCFT.Place.IsInfinite v
  · obtain ⟨w, rfl⟩ := NK.GlobalCFT.Place.isInfinite_iff.mp hinv
    exact Set.mem_range_self w
  · -- `v` is a finite place, where the local units are compact
    exfalso
    have hf : NK.GlobalCFT.Place.IsFinite v := hinv
    obtain ⟨q, rfl⟩ := NK.GlobalCFT.Place.isFinite_iff.mp hf
    exact hv (isCompact_localUnits_ofFinite q)

end NK.GlobalCFT.LocalField
