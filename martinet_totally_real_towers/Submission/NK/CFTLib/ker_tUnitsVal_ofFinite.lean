import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.TUnitsRank
import Submission.NK.GlobalCFTdeep.Herbrand.ker_tUnitsVal

/-!
# The kernel of the valuation map on `T`-units, pointwise

`Submission/Work/GlobalCFTdeep/Herbrand/ker_tUnitsVal.lean` proves

`LinearMap.ker (tUnitsVal T) = LinearMap.range (unitsToTUnits T)`

for an arbitrary set of places `T` of a number field `L`.  Here we record the *pointwise* form of
that statement: a `T`-unit has vanishing `T`-adic valuations if and only if it is a global unit
(an element of `(𝓞 L)ˣ`, viewed inside `Lˣ`).  This is the form in which the statement is used,
and in particular it applies verbatim to the finite set of places `{ofFinite q | q ∈ T}` attached
to a *finite* set `T` of finite places.
-/

open scoped NumberField
open IsDedekindDomain

namespace NK.GlobalCFTdeep

/-- **The kernel of the valuation map on `T`-units, pointwise.**  A `T`-unit `x` has all its
`T`-adic valuations trivial if and only if it is a global unit, i.e. lies in the image of
`(𝓞 L)ˣ → Lˣ`. -/
theorem ker_tUnitsVal_apply {L : Type} [Field L] [NumberField L] (T : Set (NK.GlobalCFT.Place L))
    (x : Additive (TUnits T)) :
    tUnitsVal T x = 0 ↔ ((Additive.toMul x : TUnits T) : Lˣ) ∈ globalUnits L := by
  rw [← LinearMap.mem_ker, Herbrand.ker_tUnitsVal T, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    rw [globalUnits, MonoidHom.mem_range]
    refine ⟨Additive.toMul y, ?_⟩
    have h : ((Additive.toMul x : TUnits T) : Lˣ) =
        (unitsToTUnitsHom T (Additive.toMul y) : Lˣ) := by
      rw [← hy]
      rfl
    rw [h, unitsToTUnitsHom_apply]
  · rw [globalUnits, MonoidHom.mem_range]
    rintro ⟨u, hu⟩
    refine ⟨Additive.ofMul u, Additive.toMul.injective ?_⟩
    rw [show Additive.toMul (unitsToTUnits T (Additive.ofMul u)) = unitsToTUnitsHom T u from rfl]
    apply Subtype.ext
    rw [unitsToTUnitsHom_apply]
    exact hu

end NK.GlobalCFTdeep

namespace NK.CFTLib

theorem ker_tUnitsVal_ofFinite (F : Type) [Field F] [NumberField F]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) :
    ∀ x : Additive (NK.GlobalCFTdeep.TUnits
        {w : NK.GlobalCFT.Place F | ∃ q ∈ T, w = NK.GlobalCFT.Place.ofFinite q}),
      NK.GlobalCFTdeep.tUnitsVal
          {w : NK.GlobalCFT.Place F | ∃ q ∈ T, w = NK.GlobalCFT.Place.ofFinite q} x = 0 ↔
        ((Additive.toMul x : NK.GlobalCFTdeep.TUnits
            {w : NK.GlobalCFT.Place F | ∃ q ∈ T, w = NK.GlobalCFT.Place.ofFinite q}) : Fˣ)
          ∈ NK.GlobalCFTdeep.globalUnits F := by
  intro x
  exact NK.GlobalCFTdeep.ker_tUnitsVal_apply
    {w : NK.GlobalCFT.Place F | ∃ q ∈ T, w = NK.GlobalCFT.Place.ofFinite q} x

end NK.CFTLib
