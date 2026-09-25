import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.TUnitsRank

/-!
# The kernel of the valuation map on `T`-units

Let `L` be a number field and `T` a set of places of `L`.  The `T`-units `TUnits T` are the
units of `L` which are local units outside `T`, and `tUnitsVal T` records the `q`-adic
valuations of a `T`-unit at the finite places `q ∈ T`.

The kernel of this valuation map consists of the `T`-units all of whose finite valuations
vanish.  Since a `T`-unit already has trivial valuation outside `T`, such an element has
trivial valuation at *every* finite place, hence is integral and has integral inverse: it is
a global unit of `𝓞 L`.  This is the statement of `ker_tUnitsVal`.
-/

open NK.GlobalCFT IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFTdeep

/-- The kernel of the `T`-adic valuation map on the `T`-units is the group of units of `𝓞 L`:
a `T`-unit with vanishing valuation at every finite place in `T` is integral with integral
inverse, i.e. a global unit (and conversely, global units have all finite valuations `1`). -/
theorem ker_tUnitsVal {L : Type} [Field L] [NumberField L] (T : Set (NK.GlobalCFT.Place L)) :
    LinearMap.ker (NK.GlobalCFTdeep.tUnitsVal (L := L) T) =
      LinearMap.range (NK.GlobalCFTdeep.unitsToTUnits (L := L) T) := by
  open scoped NumberField in
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · -- A `T`-unit killed by the valuation map has all its finite valuations trivial.
    intro hx
    set a : Lˣ := ((Additive.toMul x : TUnits T) : Lˣ) with ha
    have hval : ∀ q : HeightOneSpectrum (𝓞 L), q.valuation L (a : L) = 1 := by
      intro q
      by_cases hq : Place.ofFinite q ∈ T
      · have h1 := congrFun hx (⟨q, hq⟩ : SSet T)
        rw [tUnitsVal_apply] at h1
        rw [← ha] at h1
        exact (expUnit_eq_zero_iff q a).mp h1
      · have h2 := (mem_TUnits_iff_expUnit T).mp (Additive.toMul x).2 q hq
        rw [← ha] at h2
        exact (expUnit_eq_zero_iff q a).mp h2
    -- Hence `a` and its inverse are both integral over `𝓞 L`.
    have hval_inv : ∀ q : HeightOneSpectrum (𝓞 L), q.valuation L ((a⁻¹ : Lˣ) : L) = 1 := by
      intro q
      rw [← (expUnit_eq_zero_iff q a⁻¹), expUnit_inv, (expUnit_eq_zero_iff q a).mpr (hval q),
        neg_zero]
    obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one L (a : L)
        (fun q => le_of_eq (hval q))
    obtain ⟨w, hw⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one L ((a⁻¹ : Lˣ) : L)
        (fun q => le_of_eq (hval_inv q))
    have hzw : z * w = 1 := by
      apply IsFractionRing.injective (𝓞 L) L
      rw [map_mul, map_one, hz, hw, Units.mul_inv]
    have hwz : w * z = 1 := by
      apply IsFractionRing.injective (𝓞 L) L
      rw [map_mul, map_one, hw, hz, Units.inv_mul]
    -- Thus `z` is a unit of `𝓞 L` mapping to `a`, i.e. to `x`.
    let u : (𝓞 L)ˣ := ⟨z, w, hzw, hwz⟩
    have hmain : unitsToTUnitsHom T u = Additive.toMul x := by
      apply Subtype.ext
      rw [unitsToTUnitsHom_apply]
      apply Units.ext
      rw [show ((Units.map (algebraMap (𝓞 L) L).toMonoidHom u : Lˣ) : L)
            = algebraMap (𝓞 L) L (u : 𝓞 L) from rfl]
      change algebraMap (𝓞 L) L z = ↑a
      rw [hz]
    refine ⟨Additive.ofMul u, ?_⟩
    show Additive.ofMul (unitsToTUnitsHom T u) = x
    exact congrArg Additive.ofMul hmain
  · -- Conversely the valuation of a global unit at every finite place is `1`.
    rintro ⟨u, rfl⟩
    have key : ∀ v : (𝓞 L)ˣ, tUnitsVal T (Additive.ofMul (unitsToTUnitsHom T v)) = 0 := by
      intro v
      funext q
      show expUnit q.1 ((unitsToTUnitsHom T v : TUnits T) : Lˣ) = 0
      rw [expUnit_eq_zero_iff, unitsToTUnitsHom_apply]
      rw [show ((Units.map (algebraMap (𝓞 L) L).toMonoidHom v : Lˣ) : L)
            = algebraMap (𝓞 L) L (v : 𝓞 L) from rfl]
      rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
      intro hmem
      exact q.1.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem q.1.asIdeal hmem (Units.isUnit v))
    rw [unitsToTUnits_apply]
    exact key (Additive.toMul u)

end NK.GlobalCFTdeep.Herbrand
