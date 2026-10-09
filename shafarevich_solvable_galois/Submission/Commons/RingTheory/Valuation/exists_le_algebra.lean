import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

open IsLocalRing

/-! # Extension of a valuation subring to a field extension

This is the *existence* form of `Valuation.HasExtension`: every valuation subring of a field `K`
is the restriction of a valuation subring of any field extension `L/K`.

We use the key tool `LocalSubring.exists_le_valuationSubring`: every local subring `A` of a field
is dominated by a valuation subring (`∃ B : ValuationSubring K, A ≤ B.toLocalSubring`), where `≤`
on `LocalSubring` is the *domination* order (`A ≤ B ↔ A.toSubring ≤ B.toSubring` **and**
`IsLocalHom (Subring.inclusion ·)`, i.e. non-units of `A` stay non-units in `B`).

Let `V : ValuationSubring K` and put `V' : LocalSubring L := V.toLocalSubring.map (algebraMap K L)`
(the image of `V` in `L`). Applying `LocalSubring.exists_le_valuationSubring V'` yields
`W : ValuationSubring L` with `V' ≤ W.toLocalSubring`. Then `W ∩ K = V`:
* `V ⊆ W` is clear;
* conversely, if `x ∈ K` has `algebraMap x ∈ W` but `x ∉ V`, then `x ≠ 0` and `x⁻¹ ∈ V`
  (valuation subring!), and `x⁻¹` is *not* a unit of `V`. Its image `y` in `V'` is therefore also
  not a unit of `V'`, so — by the domination `V' ≤ W` — `Subring.inclusion · y` is not a unit of
  `W`. But `algebraMap x ∈ W` and `algebraMap x⁻¹` is its inverse in `W`, so `y` *is* a unit
  of `W` — contradiction.
-/

theorem exists_le_algebra {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) :
    ∃ W : ValuationSubring L, ∀ x : K, x ∈ V ↔ algebraMap K L x ∈ W := by
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  let V' : LocalSubring L := V.toLocalSubring.map (algebraMap K L)
  obtain ⟨W, hW⟩ := V'.exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := hW
  have hmem : ∀ v ∈ V, algebraMap K L v ∈ V'.toSubring :=
    fun v hv => Subring.mem_map.mpr ⟨v, hv, rfl⟩
  refine ⟨W, fun x => ⟨fun hx => hle (hmem x hx), fun hx => ?_⟩⟩
  -- suppose `algebraMap x ∈ W` but `x ∉ V`
  by_contra hxV
  have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
  have hxinv : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
  let y : V'.toSubring := ⟨algebraMap K L x⁻¹, hmem x⁻¹ hxinv⟩
  -- `algebraMap x` is the inverse of `y` inside `W`
  have hy : IsUnit (Subring.inclusion hle y) := by
    refine ⟨⟨_, ⟨algebraMap K L x, hx⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      change (algebraMap K L x⁻¹) * (algebraMap K L x) = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    · apply Subtype.ext
      change (algebraMap K L x) * (algebraMap K L x⁻¹) = 1
      rw [← map_mul, mul_inv_cancel₀ hx0, map_one]
  -- by domination, `y` itself is a unit in `V'`
  have hy' : IsUnit y := hloc.map_nonunit y hy
  obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hy'
  -- hence the inverse `z` in `V'` is `algebraMap x`, so `algebraMap x ∈ V'` and `x ∈ V`
  have hz1 : (z : L) = algebraMap K L x := by
    have hh : algebraMap K L x⁻¹ * (z : L) = 1 := by
      have := congrArg (Subtype.val : V'.toSubring → L) hz
      simpa [y] using this
    have := congrArg (fun t : L => algebraMap K L x * t) hh
    rw [mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0, map_one, one_mul] at this
    exact this
  have hxA : algebraMap K L x ∈ V'.toSubring := hz1 ▸ z.2
  obtain ⟨v, hv, hveq⟩ := Subring.mem_map.mp hxA
  exact hxV (hinj hveq ▸ hv)

end Commons.RingTheory.Valuation