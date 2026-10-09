import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- If `O` is the pullback of the valuation subring `W` of `L` along the structure map
`K → L`, then the two valuations cut out the same "strictly smaller than `1`" set. -/
theorem valuation_lt_one_algebraMap_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (W : ValuationSubring L) (O : ValuationSubring K)
    (h : W.comap (algebraMap K L) = O) (x : K) :
    W.valuation (algebraMap K L x) < 1 ↔ O.valuation x < 1 := by
  -- On elements the two valuation subrings have the same "integral" members.
  have hle : ∀ y : K, W.valuation (algebraMap K L y) ≤ 1 ↔ O.valuation y ≤ 1 := fun y => by
    have hm : algebraMap K L y ∈ W ↔ y ∈ O := by
      rw [← ValuationSubring.mem_comap, h]
    rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff]
    exact hm
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hfx : algebraMap K L x ≠ 0 :=
      fun hc => hx ((algebraMap K L).injective (by simpa using hc))
    -- Comparing `1 ≤ ·` is the same as comparing `·⁻¹ ≤ 1`, which is the `hle` statement at `x⁻¹`.
    have hge : 1 ≤ W.valuation (algebraMap K L x) ↔ 1 ≤ O.valuation x := by
      have h1 := hle x⁻¹
      rw [map_inv₀] at h1
      rw [Valuation.one_le_val_iff W.valuation hfx, Valuation.one_le_val_iff O.valuation hx]
      exact h1
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hle x, hge]

end Work.SSGRoute
