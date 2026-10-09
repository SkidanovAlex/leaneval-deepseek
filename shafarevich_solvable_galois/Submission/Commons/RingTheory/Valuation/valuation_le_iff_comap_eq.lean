import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

theorem valuation_le_iff_comap_eq {F L : Type*} [Field F] [Field L] [Algebra F L] (C : ValuationSubring F) (W : ValuationSubring L) (hW : W.comap (algebraMap F L) = C) {x c : F} (hc : c ≠ 0) : (W.valuation (algebraMap F L x) ≤ W.valuation (algebraMap F L c) ↔ C.valuation x ≤ C.valuation c) := by
  -- Compare through the divisibility relations `algebraMap x / algebraMap c ∈ W` and `x / c ∈ C`.
  rw [ValuationSubring.valuation_le_iff W (algebraMap F L x) (algebraMap F L c),
      ValuationSubring.valuation_le_iff C x c]
  have hcL : algebraMap F L c ≠ 0 :=
    fun h => hc (FaithfulSMul.algebraMap_injective F L (by rw [h, map_zero]))
  constructor
  · rintro ⟨a, ha⟩
    -- `x / c ∈ C` because `algebraMap (x / c) = a ∈ W`.
    have hmem : x / c ∈ C := by
      have hxa : algebraMap F L (x / c) = (a : L) := by
        rw [map_div₀]
        exact (div_eq_iff hcL).mpr ha.symm
      rw [← hW, ValuationSubring.mem_comap, hxa]
      exact a.2
    exact ⟨⟨x / c, hmem⟩, div_mul_cancel₀ x hc⟩
  · rintro ⟨b, hb⟩
    have hbW : (b : F) ∈ W.comap (algebraMap F L) := by rw [hW]; exact b.2
    exact ⟨⟨algebraMap F L (b : F), (ValuationSubring.mem_comap).mp hbW⟩,
      by rw [← map_mul, hb]⟩

end Commons.RingTheory.Valuation