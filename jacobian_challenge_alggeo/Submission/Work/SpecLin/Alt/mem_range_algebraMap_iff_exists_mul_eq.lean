import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SpecLin.Alt

theorem mem_range_algebraMap_iff_exists_mul_eq {R S K : Type*} [CommRing R] [CommRing S] [CommRing K]
    (P : Ideal R) [P.IsPrime] [Algebra R S] [IsLocalization P.primeCompl S] [Algebra R K]
    [Algebra S K] [IsScalarTower R S K] (x : K) :
    x ∈ (algebraMap S K).range ↔ ∃ a b : R, b ∉ P ∧ x * algebraMap R K b = algebraMap R K a := by
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨⟨a, b⟩, hb⟩ := IsLocalization.surj P.primeCompl s
    refine ⟨a, ↑b, Ideal.mem_primeCompl_iff.mp b.2, ?_⟩
    rw [IsScalarTower.algebraMap_apply R S K (b : R), ← map_mul, hb,
        IsScalarTower.algebraMap_apply R S K a]
  · rintro ⟨a, b, hb, h⟩
    have hbmem : b ∈ P.primeCompl := Ideal.mem_primeCompl_iff.mpr hb
    refine ⟨IsLocalization.mk' S a ⟨b, hbmem⟩, ?_⟩
    have hunit : IsUnit (algebraMap R K b) := by
      rw [IsScalarTower.algebraMap_apply R S K b]
      exact (IsLocalization.map_units S ⟨b, hbmem⟩).map (algebraMap S K)
    have hmk : algebraMap S K (IsLocalization.mk' S a ⟨b, hbmem⟩) * algebraMap R K b =
        algebraMap R K a := by
      rw [IsScalarTower.algebraMap_apply R S K b, ← map_mul,
          IsLocalization.mk'_spec S a ⟨b, hbmem⟩, IsScalarTower.algebraMap_apply R S K a]
    exact hunit.mul_right_cancel (hmk.trans h.symm)

end Work.SpecLin.Alt
