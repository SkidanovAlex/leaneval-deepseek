import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SpecLin.Alt

/-- The property "`x` is a fraction `a/b` with `b` outside `P`", tested over `R`, is equivalent
to the same property tested over a localization `S = M⁻¹R` of `R`, provided `M` is disjoint
from the prime `P` (so that `P·S` contracts back to `P`). -/
theorem exists_mul_eq_iff_of_isLocalization {R S K : Type*} [CommRing R] [CommRing S] [CommRing K]
    (M : Submonoid R) [Algebra R S] [IsLocalization M S] [Algebra R K] [Algebra S K]
    [IsScalarTower R S K] (P : Ideal R) [P.IsPrime] (hdisj : Disjoint (M : Set R) (P : Set R))
    (x : K) :
    (∃ a b : R, b ∉ P ∧ x * algebraMap R K b = algebraMap R K a) ↔
      (∃ a b : S, b ∉ Ideal.map (algebraMap R S) P ∧ x * algebraMap S K b = algebraMap S K a) := by
  have hunder : Ideal.under R (Ideal.map (algebraMap R S) P) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M S (inferInstance : P.IsPrime) hdisj
  constructor
  · rintro ⟨a, b, hbP, hx⟩
    refine ⟨algebraMap R S a, algebraMap R S b, ?_, ?_⟩
    · intro hmem
      have : b ∈ Ideal.under R (Ideal.map (algebraMap R S) P) := (Ideal.mem_under R _).mpr hmem
      rw [hunder] at this
      exact hbP this
    · rw [← IsScalarTower.algebraMap_apply R S K b, ← IsScalarTower.algebraMap_apply R S K a]
      exact hx
  · rintro ⟨a, b, hb, hx⟩
    obtain ⟨xa, hxa⟩ := IsLocalization.surj M a
    obtain ⟨xb, hxb⟩ := IsLocalization.surj M b
    refine ⟨xa.1 * (xb.2 : R), xb.1 * (xa.2 : R), ?_, ?_⟩
    · -- `xb.1 * xa.2 ∉ P`: the numerator of `b` is not in `P` (else `b ∈ P·S`),
      -- and `xa.2 ∈ M` is not in `P`.
      have hrbS : algebraMap R S xb.1 ∉ Ideal.map (algebraMap R S) P := by
        intro hmem
        have hbPS : b ∈ Ideal.map (algebraMap R S) P := by
          apply (Ideal.mul_unit_mem_iff_mem (Ideal.map (algebraMap R S) P)
            (IsLocalization.map_units S xb.2)).mp
          rw [hxb]
          exact hmem
        exact hb hbPS
      have hrb : xb.1 ∉ P := by
        intro hmemP
        apply hrbS
        exact (Ideal.mem_under R (Ideal.map (algebraMap R S) P)).mp (by rw [hunder]; exact hmemP)
      have hma : (xa.2 : R) ∉ P := fun h => Set.disjoint_left.mp hdisj xa.2.2 h
      intro hprod
      rcases (inferInstance : P.IsPrime).mem_or_mem hprod with h1 | h2
      · exact hrb h1
      · exact hma h2
    · -- `x * (xb.1 * xa.2) = xa.1 * xb.2` in `K`, obtained by clearing denominators.
      have haK : algebraMap S K a * algebraMap R K ↑xa.2 = algebraMap R K xa.1 := by
        have h := congrArg (algebraMap S K) hxa
        simpa [map_mul, ← IsScalarTower.algebraMap_apply R S K] using h
      have hbK : algebraMap S K b * algebraMap R K ↑xb.2 = algebraMap R K xb.1 := by
        have h := congrArg (algebraMap S K) hxb
        simpa [map_mul, ← IsScalarTower.algebraMap_apply R S K] using h
      rw [map_mul, map_mul]
      calc x * (algebraMap R K xb.1 * algebraMap R K ↑xa.2)
          = x * ((algebraMap S K b * algebraMap R K ↑xb.2) * algebraMap R K ↑xa.2) := by
            rw [← hbK]
        _ = (x * algebraMap S K b) * (algebraMap R K ↑xb.2 * algebraMap R K ↑xa.2) := by ring
        _ = algebraMap S K a * (algebraMap R K ↑xb.2 * algebraMap R K ↑xa.2) := by rw [hx]
        _ = (algebraMap S K a * algebraMap R K ↑xa.2) * algebraMap R K ↑xb.2 := by ring
        _ = algebraMap R K xa.1 * algebraMap R K ↑xb.2 := by rw [← haK]

end Work.SpecLin.Alt
