import Mathlib.NumberTheory.LocalField.Basic
import Submission.NK.LocalReciprocityLubinTate.LubinTate.exists_ltSymbol_ker_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

open scoped ValuativeRel

/-! ### Preimage of the higher principal units under the unit part map

The "unit part" map `unitPartHom π hπ : Fˣ →* 𝒪[F]ˣ` of `exists_ltSymbol_ker_eq` is a splitting of
`𝒪[F]ˣ ↪ Fˣ` with kernel `⟨π⟩`.  This file computes the preimage of the higher principal unit
group `U^n = 1 + 𝔪^n ≤ 𝒪[F]ˣ`:

`(principalUnits F n).comap (unitPartHom π hπ) = ⟨π⟩ ⊔ higherUnits F n`,

i.e. a unit of `F` has unit part in `U^n` exactly when it lies in `⟨π⟩ · U^n`.

* `⊆`: `x = unitsIncl (unitPartHom x) · ((unitsIncl (unitPartHom x))⁻¹ * x)`; the first factor is
  in `higherUnits F n` because the unit part is, the second lies in `⟨π⟩` by
  `unitPartHom_spec`.
* `⊇`: `unitPartHom` kills `⟨π⟩` (`unitPartHom_ker`) and is the identity on
  `𝒪[F]ˣ ↪ Fˣ` (`unitPartHom_unitsIncl`), so it sends `⟨π⟩ · U^n` to `U^n`. -/

theorem comap_unitPartHom_principalUnits {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (πu : Fˣ) (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F)) (n : ℕ) :
    (NK.LocalReciprocityLubinTate.principalUnits F n).comap
        (NK.LocalReciprocityLubinTate.LubinTate.unitPartHom (F := F) πu hπ)
      = Subgroup.zpowers πu ⊔ NK.LocalReciprocityLubinTate.higherUnits F n := by
  classical
  ext x
  rw [Subgroup.mem_comap]
  constructor
  · intro hu
    rw [Subgroup.mem_sup]
    refine ⟨(NK.LocalReciprocityLubinTate.Units.unitsIncl F
        (unitPartHom (F := F) πu hπ x))⁻¹ * x,
      unitPartHom_spec (F := F) πu hπ x,
      NK.LocalReciprocityLubinTate.Units.unitsIncl F (unitPartHom (F := F) πu hπ x),
      Subgroup.mem_map_of_mem (NK.LocalReciprocityLubinTate.Units.unitsIncl F) hu, ?_⟩
    rw [mul_assoc, mul_comm x _, ← mul_assoc, inv_mul_cancel, one_mul]
  · intro hx
    rw [Subgroup.mem_sup] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    have hb' : b ∈ (NK.LocalReciprocityLubinTate.principalUnits F n).map
        (NK.LocalReciprocityLubinTate.Units.unitsIncl F) := hb
    rw [Subgroup.mem_map] at hb'
    obtain ⟨u, hu, rfl⟩ := hb'
    have ha1 : unitPartHom (F := F) πu hπ a = 1 := by
      rw [← MonoidHom.mem_ker, unitPartHom_ker (F := F) πu hπ]
      exact ha
    have hux : unitPartHom (F := F) πu hπ x = u := by
      rw [← hab, map_mul, ha1, unitPartHom_unitsIncl (F := F) πu hπ u, one_mul]
    rw [hux]
    exact hu

end NK.LocalReciprocityLubinTate.LubinTate
