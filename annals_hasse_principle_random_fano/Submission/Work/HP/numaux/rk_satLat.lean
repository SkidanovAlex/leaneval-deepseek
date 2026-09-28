import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.numaux.rk_orthLatDefs

/-!
# The rank of the saturation of an integral lattice

For an integral lattice `Λ ⊆ ℤ^ι` (with `ι` finite), the saturation
`satLat Λ = {x : ∃ m ≠ 0, m • x ∈ Λ}` has the same rank as `Λ`:

`rk (satLat Λ) = rk Λ`.

The proof spreads both lattices out over `ℚ`: writing `spread L` for the `ℚ`-span of the
rational points of `L`, one has `rk L = finrank ℚ (spread L)`, and saturating a lattice does
not change its rational spread, because `m • x ∈ Λ` implies
`castL x = m⁻¹ • castL (m • x) ∈ spread Λ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP.numaux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The rational spread of a lattice -/

/-- The rational spread is monotone. -/
lemma spread_mono {L M : Submodule ℤ (ι → ℤ)} (h : L ≤ M) : spread L ≤ spread M := by
  rw [spread, spread]
  apply Submodule.span_mono
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, h hy, rfl⟩

/-- The image in `ℚ^ι` of a vector of `Λ` lies in the rational spread of `Λ`. -/
lemma castL_mem_spread {Λ : Submodule ℤ (ι → ℤ)} {x : ι → ℤ} (hx : x ∈ Λ) :
    castL x ∈ spread Λ := by
  rw [spread]
  exact Submodule.subset_span (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

/-- The image of `L` under the coordinatewise inclusion is the range of the composite with
`L.subtype`. -/
lemma map_castL_eq_range (L : Submodule ℤ (ι → ℤ)) :
    L.map (castL (ι := ι)) = LinearMap.range (castL (ι := ι) ∘ₗ L.subtype) := by
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩

/-- The coordinatewise inclusion `ℤ^ι → ℚ^ι` preserves the rank of a lattice. -/
lemma finrank_map_castL (L : Submodule ℤ (ι → ℤ)) :
    Module.finrank ℤ (L.map (castL (ι := ι))) = Module.finrank ℤ L := by
  rw [map_castL_eq_range]
  exact LinearMap.finrank_range_of_inj (castL_injective.comp Subtype.coe_injective)

/-- Spreading out is rank preserving: the rank of an integral lattice equals the `ℚ`-dimension of
its rational spread. -/
lemma finrank_eq_finrank_spread (L : Submodule ℤ (ι → ℤ)) :
    Module.finrank ℤ L = Module.finrank ℚ (spread L) := by
  rw [spread]
  rw [Submodule.finrank_span_eq_finrank (R := ℤ) (A := ℚ) (M := ι → ℚ)
        (L.map (castL (ι := ι))), finrank_map_castL]

/-! ## Saturating does not change the spread -/

/-- The saturation of a lattice has the same rational spread as the lattice. -/
lemma spread_satLat_eq (Λ : Submodule ℤ (ι → ℤ)) : spread (satLat Λ) = spread Λ := by
  refine le_antisymm ?_ (spread_mono (le_satLat Λ))
  rw [spread_eq_span_image, Submodule.span_le]
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨m, hm, hmy⟩ := mem_satLat.mp hy
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have h2 : castL y = ((m : ℚ))⁻¹ • castL (m • y) := by
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℚ m (castL y), smul_smul,
      inv_mul_cancel₀ hmq, one_smul]
  rw [h2]
  exact Submodule.smul_mem _ _ (castL_mem_spread hmy)

/-! ## The main result -/

theorem rk_satLat {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Submodule ℤ (ι → ℤ)) :
    rk (satLat Λ) = rk Λ := by
  show Module.finrank ℤ (satLat Λ) = Module.finrank ℤ Λ
  rw [finrank_eq_finrank_spread (satLat Λ), finrank_eq_finrank_spread Λ, spread_satLat_eq]

end Work.HP.numaux
