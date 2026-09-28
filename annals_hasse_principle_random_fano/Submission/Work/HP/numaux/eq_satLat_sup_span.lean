import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.numaux.rk_orthLatDefs
import Submission.Work.HP.numaux.castL_mem_spread_iff
import Submission.Work.HP.numaux.rk_satLat

/-!
# Saturating `Λ ⊔ ℤu` for `u ∈ L ∖ satLat Λ`

Let `Λ ≤ L` be integral lattices in `ℤ^ι` (`ι` finite) with `L` primitive and
`rk L = rk Λ + 1`.  If `u ∈ L` is not in the saturation of `Λ`, then adjoining `u` to `Λ`
and saturating recovers `L`:

`satLat (Λ ⊔ span_ℤ {u}) = L`.

The proof passes to the rational spreads `spread M ⊆ ℚ^ι` of `rk_orthLatDefs`:

* `spread (Λ ⊔ span_ℤ {u}) = spread Λ ⊔ span_ℚ {castL u}`;
* `spread Λ ⊓ span_ℚ {castL u} = ⊥`, because `castL u ∉ spread Λ` (this is exactly
  `u ∉ satLat Λ`, by `castL_mem_spread_iff`), so the sup has `ℚ`-dimension
  `finrank (spread Λ) + 1 = rk Λ + 1 = rk L = finrank (spread L)`;
* since `spread (Λ ⊔ span_ℤ {u}) ≤ spread L` with equal finite dimension, the two spreads
  coincide;
* finally `satLat N` is exactly the set of integer points of `spread N`
  (`castL_mem_spread_iff`), and `satLat L = L` because `L` is primitive.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.HP.numaux

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The rational spread commutes with the sum of lattices. -/
lemma spread_sup_eq {Λ M : Submodule ℤ (ι → ℤ)} :
    spread (Λ ⊔ M) = spread Λ ⊔ spread M := by
  refine le_antisymm ?_ (sup_le (spread_mono le_sup_left) (spread_mono le_sup_right))
  rw [spread_eq_span_image, spread_eq_span_image, spread_eq_span_image]
  rw [Submodule.span_le]
  rintro z ⟨y, hy, rfl⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (show y ∈ Λ ⊔ M from hy)
  rw [← hab, map_add]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨a, ha, rfl⟩)
    (Submodule.subset_span ⟨b, hb, rfl⟩)

/-- The rational spread of the span of a single vector is the rational line it generates. -/
lemma spread_span_singleton_eq (u : ι → ℤ) :
    spread (Submodule.span ℤ ({u} : Set (ι → ℤ)))
      = Submodule.span ℚ ({castL u} : Set (ι → ℚ)) := by
  have hsub : (↑(Submodule.span ℤ ({castL u} : Set (ι → ℚ))) : Set (ι → ℚ))
      ⊆ ↑(Submodule.span ℚ ({castL u} : Set (ι → ℚ))) := by
    intro x hx
    have hx' : x ∈ (Submodule.span ℚ ({castL u} : Set (ι → ℚ))).restrictScalars ℤ :=
      Submodule.span_le.mpr (fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact Submodule.subset_span rfl) hx
    exact hx'
  rw [spread, Submodule.map_span, Set.image_singleton]
  refine le_antisymm (Submodule.span_le.mpr hsub) ?_
  · refine Submodule.span_mono ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Submodule.subset_span rfl

/-- Saturating `Λ ⊔ ℤu` for `u ∈ L ∖ satLat Λ` recovers `L`. -/
theorem eq_satLat_sup_span {ι : Type} [Fintype ι] [DecidableEq ι] {Λ L : Submodule ℤ (ι → ℤ)}
    (hΛ : IsPrimLat Λ) (hL : IsPrimLat L) (hle : Λ ≤ L) (hrk : rk L = rk Λ + 1)
    {u : ι → ℤ} (hu : u ∈ L) (hu' : u ∉ satLat Λ) :
    satLat (Λ ⊔ Submodule.span ℤ ({u} : Set (ι → ℤ))) = L := by
  have hu_ne : u ≠ 0 := fun h => hu' (by rw [h]; exact Submodule.zero_mem _)
  have hu0 : castL u ≠ 0 := fun h => hu_ne (castL_injective (by rw [h, map_zero]))
  -- The line `ℚ·u` meets the spread of `Λ` trivially.
  have hinf : spread Λ ⊓ Submodule.span ℚ ({castL u} : Set (ι → ℚ)) = ⊥ := by
    refine le_antisymm (fun y hy => ?_) bot_le
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (show y ∈ Submodule.span ℚ ({castL u} : Set (ι → ℚ)) from hy2)
    by_cases ha0 : a = 0
    · rw [ha0, zero_smul] at ha
      exact (Submodule.mem_bot ℚ).mpr ha.symm
    · exfalso
      have hmem : a • castL u ∈ spread Λ := ha ▸ hy1
      have hcu : castL u ∈ spread Λ := by
        have h := (spread Λ).smul_mem (a⁻¹) hmem
        rwa [smul_smul, inv_mul_cancel₀ ha0, one_smul] at h
      exact hu' ((castL_mem_spread_iff Λ u).mp hcu)
  -- Dimension count: the sup has dimension `rk Λ + 1 = rk L = dim (spread L)`.
  have hcard := Submodule.finrank_sup_add_finrank_inf_eq (spread Λ)
    (Submodule.span ℚ ({castL u} : Set (ι → ℚ)))
  rw [hinf, finrank_bot ℚ, finrank_span_singleton hu0] at hcard
  have hdim1 : Module.finrank ℚ ↥(spread Λ ⊔ Submodule.span ℚ ({castL u} : Set (ι → ℚ)))
      = Module.finrank ℚ ↥(spread Λ) + 1 := by omega
  have hd : Module.finrank ℚ ↥(spread Λ ⊔ Submodule.span ℚ ({castL u} : Set (ι → ℚ)))
      = Module.finrank ℚ ↥(spread L) := by
    rw [hdim1, ← finrank_eq_finrank_spread Λ, ← finrank_eq_finrank_spread L]
    exact hrk.symm
  have hle1 : spread Λ ⊔ Submodule.span ℚ ({castL u} : Set (ι → ℚ)) ≤ spread L :=
    sup_le (spread_mono hle) (Submodule.span_le.mpr (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact castL_mem_spread hu))
  have hspread1 : spread Λ ⊔ Submodule.span ℚ ({castL u} : Set (ι → ℚ)) = spread L :=
    Submodule.eq_of_le_of_finrank_eq hle1 hd
  have hspread : spread (Λ ⊔ Submodule.span ℤ ({u} : Set (ι → ℤ))) = spread L := by
    rw [spread_sup_eq, spread_span_singleton_eq]
    exact hspread1
  refine le_antisymm ?_ ?_
  · have hML : Λ ⊔ Submodule.span ℤ ({u} : Set (ι → ℤ)) ≤ L :=
      sup_le hle (Submodule.span_le.mpr (fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hu))
    calc satLat (Λ ⊔ Submodule.span ℤ ({u} : Set (ι → ℤ)))
        ≤ satLat L := satLat_mono hML
      _ = L := satLat_eq_of_isPrimLat hL
  · intro x hx
    have hx' : castL x ∈ spread (Λ ⊔ Submodule.span ℤ ({u} : Set (ι → ℤ))) := by
      rw [hspread]
      exact castL_mem_spread hx
    exact (castL_mem_spread_iff (Λ ⊔ Submodule.span ℤ ({u} : Set (ι → ℤ))) x).mp hx'

end Work.HP.numaux
