import Mathlib

/-!
# The band region over an open set is open

Let `C ⊆ (Fin p → ℝ)` be open and let `a b : (Fin p → ℝ) → EReal` be continuous on `C`.
Then the "band" region

  `{(v, w) | v ∈ C, a v < w < b v}`   (with `w : ℝ` coerced into `EReal`)

is open in the product `(Fin p → ℝ) × ℝ`.

The point of the proof is that near a point of the band both bounds are bounded away
from `w` by actual real numbers: continuity of `a` (resp. `b`) at `v₀` with `a v₀ < w₀`
(resp. `w₀ < b v₀`) gives a neighbourhood on which `a < c` (resp. `d < b`) for a real
`c < w₀` (resp. `w₀ < d`), using `EReal.exists_between_coe_real`.  The band then
contains the open box `U ×ˢ Ioo c d` around each of its points.
-/

open Set Filter

namespace Work.WilCrux.GR

theorem BandRegion (p : ℕ) {C : Set (Fin p → ℝ)} (hC : IsOpen C)
    {a b : (Fin p → ℝ) → EReal} (ha : ContinuousOn a C) (hb : ContinuousOn b C) :
    IsOpen {vw : (Fin p → ℝ) × ℝ | vw.1 ∈ C ∧ a vw.1 < ((vw.2 : ℝ) : EReal) ∧
      ((vw.2 : ℝ) : EReal) < b vw.1} := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨v, w⟩ ⟨hvC, haw, hwb⟩
  -- the two bounds around `w`
  obtain ⟨c, hac, hcw⟩ := EReal.exists_between_coe_real haw
  obtain ⟨d, hwd, hdb⟩ := EReal.exists_between_coe_real hwb
  have hcw' : c < w := EReal.coe_lt_coe_iff.mp hcw
  have hwd' : w < d := EReal.coe_lt_coe_iff.mp hwd
  -- the open neighbourhood of `v` on which `a < c` and `d < b`
  set U : Set (Fin p → ℝ) := (C ∩ a ⁻¹' Iio (c : EReal)) ∩ b ⁻¹' Ioi (d : EReal)
  have hU : IsOpen U := by
    have h1 : IsOpen (C ∩ a ⁻¹' Iio (c : EReal)) :=
      ha.isOpen_inter_preimage hC isOpen_Iio
    exact (hb.mono inter_subset_left).isOpen_inter_preimage h1 isOpen_Ioi
  have hbox : IsOpen (U ×ˢ Ioo c d) := hU.prod isOpen_Ioo
  refine Filter.mem_of_superset (hbox.mem_nhds ?_) ?_
  · simp only [U, mem_prod, mem_Ioo, mem_inter_iff, mem_preimage, mem_Iio, mem_Ioi]
    exact ⟨⟨⟨hvC, hac⟩, hdb⟩, hcw', hwd'⟩
  · rintro ⟨v', w'⟩ ⟨⟨⟨hv'C, hav'⟩, hdb'⟩, hcw'', hwd''⟩
    exact ⟨hv'C, lt_trans hav' (EReal.coe_lt_coe hcw''),
      lt_trans (EReal.coe_lt_coe hwd'') hdb'⟩

end Work.WilCrux.GR
