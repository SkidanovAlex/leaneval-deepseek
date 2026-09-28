import Mathlib
import Submission.Work.Q44Geom.BadDefs
import Submission.Work.Q44Geom.invSub_finrank_le
import Submission.Work.Q44Geom.sat_span

/-!
# `Work.Q44Geom.badA_subset`

If a bad lattice `L ∈ badSet c s` has `rk (L ⊓ latW (f44 c)) = 3`, then `L` is the invariance
lattice `W = latW (f44 c)` itself.

Indeed `L` is a saturated rank-`3` sublattice of `ℤ^5`, and `W` is saturated with `rk W ≤ 3`.
The sublattice `N := L ⊓ W` has rank `3`, so its rational span

* is contained in `ratSpan L` and `ratSpan W`,
* has `ℚ`-dimension `3 = rk L ≥ rk W`,

forcing `ratSpan L = ratSpan N = ratSpan W`.  Since a saturated lattice is exactly the set of
integral points of its rational span (`sat_span`), this gives `L = W`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Q44Geom

open MvPolynomial

theorem badA_subset (c : Work.HP.Mon 4 4 → ℤ) (hf0 : Work.HP.formOf 4 4 c ≠ 0)
    (hirr : Irreducible (Work.HP.formOf 4 4 c)) (s : Fin 3 → ℝ) :
    Work.Q44Geom.badASet c s ⊆ {Work.Q44Geom.Wlat c} := by
  intro L hL
  rw [Set.mem_singleton_iff]
  obtain ⟨hLbad, hrkN⟩ := hL
  obtain ⟨hLprim, hLrk, hs, hv⟩ := hLbad.1
  have hWprim : Work.HP.IsPrimLat (Wlat c) := isPrimLat_Wlat c
  have hWrk : Work.HP.rk (Wlat c) ≤ 3 :=
    le_trans (latW_rank_le (f44 c)) (invSub_finrank_le c hf0 hirr)
  have hNleL : ratSpan (L ⊓ Wlat c) ≤ ratSpan L := ratSpan_mono inf_le_left
  have hNleW : ratSpan (L ⊓ Wlat c) ≤ ratSpan (Wlat c) := ratSpan_mono inf_le_right
  have hfinN : Module.finrank ℚ (ratSpan (L ⊓ Wlat c)) = 3 := by
    rw [ratSpan_finrank_general, hrkN]
  have hfinL : Module.finrank ℚ (ratSpan L) = 3 := by
    rw [ratSpan_finrank_general, hLrk]
  have hfinW : Module.finrank ℚ (ratSpan (Wlat c)) = Work.HP.rk (Wlat c) :=
    ratSpan_finrank_general _
  have hspL : ratSpan (L ⊓ Wlat c) = ratSpan L :=
    Submodule.eq_of_le_of_finrank_eq hNleL (by rw [hfinN, hfinL])
  have hle3 : 3 ≤ Module.finrank ℚ (ratSpan (Wlat c)) := by
    have h1 := Submodule.finrank_mono hNleW
    rwa [hfinN] at h1
  have hfinW3 : Module.finrank ℚ (ratSpan (Wlat c)) = 3 := by omega
  have hspW : ratSpan (L ⊓ Wlat c) = ratSpan (Wlat c) :=
    Submodule.eq_of_le_of_finrank_eq hNleW (by rw [hfinN, hfinW3])
  apply Submodule.ext
  intro v
  rw [sat_span L hLprim v, sat_span (Wlat c) hWprim v, ← hspL, ← hspW]

end Work.Q44Geom
