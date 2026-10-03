import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.BlockDefs

namespace Work.HornSC.CellBoundaryJordan

open Set

lemma block_of_corner {A : Finset (ℤ × ℤ)} {z : ℂ} {p : ℤ × ℤ}
    (hp : p ∈ A) (hzp : z ∈ cell p)
    (hx : z.re = (⌊z.re⌋ : ℝ)) (hy : z.im = (⌊z.im⌋ : ℝ))
    (hw : z ∉ wallSet A) :
    RectBlock A (⌊z.re⌋ - 1) (⌊z.re⌋ + 1) (⌊z.im⌋ - 1) (⌊z.im⌋ + 1) := by
  set m : ℤ := ⌊z.re⌋ with hm
  set n : ℤ := ⌊z.im⌋ with hn
  have hHN : ¬ hWallAt A (m, n) :=
    not_hWallAt_of_mem_hSeg hw (by simpa only [← hm, ← hn] using mem_hSeg_floor (z := z) hy)
  have hHW : ¬ hWallAt A (m - 1, n) :=
    not_hWallAt_of_mem_hSeg hw (by simpa only [← hm, ← hn] using mem_hSeg_floor_left (z := z) hy hx)
  have hVN : ¬ vWallAt A (m, n) :=
    not_vWallAt_of_mem_vSeg hw (by simpa only [← hm, ← hn] using mem_vSeg_floor (z := z) hx)
  have eNE_SE : (m, n) ∈ A ↔ (m, n - 1) ∈ A :=
    ⟨mem_south_of_not_hWallAt hHN, mem_north_of_not_hWallAt hHN⟩
  have eNW_SW : (m - 1, n) ∈ A ↔ (m - 1, n - 1) ∈ A :=
    ⟨mem_south_of_not_hWallAt hHW, mem_north_of_not_hWallAt hHW⟩
  have eNE_NW : (m, n) ∈ A ↔ (m - 1, n) ∈ A :=
    ⟨mem_west_of_not_vWallAt hVN, mem_east_of_not_vWallAt hVN⟩
  have hNE : (m, n) ∈ A := by
    have h1 : p.1 = m ∨ p.1 = m - 1 := by
      have hc := mem_cell_fst_cases hzp
      rw [← hm] at hc
      exact hc
    have h2 : p.2 = n ∨ p.2 = n - 1 := by
      have hc := mem_cell_snd_cases hzp
      rw [← hn] at hc
      exact hc
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · have hpe : p = (m, n) := by ext <;> simp [h1, h2]
      rwa [hpe] at hp
    · have hpe : p = (m, n - 1) := by ext <;> simp [h1, h2]
      rw [hpe] at hp
      exact eNE_SE.mpr hp
    · have hpe : p = (m - 1, n) := by ext <;> simp [h1, h2]
      rw [hpe] at hp
      exact eNE_NW.mpr hp
    · have hpe : p = (m - 1, n - 1) := by ext <;> simp [h1, h2]
      rw [hpe] at hp
      exact eNE_NW.mpr (eNW_SW.mpr hp)
  intro p' q' h1 h2 h3 h4
  have hp' : p' = m - 1 ∨ p' = m := by omega
  have hq' : q' = n - 1 ∨ q' = n := by omega
  rcases hp' with hh | hh <;> rcases hq' with hk | hk <;>
    subst hh <;> subst hk
  · exact eNW_SW.mp (eNE_NW.mp hNE)
  · exact eNE_NW.mp hNE
  · exact eNE_SE.mp hNE
  · exact hNE

end Work.HornSC.CellBoundaryJordan
