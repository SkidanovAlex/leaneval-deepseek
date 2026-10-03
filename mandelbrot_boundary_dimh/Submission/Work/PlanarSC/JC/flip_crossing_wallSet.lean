import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.CellBoundaryJordan.RayDefs
import Submission.Work.HornSC.Cells

/-!
# Crossing a wall of a union of lattice cells flips membership

If `p` lies on a wall of the finite cell family `A` (`p ∈ wallSet A`) and `p` is not a lattice
point (`NonLattice p`), then `p` lies in the relative interior of exactly one unit grid segment of
the wall.  Walking a small distance `s` in a direction `v` with positive real and imaginary parts
(`0 < v.re`, `0 < v.im`) moves `p` off the wall on the north-east side, while walking in direction
`-v` moves `p` off the wall on the south-west side.  Since the two cells adjacent to the wall
segment are exactly one in `A` and one not in `A`, exactly one of the two points lies in the cell
union.

The proof is elementary: for `s` smaller than the distance from `p` to the endpoint of its wall
segment (and to the neighbouring grid lines), `p + s v` is in the *open* cell on the north-east
side and `p - s v` in the *open* cell on the south-west side; then the characterisation
`z ∈ cellUnion A ↔ q ∈ A` for `z ∈ iCell q` converts membership in the closed union into
membership of the open cell index in `A`.
-/

namespace Work.PlanarSC.JC

open Set

namespace FlipWall

open Work.HornSC Work.HornSC.CellBoundaryJordan

/-! ## Real and imaginary parts of the moving points -/

lemma add_mul_re (p v : ℂ) (s : ℝ) : (p + (s : ℂ) * v).re = p.re + s * v.re := by simp

lemma add_mul_im (p v : ℂ) (s : ℝ) : (p + (s : ℂ) * v).im = p.im + s * v.im := by simp

lemma sub_mul_re (p v : ℂ) (s : ℝ) : (p - (s : ℂ) * v).re = p.re - s * v.re := by simp

lemma sub_mul_im (p v : ℂ) (s : ℝ) : (p - (s : ℂ) * v).im = p.im - s * v.im := by simp

/-! ## The open cell containing a point is the unique cell containing it -/

/-- Recovering a complex number from its real and imaginary parts as a lattice point. -/
lemma eq_lpt_of_re_im {w : ℂ} {m n : ℤ} (hre : w.re = (m : ℝ)) (him : w.im = (n : ℝ)) :
    w = lpt (m, n) := by
  refine Complex.ext ?_ ?_ <;> simp [lpt, hre, him]

lemma iCell_subset_cell {q : ℤ × ℤ} : iCell q ⊆ cell q := by
  rintro z ⟨h1, h2, h3, h4⟩
  exact ⟨le_of_lt h1, le_of_lt h2, le_of_lt h3, le_of_lt h4⟩

/-- A point of an open cell `iCell q` lies in the closed cell `cell q'` only for `q' = q`. -/
lemma eq_of_mem_iCell_of_mem_cell {q q' : ℤ × ℤ} {z : ℂ}
    (h : z ∈ iCell q) (h' : z ∈ cell q') : q' = q := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨k1, k2, k3, k4⟩ := h'
  have hfst : q'.1 = q.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hc : ((q'.1 : ℤ) : ℝ) + 1 ≤ ((q.1 : ℤ) : ℝ) := by
        have : q'.1 + 1 ≤ q.1 := by omega
        exact_mod_cast this
      linarith
    · have hc : ((q.1 : ℤ) : ℝ) + 1 ≤ ((q'.1 : ℤ) : ℝ) := by
        have : q.1 + 1 ≤ q'.1 := by omega
        exact_mod_cast this
      linarith
  have hsnd : q'.2 = q.2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hc : ((q'.2 : ℤ) : ℝ) + 1 ≤ ((q.2 : ℤ) : ℝ) := by
        have : q'.2 + 1 ≤ q.2 := by omega
        exact_mod_cast this
      linarith
    · have hc : ((q.2 : ℤ) : ℝ) + 1 ≤ ((q'.2 : ℤ) : ℝ) := by
        have : q.2 + 1 ≤ q'.2 := by omega
        exact_mod_cast this
      linarith
  exact Prod.ext hfst hsnd

/-- A point of the open cell `iCell q` lies in `cellUnion A` exactly when `q ∈ A`. -/
lemma mem_cellUnion_of_mem_iCell {A : Finset (ℤ × ℤ)} {q : ℤ × ℤ} {z : ℂ}
    (hz : z ∈ iCell q) : (z ∈ cellUnion A ↔ q ∈ A) := by
  constructor
  · intro h
    obtain ⟨q', hq', hzq'⟩ := Set.mem_iUnion₂.mp h
    have hqq : q' = q := eq_of_mem_iCell_of_mem_cell hz hzq'
    rwa [hqq] at hq'
  · intro hq
    exact Set.mem_iUnion₂.mpr ⟨q, hq, iCell_subset_cell hz⟩

end FlipWall

theorem flip_crossing_wallSet {A : Finset (ℤ × ℤ)} {p v : ℂ}
    (hp : p ∈ Work.HornSC.CellBoundaryJordan.wallSet A)
    (hnl : Work.HornSC.CellBoundaryJordan.NonLattice p)
    (hvr : 0 < v.re) (hvi : 0 < v.im) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      ((p + (s : ℂ) * v ∈ Work.HornSC.cellUnion A) ↔
        ¬ (p - (s : ℂ) * v ∈ Work.HornSC.cellUnion A)) := by
  rw [Work.HornSC.CellBoundaryJordan.mem_wallSet] at hp
  rcases hp with ⟨u, hu, hpu⟩ | ⟨u, hu, hpu⟩
  · -- `p` lies in the relative interior of a horizontal wall segment at `u`
    rw [Work.HornSC.CellBoundaryJordan.mem_hSeg] at hpu
    obtain ⟨him, hle, hle'⟩ := hpu
    have hre1 : (u.1 : ℝ) < p.re := by
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exact absurd (FlipWall.eq_lpt_of_re_im h.symm him) (hnl.notMem_lpt (u.1, u.2))
    have hre2 : p.re < (u.1 : ℝ) + 1 := by
      rcases lt_or_eq_of_le hle' with h | h
      · exact h
      · have h' : p.re = ((u.1 + 1 : ℤ) : ℝ) := by push_cast; exact h
        exact absurd (FlipWall.eq_lpt_of_re_im h' him) (hnl.notMem_lpt (u.1 + 1, u.2))
    set a : ℝ := min (p.re - (u.1 : ℝ)) ((u.1 : ℝ) + 1 - p.re) with ha
    have ha1 : a ≤ p.re - (u.1 : ℝ) := min_le_left _ _
    have ha2 : a ≤ (u.1 : ℝ) + 1 - p.re := min_le_right _ _
    have ha_pos : 0 < a := lt_min (by linarith) (by linarith)
    refine ⟨min (a / v.re) (1 / v.im), lt_min (div_pos ha_pos hvr) (one_div_pos.mpr hvi), ?_⟩
    intro s hs0 hs
    have hsv_re : 0 < s * v.re := mul_pos hs0 hvr
    have hsv_im : 0 < s * v.im := mul_pos hs0 hvi
    have hs_a : s * v.re < a := by
      have h : s < a / v.re := lt_of_lt_of_le hs (min_le_left _ _)
      rwa [lt_div_iff₀ hvr] at h
    have hs_1 : s * v.im < 1 := by
      have h : s < 1 / v.im := lt_of_lt_of_le hs (min_le_right _ _)
      rwa [lt_div_iff₀ hvi] at h
    have h1 : (u.1 : ℝ) < (p + (s : ℂ) * v).re := by
      rw [FlipWall.add_mul_re]; linarith
    have h2 : (p + (s : ℂ) * v).re < (u.1 : ℝ) + 1 := by
      rw [FlipWall.add_mul_re]; linarith
    have h3 : (u.2 : ℝ) < (p + (s : ℂ) * v).im := by
      rw [FlipWall.add_mul_im]; linarith
    have h4 : (p + (s : ℂ) * v).im < (u.2 : ℝ) + 1 := by
      rw [FlipWall.add_mul_im]; linarith
    have hup : p + (s : ℂ) * v ∈ Work.HornSC.CellBoundaryJordan.iCell ((u.1, u.2) : ℤ × ℤ) :=
      ⟨h1, h2, h3, h4⟩
    have k1 : (u.1 : ℝ) < (p - (s : ℂ) * v).re := by
      rw [FlipWall.sub_mul_re]; linarith
    have k2 : (p - (s : ℂ) * v).re < (u.1 : ℝ) + 1 := by
      rw [FlipWall.sub_mul_re]; linarith
    have k3 : ((u.2 - 1 : ℤ) : ℝ) < (p - (s : ℂ) * v).im := by
      rw [FlipWall.sub_mul_im]; push_cast; linarith
    have k4 : (p - (s : ℂ) * v).im < ((u.2 - 1 : ℤ) : ℝ) + 1 := by
      rw [FlipWall.sub_mul_im]; push_cast; linarith
    have hdn : p - (s : ℂ) * v ∈ Work.HornSC.CellBoundaryJordan.iCell ((u.1, u.2 - 1) : ℤ × ℤ) :=
      ⟨k1, k2, k3, k4⟩
    have key : (((u.1, u.2) : ℤ × ℤ) ∈ A ↔ ¬ (((u.1, u.2 - 1) : ℤ × ℤ) ∈ A)) := by
      simp only [Work.HornSC.CellBoundaryJordan.hWallAt] at hu
      tauto
    simp only [FlipWall.mem_cellUnion_of_mem_iCell hup, FlipWall.mem_cellUnion_of_mem_iCell hdn]
    exact key
  · -- `p` lies in the relative interior of a vertical wall segment at `u`
    rw [Work.HornSC.CellBoundaryJordan.mem_vSeg] at hpu
    obtain ⟨hre, hle, hle'⟩ := hpu
    have him1 : (u.2 : ℝ) < p.im := by
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exact absurd (FlipWall.eq_lpt_of_re_im hre h.symm) (hnl.notMem_lpt (u.1, u.2))
    have him2 : p.im < (u.2 : ℝ) + 1 := by
      rcases lt_or_eq_of_le hle' with h | h
      · exact h
      · have h' : p.im = ((u.2 + 1 : ℤ) : ℝ) := by push_cast; exact h
        exact absurd (FlipWall.eq_lpt_of_re_im hre h') (hnl.notMem_lpt (u.1, u.2 + 1))
    set b : ℝ := min (p.im - (u.2 : ℝ)) ((u.2 : ℝ) + 1 - p.im) with hb
    have hb1 : b ≤ p.im - (u.2 : ℝ) := min_le_left _ _
    have hb2 : b ≤ (u.2 : ℝ) + 1 - p.im := min_le_right _ _
    have hb_pos : 0 < b := lt_min (by linarith) (by linarith)
    refine ⟨min (b / v.im) (1 / v.re), lt_min (div_pos hb_pos hvi) (one_div_pos.mpr hvr), ?_⟩
    intro s hs0 hs
    have hsv_re : 0 < s * v.re := mul_pos hs0 hvr
    have hsv_im : 0 < s * v.im := mul_pos hs0 hvi
    have hs_b : s * v.im < b := by
      have h : s < b / v.im := lt_of_lt_of_le hs (min_le_left _ _)
      rwa [lt_div_iff₀ hvi] at h
    have hs_1 : s * v.re < 1 := by
      have h : s < 1 / v.re := lt_of_lt_of_le hs (min_le_right _ _)
      rwa [lt_div_iff₀ hvr] at h
    have h1 : (u.1 : ℝ) < (p + (s : ℂ) * v).re := by
      rw [FlipWall.add_mul_re]; linarith
    have h2 : (p + (s : ℂ) * v).re < (u.1 : ℝ) + 1 := by
      rw [FlipWall.add_mul_re]; linarith
    have h3 : (u.2 : ℝ) < (p + (s : ℂ) * v).im := by
      rw [FlipWall.add_mul_im]; linarith
    have h4 : (p + (s : ℂ) * v).im < (u.2 : ℝ) + 1 := by
      rw [FlipWall.add_mul_im]; linarith
    have hup : p + (s : ℂ) * v ∈ Work.HornSC.CellBoundaryJordan.iCell ((u.1, u.2) : ℤ × ℤ) :=
      ⟨h1, h2, h3, h4⟩
    have k1 : ((u.1 - 1 : ℤ) : ℝ) < (p - (s : ℂ) * v).re := by
      rw [FlipWall.sub_mul_re]; push_cast; linarith
    have k2 : (p - (s : ℂ) * v).re < ((u.1 - 1 : ℤ) : ℝ) + 1 := by
      rw [FlipWall.sub_mul_re]; push_cast; linarith
    have k3 : (u.2 : ℝ) < (p - (s : ℂ) * v).im := by
      rw [FlipWall.sub_mul_im]; linarith
    have k4 : (p - (s : ℂ) * v).im < (u.2 : ℝ) + 1 := by
      rw [FlipWall.sub_mul_im]; linarith
    have hdn : p - (s : ℂ) * v ∈ Work.HornSC.CellBoundaryJordan.iCell ((u.1 - 1, u.2) : ℤ × ℤ) :=
      ⟨k1, k2, k3, k4⟩
    have key : (((u.1, u.2) : ℤ × ℤ) ∈ A ↔ ¬ (((u.1 - 1, u.2) : ℤ × ℤ) ∈ A)) := by
      simp only [Work.HornSC.CellBoundaryJordan.vWallAt] at hu
      tauto
    simp only [FlipWall.mem_cellUnion_of_mem_iCell hup, FlipWall.mem_cellUnion_of_mem_iCell hdn]
    exact key

end Work.PlanarSC.JC
