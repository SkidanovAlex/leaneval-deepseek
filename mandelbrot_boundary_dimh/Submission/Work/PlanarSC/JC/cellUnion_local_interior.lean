import Mathlib
import Submission.Work.PlanarSC.JC.RayBasic
import Submission.Work.HornSC.CellBoundaryJordan.Defs

/-!
# A point of a finite union of lattice cells off the wall set is an interior point

`Work.HornSC.cellUnion A` is the union of the closed unit cells of the integer lattice indexed by
a finite set `A`, and `Work.HornSC.CellBoundaryJordan.wallSet A` is the union of the closed unit
grid segments separating a cell of `A` from a cell outside `A`.

The main theorem `cellUnion_local_interior` shows that a point of `cellUnion A` that does not lie
on `wallSet A` is an *interior* point of `cellUnion A`: a point of the union which is not on a
wall is surrounded by cells of `A` only.

The proof has two elementary ingredients:

* `CellUL.floorCell_mem_of_dist_lt`: there is a positive radius `r` around `z` such that every
  point `w` with `‖w - z‖ < r` satisfies `z ∈ cell (⌊w.re⌋, ⌊w.im⌋)`, i.e. `z` belongs to the
  floor cell of every sufficiently close point `w`;
* `CellUL.wall_of_mem_cell_pair'`: if a point `z` lies in two cells, one of them in `A` and the
  other not, then `z` lies on a wall of `A`.
-/

namespace Work.PlanarSC.JC

open Set

namespace CellUL

open Work.HornSC Work.HornSC.CellBoundaryJordan

/-! ## The floor cell of a nearby point -/

/-- Every point of the plane lies in the closed unit cell whose lower left corner is the
coordinatewise floor of the point. -/
lemma mem_floorCell (w : ℂ) : w ∈ cell (⌊w.re⌋, ⌊w.im⌋) := by
  rw [mem_cell]
  exact ⟨Int.floor_le w.re, le_of_lt (Int.lt_floor_add_one w.re),
    Int.floor_le w.im, le_of_lt (Int.lt_floor_add_one w.im)⟩

/-- A "safe" radius around `t : ℝ` for the floor map: the distance from `t` to the nearest
integer if `t` is not an integer, and `1` if it is. -/
noncomputable def rho (t : ℝ) : ℝ :=
  if (⌊t⌋ : ℝ) = t then 1 else min (t - ⌊t⌋) (⌊t⌋ + 1 - t)

lemma rho_pos (t : ℝ) : 0 < rho t := by
  unfold rho
  split_ifs with ht
  · norm_num
  · refine lt_min ?_ ?_
    · have h := Int.floor_le t
      have hne : (⌊t⌋ : ℝ) ≠ t := ht
      have hlt : (⌊t⌋ : ℝ) < t := lt_of_le_of_ne h hne
      linarith
    · have h := Int.lt_floor_add_one t; linarith

/-- The defining property of the safe radius `rho`: a real number whose distance to `t` is less
than `rho t` lies in a unit interval with integer endpoint that contains `t`. -/
lemma rho_spec {t s : ℝ} (h : |s - t| < rho t) :
    (⌊s⌋ : ℝ) ≤ t ∧ t ≤ (⌊s⌋ : ℝ) + 1 := by
  rw [abs_lt] at h
  obtain ⟨hlo, hhi⟩ := h
  unfold rho at hlo hhi
  split_ifs at hlo hhi with ht
  · -- `t` is an integer
    have hle1 : ⌊s⌋ ≤ ⌊t⌋ := by
      have hh : s < ((⌊t⌋ + 1 : ℤ) : ℝ) := by
        rw [← ht] at hhi
        push_cast
        linarith
      have hlt := Int.floor_lt.mpr hh
      omega
    have hle2 : ⌊t⌋ - 1 ≤ ⌊s⌋ := by
      have hl : ((⌊t⌋ - 1 : ℤ) : ℝ) ≤ s := by
        rw [← ht] at hlo
        push_cast
        linarith
      exact Int.le_floor.mpr hl
    have c1 : ((⌊s⌋ : ℤ) : ℝ) ≤ ((⌊t⌋ : ℤ) : ℝ) := by exact_mod_cast hle1
    have c2 : ((⌊t⌋ : ℤ) : ℝ) - 1 ≤ ((⌊s⌋ : ℤ) : ℝ) := by
      have hh : ((⌊t⌋ - 1 : ℤ) : ℝ) ≤ ((⌊s⌋ : ℤ) : ℝ) := by exact_mod_cast hle2
      push_cast at hh
      linarith
    constructor
    · rw [ht] at c1; exact c1
    · rw [← ht]; linarith
  · -- `t` is not an integer
    have h1 : ((⌊t⌋ : ℤ) : ℝ) < s := by
      have hm : min (t - ⌊t⌋) (⌊t⌋ + 1 - t) ≤ t - ⌊t⌋ := min_le_left _ _
      linarith
    have h2 : s < ((⌊t⌋ + 1 : ℤ) : ℝ) := by
      have hm : min (t - ⌊t⌋) (⌊t⌋ + 1 - t) ≤ ⌊t⌋ + 1 - t := min_le_right _ _
      push_cast
      linarith
    have hfl : ⌊s⌋ = ⌊t⌋ := by
      refine le_antisymm ?_ ?_
      · have hlt := Int.floor_lt.mpr h2
        omega
      · exact Int.le_floor.mpr (le_of_lt h1)
    rw [hfl]
    exact ⟨Int.floor_le t, le_of_lt (Int.lt_floor_add_one t)⟩

/-- Within the radius `min (rho z.re) (rho z.im)` of `z`, every point lies in a unit cell that
also contains `z`. -/
lemma floorCell_mem_of_dist_lt {z w : ℂ}
    (h : ‖w - z‖ < min (rho z.re) (rho z.im)) :
    z ∈ cell (⌊w.re⌋, ⌊w.im⌋) := by
  have hr : |w.re - z.re| < rho z.re := by
    have h1 : |w.re - z.re| ≤ ‖w - z‖ := by
      simpa using Complex.abs_re_le_norm (w - z)
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le h (min_le_left _ _))
  have hi : |w.im - z.im| < rho z.im := by
    have h1 : |w.im - z.im| ≤ ‖w - z‖ := by
      simpa using Complex.abs_im_le_norm (w - z)
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le h (min_le_right _ _))
  obtain ⟨e1, e2⟩ := rho_spec hr
  obtain ⟨e3, e4⟩ := rho_spec hi
  rw [mem_cell]
  exact ⟨e1, e2, e3, e4⟩

/-! ## A pair of cells containing a common point lies across a wall -/

lemma mem_wallSet_of_mem_hSeg {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} {z : ℂ}
    (h : hWallAt A u) (hz : z ∈ hSeg u) : z ∈ wallSet A :=
  Or.inl (mem_hWallSet.mpr ⟨u, h, hz⟩)

lemma mem_wallSet_of_mem_vSeg {A : Finset (ℤ × ℤ)} {u : ℤ × ℤ} {z : ℂ}
    (h : vWallAt A u) (hz : z ∈ vSeg u) : z ∈ wallSet A :=
  Or.inr (mem_vWallSet.mpr ⟨u, h, hz⟩)

/-- Two `4`-adjacent cells that both contain `z`, exactly one of them in `A`, put `z` on a wall
of `A`: the common edge of the two cells is a wall and contains `z`. -/
lemma wallSet_of_adj4 {A : Finset (ℤ × ℤ)} {z : ℂ} {p q : ℤ × ℤ}
    (hp : z ∈ cell p) (hq : z ∈ cell q) (hadj : Adj4 p q) (hpA : p ∈ A) (hqA : q ∉ A) :
    z ∈ wallSet A := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_cell.mp hp
  rcases hadj with h | h | h | h
  · -- `q = (p.1 + 1, p.2)`
    subst h
    obtain ⟨k1, _, k3, k4⟩ := mem_cell.mp hq
    refine mem_wallSet_of_mem_vSeg (u := (p.1 + 1, p.2)) ?_ ?_
    · right
      refine ⟨hqA, ?_⟩
      show ((p.1 + 1 - 1, p.2) : ℤ × ℤ) ∈ A
      rw [show ((p.1 + 1 - 1, p.2) : ℤ × ℤ) = p by simp]
      exact hpA
    · rw [mem_vSeg]
      refine ⟨?_, k3, k4⟩
      have hh : ((p.1 + 1 : ℤ) : ℝ) = (p.1 : ℝ) + 1 := by push_cast; ring
      linarith
  · -- `q = (p.1 - 1, p.2)`
    subst h
    obtain ⟨_, k2, _, _⟩ := mem_cell.mp hq
    refine mem_wallSet_of_mem_vSeg (u := p) ?_ ?_
    · left
      exact ⟨hpA, hqA⟩
    · rw [mem_vSeg]
      refine ⟨?_, h3, h4⟩
      have hh : ((p.1 - 1 : ℤ) : ℝ) + 1 = (p.1 : ℝ) := by push_cast; ring
      linarith
  · -- `q = (p.1, p.2 + 1)`
    subst h
    obtain ⟨k1, k2, k3, _⟩ := mem_cell.mp hq
    refine mem_wallSet_of_mem_hSeg (u := (p.1, p.2 + 1)) ?_ ?_
    · right
      refine ⟨hqA, ?_⟩
      show ((p.1, p.2 + 1 - 1) : ℤ × ℤ) ∈ A
      rw [show ((p.1, p.2 + 1 - 1) : ℤ × ℤ) = p by simp]
      exact hpA
    · rw [mem_hSeg]
      refine ⟨?_, k1, k2⟩
      have hh : ((p.2 + 1 : ℤ) : ℝ) = (p.2 : ℝ) + 1 := by push_cast; ring
      linarith
  · -- `q = (p.1, p.2 - 1)`
    subst h
    obtain ⟨_, _, _, k4⟩ := mem_cell.mp hq
    refine mem_wallSet_of_mem_hSeg (u := p) ?_ ?_
    · left
      exact ⟨hpA, hqA⟩
    · rw [mem_hSeg]
      refine ⟨?_, h1, h2⟩
      have hh : ((p.2 - 1 : ℤ) : ℝ) + 1 = (p.2 : ℝ) := by push_cast; ring
      linarith

/-- If a point `z` lies in two unit cells, one of them in `A` and the other not, then `z` lies on
the wall set of `A`. -/
lemma wall_of_mem_cell_pair' {A : Finset (ℤ × ℤ)} {z : ℂ} {p q : ℤ × ℤ}
    (hp : z ∈ cell p) (hq : z ∈ cell q) (hpA : p ∈ A) (hqA : q ∉ A) :
    z ∈ wallSet A := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_cell.mp hp
  obtain ⟨k1, k2, k3, k4⟩ := mem_cell.mp hq
  -- the two cells are lattice neighbours
  have hle1 : |p.1 - q.1| ≤ 1 := by
    have hA1 : p.1 ≤ q.1 + 1 := by
      have hh : ((p.1 : ℤ) : ℝ) ≤ ((q.1 + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast hh
    have hA2 : q.1 ≤ p.1 + 1 := by
      have hh : ((q.1 : ℤ) : ℝ) ≤ ((p.1 + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast hh
    rw [abs_le]
    omega
  have hle2 : |p.2 - q.2| ≤ 1 := by
    have hA1 : p.2 ≤ q.2 + 1 := by
      have hh : ((p.2 : ℤ) : ℝ) ≤ ((q.2 + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast hh
    have hA2 : q.2 ≤ p.2 + 1 := by
      have hh : ((q.2 : ℤ) : ℝ) ≤ ((p.2 + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast hh
    rw [abs_le]
    omega
  rcases eq_or_ne p q with hpq | hpq
  · exact absurd (hpq ▸ hpA) hqA
  · by_cases hadj : Adj4 p q
    · exact wallSet_of_adj4 hp hq hadj hpA hqA
    · -- `p ≠ q` and not `4`-adjacent, so both coordinates differ and `(p.1, q.2)` is a common
      -- edge neighbour of `p` and `q`
      have h1ne : p.1 ≠ q.1 := by
        intro he
        have h2ne : p.2 ≠ q.2 := fun he2 => hpq (Prod.ext he he2)
        have hd2 : q.2 = p.2 + 1 ∨ q.2 = p.2 - 1 := by
          have := abs_le.mp hle2
          omega
        rcases hd2 with hc | hc
        · exact hadj (Or.inr (Or.inr (Or.inl (Prod.ext he.symm hc))))
        · exact hadj (Or.inr (Or.inr (Or.inr (Prod.ext he.symm hc))))
      have h2ne : p.2 ≠ q.2 := by
        intro he
        have hd1 : q.1 = p.1 + 1 ∨ q.1 = p.1 - 1 := by
          have := abs_le.mp hle1
          omega
        rcases hd1 with hc | hc
        · exact hadj (Or.inl (Prod.ext hc he.symm))
        · exact hadj (Or.inr (Or.inl (Prod.ext hc he.symm)))
      have hd1 : q.1 = p.1 + 1 ∨ q.1 = p.1 - 1 := by
        have := abs_le.mp hle1
        omega
      have hd2 : q.2 = p.2 + 1 ∨ q.2 = p.2 - 1 := by
        have := abs_le.mp hle2
        omega
      have hdz : z ∈ cell (p.1, q.2) := ⟨h1, h2, k3, k4⟩
      have hadj_pd : Adj4 p (p.1, q.2) := by
        rcases hd2 with hc | hc
        · exact Or.inr (Or.inr (Or.inl (Prod.ext rfl hc)))
        · exact Or.inr (Or.inr (Or.inr (Prod.ext rfl hc)))
      have hadj_dq : Adj4 (p.1, q.2) q := by
        rcases hd1 with hc | hc
        · exact Or.inl (Prod.ext hc rfl)
        · exact Or.inr (Or.inl (Prod.ext hc rfl))
      by_cases hdA : (p.1, q.2) ∈ A
      · exact wallSet_of_adj4 hdz hq hadj_dq hdA hqA
      · exact wallSet_of_adj4 hp hdz hadj_pd hpA hdA

end CellUL

theorem cellUnion_local_interior {A : Finset (ℤ × ℤ)} {z : ℂ}
    (hz : z ∈ Work.HornSC.cellUnion A) (hzw : z ∉ Work.HornSC.CellBoundaryJordan.wallSet A) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w - z‖ < r → w ∈ Work.HornSC.cellUnion A := by
  obtain ⟨p, hpA, hzp⟩ := Set.mem_iUnion₂.mp hz
  refine ⟨min (CellUL.rho z.re) (CellUL.rho z.im),
    lt_min (CellUL.rho_pos _) (CellUL.rho_pos _), fun w hw => ?_⟩
  have hzc : z ∈ Work.HornSC.cell (⌊w.re⌋, ⌊w.im⌋) := CellUL.floorCell_mem_of_dist_lt hw
  have hmem : (⌊w.re⌋, ⌊w.im⌋) ∈ A := by
    by_contra hc
    exact hzw (CellUL.wall_of_mem_cell_pair' hzp hzc hpA hc)
  exact Work.HornSC.cell_subset_cellUnion hmem (CellUL.mem_floorCell w)

end Work.PlanarSC.JC
