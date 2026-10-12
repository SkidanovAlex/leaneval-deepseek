import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseBox.LatticeModel.Defs
import Submission.Work.BoseBox.LatticeModel.iUnion_pi_eq_pi_iUnion_and_disjoint
import Submission.Work.BoseBox.LatticeModel.sqrt_sum_sq_abs_sub_le
import Submission.Work.BoseBox.LatticeModel.sqrt_sum_sq_eq_zero_iff_and_coord_le
import Submission.Work.BoseBox.LatticeModel.tiling_Ico_monotone
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Geometry of the lattice cells of the FS normalisation

The cells `latticeCell h N k` of the mesh-`h`, `N`-cells-per-axis lattice
straddling the origin (see `Submission.Work.BoseBox.LatticeModel.Defs`) form a
measurable partition of the box `latticeBox h N` into cubes of volume `h³`, and
each cell is contained in the `h√3/2`-neighbourhood of its centre.

The proof reduces everything to the one-dimensional fact that the intervals
`[h(i−(N+1)/2), h(i+1−(N+1)/2))`, `i < N`, tile `[−h(N+1)/2, h(N−1)/2)`:
this is `tiling_Ico_monotone`, applied through the generic product lemma
`iUnion_pi_eq_pi_iUnion_and_disjoint` for the union and the disjointness, and
`Real.volume_pi_Ico` for the measure.  The two norm statements are
`sqrt_sum_sq_abs_sub_le` and `sqrt_sum_sq_eq_zero_iff_and_coord_le`.
-/

namespace Work.BoseBox.LatticeModel

/-- The `i`-th grid point of the mesh-`h` lattice with `N` cells per axis
straddling the origin: the common endpoint of the `(i-1)`-st and `i`-th cell
intervals, namely `h·(i − (N+1)/2)`. -/
private noncomputable def gridPt (h : ℝ) (N : ℕ) (i : ℕ) : ℝ := h * ((i : ℝ) - ((N : ℝ) + 1) / 2)

/-- The `i`-th one-dimensional cell interval
`[h(i−(N+1)/2), h(i+1−(N+1)/2))`. -/
private noncomputable def cellInterval (h : ℝ) (N : ℕ) (i : ℕ) : Set ℝ :=
  Set.Ico (gridPt h N i) (gridPt h N (i + 1))

private lemma gridPt_succ (h : ℝ) (N : ℕ) (i : ℕ) :
    gridPt h N (i + 1) = gridPt h N i + h := by
  simp only [gridPt]
  push_cast
  ring

private lemma gridPt_sub_half (h : ℝ) (N : ℕ) (k : Fin N) :
    gridPt h N k.val = h * ((k : ℝ) - (N : ℝ) / 2) - h / 2 := by
  simp only [gridPt]
  push_cast
  ring

private lemma gridPt_add_half (h : ℝ) (N : ℕ) (k : Fin N) :
    gridPt h N (k.val + 1) = h * ((k : ℝ) - (N : ℝ) / 2) + h / 2 := by
  simp only [gridPt]
  push_cast
  ring

private lemma monotone_gridPt (h : ℝ) (hh : 0 ≤ h) (N : ℕ) : Monotone (gridPt h N) := by
  intro i j hij
  simp only [gridPt]
  have h1 : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  nlinarith [hh, h1]

/-- The lattice cell is the product of the one-dimensional cell intervals. -/
private lemma latticeCell_eq_pi (h : ℝ) (N : ℕ) (k : Fin 3 → Fin N) :
    latticeCell h N k
      = Set.pi Set.univ (fun j : Fin 3 => cellInterval h N (k j).val) := by
  simp only [latticeCell, latticeCenter, gridPt, cellInterval]
  refine Set.pi_congr rfl (fun j _ => ?_)
  congr 1
  · push_cast; ring
  · push_cast; ring

/-- The lattice box is the product of the one-dimensional boxes. -/
private lemma latticeBox_eq_pi (h : ℝ) (N : ℕ) :
    latticeBox h N
      = Set.pi Set.univ (fun _ : Fin 3 => Set.Ico (gridPt h N 0) (gridPt h N N)) := by
  simp only [latticeBox, gridPt]
  refine Set.pi_congr rfl (fun j _ => ?_)
  congr 1
  · push_cast; ring
  · push_cast; ring

/-- The one-dimensional cell intervals tile the one-dimensional box. -/
private lemma iUnion_cellInterval (h : ℝ) (hh : 0 < h) (N : ℕ) :
    (⋃ i : Fin N, cellInterval h N i.val)
      = Set.Ico (gridPt h N 0) (gridPt h N N) := by
  have hconv : (⋃ i : Fin N, cellInterval h N i.val)
      = ⋃ i ∈ Finset.range N, cellInterval h N i := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Set.mem_iUnion]
      exact ⟨i.val, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr i.isLt, hi⟩⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hx⟩ := hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨hi, hx⟩ := hx
      rw [Set.mem_iUnion]
      exact ⟨⟨i, Finset.mem_range.mp hi⟩, hx⟩
  rw [hconv]
  exact (tiling_Ico_monotone (monotone_gridPt h hh.le N) N).1

/-- Distinct one-dimensional cell intervals are disjoint. -/
private lemma disjoint_cellInterval (h : ℝ) (hh : 0 < h) {N : ℕ} (i i' : Fin N) (hne : i ≠ i') :
    Disjoint (cellInterval h N i.val) (cellInterval h N i'.val) := by
  have h := (tiling_Ico_monotone (monotone_gridPt h hh.le N) N).2 i.val
    (Finset.mem_range.mpr i.isLt) i'.val (Finset.mem_range.mpr i'.isLt)
    (fun h => hne (Fin.ext h))
  simpa only [cellInterval] using h

private lemma measurableSet_latticeCell (h : ℝ) (N : ℕ) (k : Fin 3 → Fin N) :
    MeasurableSet (latticeCell h N k) := by
  rw [latticeCell_eq_pi]
  refine MeasurableSet.univ_pi (fun j => ?_)
  simp only [cellInterval]
  exact measurableSet_Ico

private lemma volume_latticeCell (h : ℝ) (hh : 0 < h) (N : ℕ) (k : Fin 3 → Fin N) :
    MeasureTheory.volume (latticeCell h N k) = ENNReal.ofReal (h ^ 3) := by
  have hstep : ∀ j : Fin 3, gridPt h N ((k j).val + 1) - gridPt h N (k j).val = h := by
    intro j
    rw [gridPt_succ]
    ring
  rw [latticeCell_eq_pi]
  simp only [cellInterval]
  rw [Real.volume_pi_Ico]
  rw [Finset.prod_congr rfl (fun j _ => by rw [hstep j])]
  rw [show (∏ _j : Fin 3, ENNReal.ofReal h) = ENNReal.ofReal (h ^ 3) from by
    rw [show (∏ _j : Fin 3, ENNReal.ofReal h) = ENNReal.ofReal h ^ 3 from by
      simp [Finset.prod_const]]
    exact (ENNReal.ofReal_pow hh.le 3).symm]

private lemma disjoint_latticeCell (h : ℝ) (hh : 0 < h) (N : ℕ) {k k' : Fin 3 → Fin N}
    (hne : k ≠ k') : Disjoint (latticeCell h N k) (latticeCell h N k') := by
  have h2 : ∀ a a' : Fin 3 → Fin N, a ≠ a' →
      Disjoint (Set.pi Set.univ (fun j : Fin 3 => cellInterval h N (a j).val))
        (Set.pi Set.univ (fun j : Fin 3 => cellInterval h N (a' j).val)) :=
    (iUnion_pi_eq_pi_iUnion_and_disjoint
      (fun (i : Fin N) (j : Fin 3) => cellInterval h N i.val)
      (fun i i' hi j => disjoint_cellInterval h hh i i' hi)).2
  have hk : latticeCell h N k = Set.pi Set.univ (fun j : Fin 3 => cellInterval h N (k j).val) :=
    latticeCell_eq_pi h N k
  have hk' : latticeCell h N k' = Set.pi Set.univ (fun j : Fin 3 => cellInterval h N (k' j).val) :=
    latticeCell_eq_pi h N k'
  rw [hk, hk']
  exact h2 k k' hne

private lemma iUnion_latticeCell_eq_latticeBox (h : ℝ) (hh : 0 < h) (N : ℕ) :
    (⋃ k : Fin 3 → Fin N, latticeCell h N k) = latticeBox h N := by
  have h1 : (⋃ k : Fin 3 → Fin N, Set.pi Set.univ (fun j : Fin 3 => cellInterval h N (k j).val))
      = Set.pi Set.univ (fun j : Fin 3 => ⋃ i : Fin N, cellInterval h N i.val) :=
    (iUnion_pi_eq_pi_iUnion_and_disjoint
      (fun (i : Fin N) (j : Fin 3) => cellInterval h N i.val)
      (fun i i' hi j => disjoint_cellInterval h hh i i' hi)).1
  have h1' : (⋃ k : Fin 3 → Fin N, latticeCell h N k)
      = ⋃ k : Fin 3 → Fin N, Set.pi Set.univ (fun j : Fin 3 => cellInterval h N (k j).val) :=
    Set.iUnion_congr fun k => latticeCell_eq_pi h N k
  rw [h1', h1, latticeBox_eq_pi]
  exact Set.pi_congr rfl (fun j _ => iUnion_cellInterval h hh N)

/-- `m < N` with `m - N/2 ≠ 0` forces `|m - N/2| ≥ 1/2`. -/
private lemma half_le_abs_nat_sub_half {m N : ℕ} (hm : (m : ℝ) - (N : ℝ) / 2 ≠ 0) :
    (1 : ℝ) / 2 ≤ |(m : ℝ) - (N : ℝ) / 2| := by
  have hz : (2 * (m : ℤ) - (N : ℤ)) ≠ 0 := by
    intro h0
    apply hm
    have hreal : ((2 * (m : ℤ) - (N : ℤ) : ℤ) : ℝ) = 2 * ((m : ℝ) - (N : ℝ) / 2) := by
      push_cast
      ring
    rw [h0] at hreal
    norm_num at hreal
    linarith
  have hcast : ((|2 * (m : ℤ) - (N : ℤ)| : ℤ) : ℝ)
      = |2 * ((m : ℝ) - (N : ℝ) / 2)| := by
    rw [Int.cast_abs]
    congr 1
    push_cast
    ring
  have h1 : (1 : ℝ) ≤ |2 * ((m : ℝ) - (N : ℝ) / 2)| := by
    rw [← hcast]
    exact_mod_cast Int.one_le_abs hz
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h1
  linarith

theorem latticeCell_geometry {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N) :
    (∀ k : Fin 3 → Fin N, MeasurableSet (latticeCell h N k)) ∧
    (∀ k k' : Fin 3 → Fin N, k ≠ k' → Disjoint (latticeCell h N k) (latticeCell h N k')) ∧
    (∀ k : Fin 3 → Fin N, MeasureTheory.volume (latticeCell h N k) = ENNReal.ofReal (h ^ 3)) ∧
    ((⋃ k : Fin 3 → Fin N, latticeCell h N k) = latticeBox h N) ∧
    (∀ k : Fin 3 → Fin N, ∀ x : Fin 3 → ℝ, x ∈ latticeCell h N k →
      |Submission.BoseGases.eucNorm3 x - Submission.BoseGases.eucNorm3 (latticeCenter h N k)|
        ≤ h * Real.sqrt 3 / 2) ∧
    (∀ k : Fin 3 → Fin N,
      Submission.BoseGases.eucNorm3 (latticeCenter h N k) = 0 ∨
        h / 2 ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun k => measurableSet_latticeCell h N k
  · exact fun k k' hne => disjoint_latticeCell h hh N hne
  · exact fun k => volume_latticeCell h hh N k
  · exact iUnion_latticeCell_eq_latticeBox h hh N
  · intro k x hx
    rw [latticeCell_eq_pi, Set.mem_univ_pi] at hx
    have hbound : ∀ j : Fin 3, |x j - latticeCenter h N k j| ≤ h / 2 := by
      intro j
      have hj := hx j
      simp only [cellInterval] at hj
      rw [Set.mem_Ico, gridPt_sub_half, gridPt_add_half] at hj
      rw [abs_le]
      constructor <;> simp only [latticeCenter] <;> linarith [hj.1, hj.2]
    have hmain := sqrt_sum_sq_abs_sub_le (h := h) hh.le hbound
    simpa only [Submission.BoseGases.eucNorm3] using hmain
  · intro k
    by_cases hall : ∀ j : Fin 3, (k j : ℝ) - (N : ℝ) / 2 = 0
    · left
      have hall' : ∀ j : Fin 3, latticeCenter h N k j = 0 := by
        intro j
        simp [latticeCenter, hall j]
      have hzero : Real.sqrt (∑ j : Fin 3, (latticeCenter h N k j) ^ 2) = 0 :=
        (sqrt_sum_sq_eq_zero_iff_and_coord_le (u := latticeCenter h N k)).1.mpr hall'
      simpa only [Submission.BoseGases.eucNorm3] using hzero
    · right
      obtain ⟨j, hj⟩ := not_forall.mp hall
      have hhalf : h / 2 ≤ |latticeCenter h N k j| := by
        have hd := half_le_abs_nat_sub_half (m := (k j).val) (N := N) hj
        simp only [latticeCenter, abs_mul, abs_of_pos hh]
        nlinarith [hd, hh]
      calc h / 2 ≤ |latticeCenter h N k j| := hhalf
        _ ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k) := by
            simpa only [Submission.BoseGases.eucNorm3] using
              (sqrt_sum_sq_eq_zero_iff_and_coord_le (u := latticeCenter h N k)).2 j

end Work.BoseBox.LatticeModel
