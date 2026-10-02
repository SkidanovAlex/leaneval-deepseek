import Mathlib
import Submission.Work.Stems.Hur2b.NetReadDefs
import Submission.Work.Stems.Hur2b.NetTree
import Submission.Work.Stems.Hur2b.NetExitGeom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The extended readings on the boundary of the net region land in the tree

The `k`-th reading `readExt k : I² → ∂I³` of the T-net is affine on the cell `netCell k`; on that
cell the clamped cell coordinates `cellCoord k z = (8 z₀ - i, 8 z₁ - j)` are the honest cell
coordinates, so that

`readExt k z = netRead k (8 z₀ - i, 8 z₁ - j)`.

Writing out the six affine readings (`readExt_val_0`, …, `readExt_val_5`) gives, on the cell, for
each output coordinate of the read point, a *clamped affine function of a single coordinate of `z`*
(and one coordinate frozen at the face value `0` or `1`).

The point of the file is the geometric input to the pinched model: if `z` lies in a net cell but not
in the interior of the net region `D = ⋃ k, netCell k` — that is, `z` is on the boundary `∂D` of the
T-shaped region — then the read point lies in the **tree** `Tree` of `∂I³` (the union of the seven
spikes of the walk).  Indeed the belt and the column of the T-net are open *subsets of the interior*
of `D` (`openBeltSet_subset_interior`, `openColSet_subset_interior`), so the hypothesis says that
`z` is not in the open belt and not in the open column; combined with the four inequalities defining
the cell this pins one of the two moving coordinates to an end of its cell, which makes the
corresponding clamped coordinate of the read point equal to `0` or `1`, i.e. puts the read point on
one of the seven spikes.

Everything is a finite case analysis over the six cells (the arithmetic is linear, so `linarith`
does it, and the few specific values are computed with `norm_num`).
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

/-! ## Elementary facts about the clamping and the affine readings -/

/-- `clamp r = 0` for `r ≤ 0`. -/
theorem clamp_eq_zero_of_nonpos {r : ℝ} (h : r ≤ 0) : clamp r = 0 :=
  Set.projIcc_of_le_left zero_le_one h

/-- `clamp r = 1` for `1 ≤ r`. -/
theorem clamp_eq_one_of_one_le {r : ℝ} (h : 1 ≤ r) : clamp r = 1 :=
  Set.projIcc_of_right_le zero_le_one h

/-- The underlying point of a face inclusion. -/
theorem faceIncl_apply (i : Fin 3) (b : Fin 2) (t : IC 2) :
    ((faceIncl i b) t).1 = faceFun i (bval b) t := rfl

theorem faceFun_zero_zero (b : unitInterval) (t : IC 2) : (faceFun (0:Fin 3) b t) 0 = b := by
  rw [faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]

theorem faceFun_zero_one (b : unitInterval) (t : IC 2) : (faceFun (0:Fin 3) b t) 1 = t 0 := by
  rw [faceFun_apply, Fin.succAbove_cases_eq_insertNth]
  rw [show (1:Fin 3) = (0:Fin 3).succAbove (0:Fin 2) by decide]
  exact Fin.insertNth_apply_succAbove _ _ _ _

theorem faceFun_zero_two (b : unitInterval) (t : IC 2) : (faceFun (0:Fin 3) b t) 2 = t 1 := by
  rw [faceFun_apply, Fin.succAbove_cases_eq_insertNth]
  rw [show (2:Fin 3) = (0:Fin 3).succAbove (1:Fin 2) by decide]
  exact Fin.insertNth_apply_succAbove _ _ _ _

theorem faceFun_one_zero (b : unitInterval) (t : IC 2) : (faceFun (1:Fin 3) b t) 0 = t 0 := by
  rw [faceFun_apply, Fin.succAbove_cases_eq_insertNth]
  rw [show (0:Fin 3) = (1:Fin 3).succAbove (0:Fin 2) by decide]
  exact Fin.insertNth_apply_succAbove _ _ _ _

theorem faceFun_one_one (b : unitInterval) (t : IC 2) : (faceFun (1:Fin 3) b t) 1 = b := by
  rw [faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]

theorem faceFun_one_two (b : unitInterval) (t : IC 2) : (faceFun (1:Fin 3) b t) 2 = t 1 := by
  rw [faceFun_apply, Fin.succAbove_cases_eq_insertNth]
  rw [show (2:Fin 3) = (1:Fin 3).succAbove (1:Fin 2) by decide]
  exact Fin.insertNth_apply_succAbove _ _ _ _

theorem faceFun_two_zero (b : unitInterval) (t : IC 2) : (faceFun (2:Fin 3) b t) 0 = t 0 := by
  rw [faceFun_apply, Fin.succAbove_cases_eq_insertNth]
  rw [show (0:Fin 3) = (2:Fin 3).succAbove (0:Fin 2) by decide]
  exact Fin.insertNth_apply_succAbove _ _ _ _

theorem faceFun_two_one (b : unitInterval) (t : IC 2) : (faceFun (2:Fin 3) b t) 1 = t 1 := by
  rw [faceFun_apply, Fin.succAbove_cases_eq_insertNth]
  rw [show (1:Fin 3) = (2:Fin 3).succAbove (1:Fin 2) by decide]
  exact Fin.insertNth_apply_succAbove _ _ _ _

theorem faceFun_two_two (b : unitInterval) (t : IC 2) : (faceFun (2:Fin 3) b t) 2 = b := by
  rw [faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]

theorem readMap_apply_zero (α a β b : ℝ) (t : IC 2) :
    (readMap α a β b) t 0 = clamp (α * (t 0:ℝ) + a) := by simp [readMap, aff, pair2]

theorem readMap_apply_one (α a β b : ℝ) (t : IC 2) :
    (readMap α a β b) t 1 = clamp (β * (t 1:ℝ) + b) := by simp [readMap, aff, pair2]

theorem readSwap_apply_zero (α a β b : ℝ) (t : IC 2) :
    (readSwap α a β b) t 0 = clamp (β * (t 1:ℝ) + b) := by simp [readSwap, aff, pair2]

theorem readSwap_apply_one (α a β b : ℝ) (t : IC 2) :
    (readSwap α a β b) t 1 = clamp (α * (t 0:ℝ) + a) := by simp [readSwap, aff, pair2]

/-! ## The six readings on their cells

On the cell `netCell k` the cell coordinates of `z` are `8 z₀ - i`, `8 z₁ - j` with `(i,j) =
netCellIdx k` (the clamping is inactive), and the affine reading gives the following values. -/

theorem readExt_val_0 {z : IC 2} (hz : z ∈ netCell 0) :
    (readExt 0 z).1 = triple (clamp (19 - 64 * (z 0 : ℝ))) 1 (clamp (64 * (z 1 : ℝ) - 27)) := by
  have hz' := hz
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at hz'
  push_cast at hz'
  obtain ⟨h0a, h0b, h1a, h1b⟩ := hz'
  have hs0 : ((cellCoord 0 z) 0 : ℝ) = 8 * (z 0 : ℝ) - 2 := by
    rw [cellCoord_coe]; norm_num [netCellIdx]
    exact clamp_val _ ⟨by linarith, by linarith⟩
  have hs1 : ((cellCoord 0 z) 1 : ℝ) = 8 * (z 1 : ℝ) - 3 := by
    rw [cellCoord_coe]; norm_num [netCellIdx]
    exact clamp_val _ ⟨by linarith, by linarith⟩
  funext i
  fin_cases i
  · show (readExt 0 z).1 0 = clamp (19 - 64 * (z 0 : ℝ))
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_one_zero,
      readMap_apply_zero, hs0]
    congr 1; ring
  · show (readExt 0 z).1 1 = 1
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_one_one, bval_one]
  · show (readExt 0 z).1 2 = clamp (64 * (z 1 : ℝ) - 27)
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_one_two,
      readMap_apply_one, hs1]
    congr 1; ring

theorem readExt_val_1 {z : IC 2} (hz : z ∈ netCell 1) :
    (readExt 1 z).1 = triple 0 (clamp (28 - 64 * (z 0 : ℝ))) (clamp (64 * (z 1 : ℝ) - 27)) := by
  have hz' := hz
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at hz'
  push_cast at hz'
  obtain ⟨h0a, h0b, h1a, h1b⟩ := hz'
  have hs0 : ((cellCoord 1 z) 0 : ℝ) = 8 * (z 0 : ℝ) - 3 := by
    rw [cellCoord_coe]; norm_num [netCellIdx]
    exact clamp_val _ ⟨by linarith, by linarith⟩
  have hs1 : ((cellCoord 1 z) 1 : ℝ) = 8 * (z 1 : ℝ) - 3 := by
    rw [cellCoord_coe]; norm_num [netCellIdx]
    exact clamp_val _ ⟨by linarith, by linarith⟩
  funext i
  fin_cases i
  · show (readExt 1 z).1 0 = 0
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_zero_zero,
      bval_zero]
  · show (readExt 1 z).1 1 = clamp (28 - 64 * (z 0 : ℝ))
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_zero_one,
      readMap_apply_zero, hs0]
    congr 1; ring
  · show (readExt 1 z).1 2 = clamp (64 * (z 1 : ℝ) - 27)
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_zero_two,
      readMap_apply_one, hs1]
    congr 1; ring

theorem readExt_val_2 {z : IC 2} (hz : z ∈ netCell 2) :
    (readExt 2 z).1 = triple (clamp (64 * (z 0 : ℝ) - 36)) 0 (clamp (64 * (z 1 : ℝ) - 27)) := by
  have hz' := hz
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at hz'
  push_cast at hz'
  obtain ⟨h0a, h0b, h1a, h1b⟩ := hz'
  have hs0 : ((cellCoord 2 z) 0 : ℝ) = 8 * (z 0 : ℝ) - 4 := by
    rw [cellCoord_coe]; norm_num [netCellIdx]
    exact clamp_val _ ⟨by linarith, by linarith⟩
  have hs1 : ((cellCoord 2 z) 1 : ℝ) = 8 * (z 1 : ℝ) - 3 := by
    rw [cellCoord_coe]; norm_num [netCellIdx]
    exact clamp_val _ ⟨by linarith, by linarith⟩
  funext i
  fin_cases i
  · show (readExt 2 z).1 0 = clamp (64 * (z 0 : ℝ) - 36)
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_one_zero,
      readMap_apply_zero, hs0]
    congr 1; ring
  · show (readExt 2 z).1 1 = 0
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_one_one,
      bval_zero]
  · show (readExt 2 z).1 2 = clamp (64 * (z 1 : ℝ) - 27)
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_one_two,
      readMap_apply_one, hs1]
    congr 1; ring

theorem readExt_val_3 {z : IC 2} (hz : z ∈ netCell 3) :
    (readExt 3 z).1 = triple 1 (clamp (64 * (z 0 : ℝ) - 45)) (clamp (64 * (z 1 : ℝ) - 27)) := by
  have hz' := hz
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at hz'
  push_cast at hz'
  obtain ⟨h0a, h0b, h1a, h1b⟩ := hz'
  have hs0 : ((cellCoord 3 z) 0 : ℝ) = 8 * (z 0 : ℝ) - 5 := by
    rw [cellCoord_coe]; norm_num [netCellIdx]
    exact clamp_val _ ⟨by linarith, by linarith⟩
  have hs1 : ((cellCoord 3 z) 1 : ℝ) = 8 * (z 1 : ℝ) - 3 := by
    rw [cellCoord_coe]; norm_num [netCellIdx]
    exact clamp_val _ ⟨by linarith, by linarith⟩
  funext i
  fin_cases i
  · show (readExt 3 z).1 0 = 1
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_zero_zero,
      bval_one]
  · show (readExt 3 z).1 1 = clamp (64 * (z 0 : ℝ) - 45)
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_zero_one,
      readMap_apply_zero, hs0]
    congr 1; ring
  · show (readExt 3 z).1 2 = clamp (64 * (z 1 : ℝ) - 27)
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_zero_two,
      readMap_apply_one, hs1]
    congr 1; ring

theorem readExt_val_4 {z : IC 2} (hz : z ∈ netCell 4) :
    (readExt 4 z).1 = triple (clamp (19 - 64 * (z 1 : ℝ))) (clamp (28 - 64 * (z 0 : ℝ))) 0 := by
  have hz' := hz
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at hz'
  push_cast at hz'
  obtain ⟨h0a, h0b, h1a, h1b⟩ := hz'
  have hs0 : ((cellCoord 4 z) 0 : ℝ) = 8 * (z 0 : ℝ) - 3 := by
    rw [cellCoord_coe]; norm_num [netCellIdx]
    exact clamp_val _ ⟨by linarith, by linarith⟩
  have hs1 : ((cellCoord 4 z) 1 : ℝ) = 8 * (z 1 : ℝ) - 2 := by
    rw [cellCoord_coe]; norm_num [netCellIdx]
    exact clamp_val _ ⟨by linarith, by linarith⟩
  funext i
  fin_cases i
  · show (readExt 4 z).1 0 = clamp (19 - 64 * (z 1 : ℝ))
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_two_zero,
      readSwap_apply_zero, hs1]
    congr 1; ring
  · show (readExt 4 z).1 1 = clamp (28 - 64 * (z 0 : ℝ))
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_two_one,
      readSwap_apply_one, hs0]
    congr 1; ring
  · show (readExt 4 z).1 2 = 0
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_two_two,
      bval_zero]

theorem readExt_val_5 {z : IC 2} (hz : z ∈ netCell 5) :
    (readExt 5 z).1 = triple (clamp (64 * (z 1 : ℝ) - 36)) (clamp (28 - 64 * (z 0 : ℝ))) 1 := by
  have hz' := hz
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at hz'
  push_cast at hz'
  obtain ⟨h0a, h0b, h1a, h1b⟩ := hz'
  have hs0 : ((cellCoord 5 z) 0 : ℝ) = 8 * (z 0 : ℝ) - 3 := by
    rw [cellCoord_coe]; norm_num [netCellIdx]
    exact clamp_val _ ⟨by linarith, by linarith⟩
  have hs1 : ((cellCoord 5 z) 1 : ℝ) = 8 * (z 1 : ℝ) - 4 := by
    rw [cellCoord_coe]; norm_num [netCellIdx]
    exact clamp_val _ ⟨by linarith, by linarith⟩
  funext i
  fin_cases i
  · show (readExt 5 z).1 0 = clamp (64 * (z 1 : ℝ) - 36)
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_two_zero,
      readSwap_apply_zero, hs1]
    congr 1; ring
  · show (readExt 5 z).1 1 = clamp (28 - 64 * (z 0 : ℝ))
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_two_one,
      readSwap_apply_one, hs0]
    congr 1; ring
  · show (readExt 5 z).1 2 = 1
    simp only [readExt, netRead, ContinuousMap.comp_apply, faceIncl_apply, faceFun_two_two,
      bval_one]

/-! ## The seven spikes, as introduction rules for `Tree` -/

theorem tree_br1 {p : IC 3} (h1 : p 1 = 0) (h2 : p 2 = 0) : Tree p := Or.inl ⟨h1, h2⟩

theorem tree_br2 {p : IC 3} (h0 : p 0 = 1) (h2 : p 2 = 0) : Tree p :=
  Or.inr (Or.inl ⟨h0, h2⟩)

theorem tree_br3 {p : IC 3} (h0 : p 0 = 1) (h1 : p 1 = 1) : Tree p :=
  Or.inr (Or.inr (Or.inl ⟨h0, h1⟩))

theorem tree_br4 {p : IC 3} (h1 : p 1 = 1) (h2 : p 2 = 0) : Tree p :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))

theorem tree_br5 {p : IC 3} (h0 : p 0 = 1) (h2 : p 2 = 1) : Tree p :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h2⟩))))

theorem tree_br6 {p : IC 3} (h1 : p 1 = 1) (h2 : p 2 = 1) : Tree p :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))

theorem tree_br7 {p : IC 3} (h1 : p 1 = 0) (h2 : p 2 = 1) : Tree p :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))))

/-! ## The six cells -/

/-- The cell `0` (grid cell `(2,3)`, face `y = 1`). -/
theorem tree_0 {z : IC 2} (hz : z ∈ netCell 0)
    (hB : (z 0 : ℝ) ≤ 1/4 ∨ 3/4 ≤ (z 0 : ℝ) ∨ (z 1 : ℝ) ≤ 3/8 ∨ 1/2 ≤ (z 1 : ℝ)) :
    Tree (readExt 0 z).1 := by
  have hz' := hz
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at hz'
  push_cast at hz'
  obtain ⟨h0a, h0b, h1a, h1b⟩ := hz'
  rw [readExt_val_0 hz]
  rcases hB with h | h | h | h
  · have hz0 : (z 0 : ℝ) = 1/4 := by linarith
    have hA : clamp (19 - 64 * (z 0 : ℝ)) = 1 := by
      rw [hz0, show (19:ℝ) - 64 * (1/4) = 3 by ring]
      exact clamp_eq_one_of_one_le (by norm_num)
    rw [hA]
    exact tree_br3 rfl rfl
  · linarith
  · have hz1 : (z 1 : ℝ) = 3/8 := by linarith
    have hC : clamp (64 * (z 1 : ℝ) - 27) = 0 := by
      rw [hz1, show (64:ℝ) * (3/8) - 27 = -3 by ring]
      exact clamp_eq_zero_of_nonpos (by norm_num)
    rw [hC]
    exact tree_br4 rfl rfl
  · have hz1 : (z 1 : ℝ) = 1/2 := by linarith
    have hC : clamp (64 * (z 1 : ℝ) - 27) = 1 := by
      rw [hz1, show (64:ℝ) * (1/2) - 27 = 5 by ring]
      exact clamp_eq_one_of_one_le (by norm_num)
    rw [hC]
    exact tree_br6 rfl rfl

/-- The cell `1` (grid cell `(3,3)`, face `x = 0`). -/
theorem tree_1 {z : IC 2} (hz : z ∈ netCell 1)
    (hB : (z 0 : ℝ) ≤ 1/4 ∨ 3/4 ≤ (z 0 : ℝ) ∨ (z 1 : ℝ) ≤ 3/8 ∨ 1/2 ≤ (z 1 : ℝ))
    (hC : (z 0 : ℝ) ≤ 3/8 ∨ 1/2 ≤ (z 0 : ℝ) ∨ (z 1 : ℝ) ≤ 1/4 ∨ 5/8 ≤ (z 1 : ℝ)) :
    Tree (readExt 1 z).1 := by
  have hz' := hz
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at hz'
  push_cast at hz'
  obtain ⟨h0a, h0b, h1a, h1b⟩ := hz'
  have hCv : clamp (64 * (z 1 : ℝ) - 27) = 0 ∨ clamp (64 * (z 1 : ℝ) - 27) = 1 := by
    rcases hB with h | h | h | h
    · linarith
    · linarith
    · left
      have hz1 : (z 1 : ℝ) = 3/8 := by linarith
      rw [hz1, show (64:ℝ) * (3/8) - 27 = -3 by ring]
      exact clamp_eq_zero_of_nonpos (by norm_num)
    · right
      have hz1 : (z 1 : ℝ) = 1/2 := by linarith
      rw [hz1, show (64:ℝ) * (1/2) - 27 = 5 by ring]
      exact clamp_eq_one_of_one_le (by norm_num)
  have hBv : clamp (28 - 64 * (z 0 : ℝ)) = 0 ∨ clamp (28 - 64 * (z 0 : ℝ)) = 1 := by
    rcases hC with h | h | h | h
    · right
      have hz0 : (z 0 : ℝ) = 3/8 := by linarith
      rw [hz0, show (28:ℝ) - 64 * (3/8) = 4 by ring]
      exact clamp_eq_one_of_one_le (by norm_num)
    · left
      have hz0 : (z 0 : ℝ) = 1/2 := by linarith
      rw [hz0, show (28:ℝ) - 64 * (1/2) = -4 by ring]
      exact clamp_eq_zero_of_nonpos (by norm_num)
    · linarith
    · linarith
  rw [readExt_val_1 hz]
  rcases hBv with h1 | h1 <;> rcases hCv with h2 | h2 <;> rw [h1, h2]
  · exact tree_br1 rfl rfl
  · exact tree_br7 rfl rfl
  · exact tree_br4 rfl rfl
  · exact tree_br6 rfl rfl

/-- The cell `2` (grid cell `(4,3)`, face `y = 0`). -/
theorem tree_2 {z : IC 2} (hz : z ∈ netCell 2)
    (hB : (z 0 : ℝ) ≤ 1/4 ∨ 3/4 ≤ (z 0 : ℝ) ∨ (z 1 : ℝ) ≤ 3/8 ∨ 1/2 ≤ (z 1 : ℝ)) :
    Tree (readExt 2 z).1 := by
  have hz' := hz
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at hz'
  push_cast at hz'
  obtain ⟨h0a, h0b, h1a, h1b⟩ := hz'
  have hCv : clamp (64 * (z 1 : ℝ) - 27) = 0 ∨ clamp (64 * (z 1 : ℝ) - 27) = 1 := by
    rcases hB with h | h | h | h
    · linarith
    · linarith
    · left
      have hz1 : (z 1 : ℝ) = 3/8 := by linarith
      rw [hz1, show (64:ℝ) * (3/8) - 27 = -3 by ring]
      exact clamp_eq_zero_of_nonpos (by norm_num)
    · right
      have hz1 : (z 1 : ℝ) = 1/2 := by linarith
      rw [hz1, show (64:ℝ) * (1/2) - 27 = 5 by ring]
      exact clamp_eq_one_of_one_le (by norm_num)
  rw [readExt_val_2 hz]
  rcases hCv with h2 | h2 <;> rw [h2]
  · exact tree_br1 rfl rfl
  · exact tree_br7 rfl rfl

/-- The cell `3` (grid cell `(5,3)`, face `x = 1`). -/
theorem tree_3 {z : IC 2} (hz : z ∈ netCell 3)
    (hB : (z 0 : ℝ) ≤ 1/4 ∨ 3/4 ≤ (z 0 : ℝ) ∨ (z 1 : ℝ) ≤ 3/8 ∨ 1/2 ≤ (z 1 : ℝ)) :
    Tree (readExt 3 z).1 := by
  have hz' := hz
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at hz'
  push_cast at hz'
  obtain ⟨h0a, h0b, h1a, h1b⟩ := hz'
  rw [readExt_val_3 hz]
  rcases hB with h | h | h | h
  · linarith
  · have hz0 : (z 0 : ℝ) = 3/4 := by linarith
    have hA : clamp (64 * (z 0 : ℝ) - 45) = 1 := by
      rw [hz0, show (64:ℝ) * (3/4) - 45 = 3 by ring]
      exact clamp_eq_one_of_one_le (by norm_num)
    rw [hA]
    exact tree_br3 rfl rfl
  · have hz1 : (z 1 : ℝ) = 3/8 := by linarith
    have hC : clamp (64 * (z 1 : ℝ) - 27) = 0 := by
      rw [hz1, show (64:ℝ) * (3/8) - 27 = -3 by ring]
      exact clamp_eq_zero_of_nonpos (by norm_num)
    rw [hC]
    exact tree_br2 rfl rfl
  · have hz1 : (z 1 : ℝ) = 1/2 := by linarith
    have hC : clamp (64 * (z 1 : ℝ) - 27) = 1 := by
      rw [hz1, show (64:ℝ) * (1/2) - 27 = 5 by ring]
      exact clamp_eq_one_of_one_le (by norm_num)
    rw [hC]
    exact tree_br5 rfl rfl

/-- The cell `4` (grid cell `(3,2)`, face `z = 0`). -/
theorem tree_4 {z : IC 2} (hz : z ∈ netCell 4)
    (hC : (z 0 : ℝ) ≤ 3/8 ∨ 1/2 ≤ (z 0 : ℝ) ∨ (z 1 : ℝ) ≤ 1/4 ∨ 5/8 ≤ (z 1 : ℝ)) :
    Tree (readExt 4 z).1 := by
  have hz' := hz
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at hz'
  push_cast at hz'
  obtain ⟨h0a, h0b, h1a, h1b⟩ := hz'
  rw [readExt_val_4 hz]
  rcases hC with h | h | h | h
  · have hz0 : (z 0 : ℝ) = 3/8 := by linarith
    have h1 : clamp (28 - 64 * (z 0 : ℝ)) = 1 := by
      rw [hz0, show (28:ℝ) - 64 * (3/8) = 4 by ring]
      exact clamp_eq_one_of_one_le (by norm_num)
    rw [h1]
    exact tree_br4 rfl rfl
  · have hz0 : (z 0 : ℝ) = 1/2 := by linarith
    have h1 : clamp (28 - 64 * (z 0 : ℝ)) = 0 := by
      rw [hz0, show (28:ℝ) - 64 * (1/2) = -4 by ring]
      exact clamp_eq_zero_of_nonpos (by norm_num)
    rw [h1]
    exact tree_br1 rfl rfl
  · have hz1 : (z 1 : ℝ) = 1/4 := by linarith
    have h1 : clamp (19 - 64 * (z 1 : ℝ)) = 1 := by
      rw [hz1, show (19:ℝ) - 64 * (1/4) = 3 by ring]
      exact clamp_eq_one_of_one_le (by norm_num)
    rw [h1]
    exact tree_br2 rfl rfl
  · linarith

/-- The cell `5` (grid cell `(3,4)`, face `z = 1`). -/
theorem tree_5 {z : IC 2} (hz : z ∈ netCell 5)
    (hC : (z 0 : ℝ) ≤ 3/8 ∨ 1/2 ≤ (z 0 : ℝ) ∨ (z 1 : ℝ) ≤ 1/4 ∨ 5/8 ≤ (z 1 : ℝ)) :
    Tree (readExt 5 z).1 := by
  have hz' := hz
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at hz'
  push_cast at hz'
  obtain ⟨h0a, h0b, h1a, h1b⟩ := hz'
  rw [readExt_val_5 hz]
  rcases hC with h | h | h | h
  · have hz0 : (z 0 : ℝ) = 3/8 := by linarith
    have h1 : clamp (28 - 64 * (z 0 : ℝ)) = 1 := by
      rw [hz0, show (28:ℝ) - 64 * (3/8) = 4 by ring]
      exact clamp_eq_one_of_one_le (by norm_num)
    rw [h1]
    exact tree_br6 rfl rfl
  · have hz0 : (z 0 : ℝ) = 1/2 := by linarith
    have h1 : clamp (28 - 64 * (z 0 : ℝ)) = 0 := by
      rw [hz0, show (28:ℝ) - 64 * (1/2) = -4 by ring]
      exact clamp_eq_zero_of_nonpos (by norm_num)
    rw [h1]
    exact tree_br7 rfl rfl
  · linarith
  · have hz1 : (z 1 : ℝ) = 5/8 := by linarith
    have h1 : clamp (64 * (z 1 : ℝ) - 36) = 1 := by
      rw [hz1, show (64:ℝ) * (5/8) - 36 = 4 by ring]
      exact clamp_eq_one_of_one_le (by norm_num)
    rw [h1]
    exact tree_br5 rfl rfl

/-! ## The boundary of the net region -/

/-- Outside the open belt: one of the four inequalities defining the belt fails. -/
theorem not_mem_openBelt {z : IC 2} (hz : z ∉ interior NetRegion) :
    (z 0 : ℝ) ≤ 1/4 ∨ 3/4 ≤ (z 0 : ℝ) ∨ (z 1 : ℝ) ≤ 3/8 ∨ 1/2 ≤ (z 1 : ℝ) := by
  have hnb : ¬ (z ∈ openBeltSet) := fun h => hz (openBeltSet_subset_interior h)
  simp only [openBeltSet, Set.mem_ofPred_eq, offOf_eq, not_and_or, not_lt] at hnb
  rcases hnb with h | h | h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (Or.inl (by linarith)))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))

/-- Outside the open column: one of the four inequalities defining the column fails. -/
theorem not_mem_openCol {z : IC 2} (hz : z ∉ interior NetRegion) :
    (z 0 : ℝ) ≤ 3/8 ∨ 1/2 ≤ (z 0 : ℝ) ∨ (z 1 : ℝ) ≤ 1/4 ∨ 5/8 ≤ (z 1 : ℝ) := by
  have hnc : ¬ (z ∈ openColSet) := fun h => hz (openColSet_subset_interior h)
  simp only [openColSet, Set.mem_ofPred_eq, offOf_eq, not_and_or, not_lt] at hnc
  rcases hnc with h | h | h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (Or.inl (by linarith)))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))

/-- **A point of a net cell outside the interior of the net region reads into the tree.** -/
theorem net_readExt_tree {z : Work.Stems.Cubical.IC 2} {k : Fin 6} (hk : z ∈ Work.Stems.Hur2b.netCell k) (hz : z ∉ interior Work.Stems.Hur2b.NetRegion) : Work.Stems.Hur2b.Tree (Work.Stems.Hur2b.readExt k z).1 := by
  have hB := not_mem_openBelt hz
  have hC := not_mem_openCol hz
  fin_cases k
  · exact tree_0 hk hB
  · exact tree_1 hk hB hC
  · exact tree_2 hk hB
  · exact tree_3 hk hB
  · exact tree_4 hk hC
  · exact tree_5 hk hC

/-- **Corollary**: a point of a net cell outside the interior of the net region reads into the
`1`-skeleton of `∂I³` (the tree consists of edges of the skeleton).  This is the form in which the
pinched model uses the statement. -/
theorem net_readExt_skel {z : Work.Stems.Cubical.IC 2} {k : Fin 6} (hk : z ∈ Work.Stems.Hur2b.netCell k)
    (hz : z ∉ interior Work.Stems.Hur2b.NetRegion) : Work.Stems.Hur2b.Skel3 (Work.Stems.Hur2b.readExt k z) := by
  have h := net_readExt_tree hk hz
  rw [show readExt k z = treeBdy (readExt k z).1 h from Subtype.ext rfl]
  exact Tree_skel h

end

end Work.Stems.Hur2b
