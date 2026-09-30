import Mathlib
import Submission.Work.RTOwed.CuspPiece
import Submission.Work.RTOwed.chartKlein_wall
import Submission.Work.RTOwed.cuspWallTableCerts
import Submission.Work.RTOwed.cuspCert.cubeOfMod_corner_dvd

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

/-!
# The single wall-crossing step of the cusp chart pasting

The chart `mbarLow v` is a pasting of the cube charts `cellPt v a k` (the chart of the cube `a` at
the unfolded coordinate `uhsXj q - lamV v k`) along the walls of the cubes.  This file supplies the
*one-step* bookkeeping: if the unfolded coordinate `y = uhsXj q - cuspCert.lamV v k` of a chart
point sits on a wall of the cube `a` (the face `y i = cubeCorner a i` for `side = 0` or
`y i = cubeCorner a i + 1` for `side = 1`), then the same point of `Mbar` is carried by the chart of
the neighbouring cube `wallNb a i side`, at the translate `k'` of `k` by the lattice vector
`wallLamV a i side`, and the two chart values differ by the group element `wallGamK a i side` of the
wall identification (`Work.RTOwed.chartKlein_wall`).
-/

/-- **Additivity of the lattice offset `lamV`.** -/
theorem cuspWall_lamV_add (v : Fin 5) (k k' : Fin 3 → ℤ) :
    cuspCert.lamV v (k + k') = cuspCert.lamV v k + cuspCert.lamV v k' := by
  apply PiLp.ext
  intro i
  show (cuspCert.lamK v (k + k') i : ℝ) = (cuspCert.lamK v k i : ℝ) + (cuspCert.lamK v k' i : ℝ)
  simp only [cuspCert.lamK, Pi.add_apply]
  push_cast
  ring

/-- The two test functions of a side agree whether the side is read as a `Fin 2` or as a `ℕ`. -/
theorem cuspWall_ite_side_zero (side : Fin 2) (a b : ℝ) :
    (if side = 0 then a else b) = (if (side : ℕ) = 0 then a else b) := by
  fin_cases side <;> simp

set_option maxHeartbeats 4000000 in
/-- The far cube of a wall lies in the same cusp as the near cube. -/
theorem cuspWall_cubeCusp_wallNb (a : Fin 48) (i : Fin 3) (side : Fin 2) :
    Work.Cusp.cubeCusp (wallNb a i side) = Work.Cusp.cubeCusp a := by
  revert a i side
  decide

/-- The coordinates of the wall lattice vector. -/
theorem cuspWall_wallLamV_apply (a : Fin 48) (i : Fin 3) (side : Fin 2) (j : Fin 3) :
    (wallLamV a i side) j = (wallLam a i side j : ℝ) := rfl

/-- **The coordinate across the wall is reflected into the far cube.** -/
theorem cuspWall_norm_coord (a : Fin 48) (i : Fin 3) (side : Fin 2) {y : CuspE3}
    (hwall : y i = (Work.Cusp.cubeCorner a i : ℝ) + (if side = 0 then 0 else 1)) :
    (y - wallLamV a i side) i
      = (Work.Cusp.cubeCorner (wallNb a i side) i : ℝ) + (if side = 0 then 1 else 0) := by
  obtain ⟨_, _, hN, _, _, _⟩ := cuspWallTableCerts
  have h := hN a i side
  simp only [cuspWall_wallLamV_apply] at h
  have h2 : (y - wallLamV a i side) i = y i - (wallLam a i side i : ℝ) := by
    simp only [PiLp.sub_apply, cuspWall_wallLamV_apply]
  rw [h2, hwall]
  linarith

/-- **The tangential coordinates are unchanged up to the shift of the corner.** -/
theorem cuspWall_tan_coord (a : Fin 48) (i : Fin 3) (side : Fin 2) {y : CuspE3} {j : Fin 3}
    (hj : j ≠ i) :
    (y - wallLamV a i side) j
      = (Work.Cusp.cubeCorner (wallNb a i side) j : ℝ) + (y j - (Work.Cusp.cubeCorner a j : ℝ)) := by
  obtain ⟨_, _, _, hT, _, _⟩ := cuspWallTableCerts
  have h := hT a i side j hj
  simp only [cuspWall_wallLamV_apply] at h
  have h2 : (y - wallLamV a i side) j = y j - (wallLam a i side j : ℝ) := by
    simp only [PiLp.sub_apply, cuspWall_wallLamV_apply]
  rw [h2]
  linarith

/-- **The wall translate of a point of the cube lies in the far cube.** -/
theorem cuspWall_mem_box (a : Fin 48) (i : Fin 3) (side : Fin 2) {y : CuspE3}
    (hy : y ∈ cubeBox a)
    (hwall : y i = (Work.Cusp.cubeCorner a i : ℝ) + (if side = 0 then 0 else 1)) :
    y - wallLamV a i side ∈ cubeBox (wallNb a i side) := by
  intro j
  by_cases hj : j = i
  · rw [hj, cuspWall_norm_coord a i side hwall]
    constructor <;> split_ifs <;> linarith
  · have hyj := hy j
    rw [cuspWall_tan_coord a i side hj]
    constructor <;> linarith [hyj.1, hyj.2]

/-- The predicate "on the upper wall" is inherited in the directions along the wall. -/
theorem cuspWall_hi_iff (a : Fin 48) (i : Fin 3) (side : Fin 2) {y : CuspE3} {j : Fin 3}
    (hj : j ≠ i) :
    ((y - wallLamV a i side) j = (Work.Cusp.cubeCorner (wallNb a i side) j : ℝ) + 1
      ↔ y j = (Work.Cusp.cubeCorner a j : ℝ) + 1) := by
  rw [cuspWall_tan_coord a i side hj]
  constructor <;> intro h <;> linarith

/-- The predicate "on the lower wall" is inherited in the directions along the wall. -/
theorem cuspWall_lo_iff (a : Fin 48) (i : Fin 3) (side : Fin 2) {y : CuspE3} {j : Fin 3}
    (hj : j ≠ i) :
    ((y - wallLamV a i side) j = (Work.Cusp.cubeCorner (wallNb a i side) j : ℝ)
      ↔ y j = (Work.Cusp.cubeCorner a j : ℝ)) := by
  rw [cuspWall_tan_coord a i side hj]
  constructor <;> intro h <;> linarith

/-- The one-unit thickening of the far cube contains the wall translate of the near cube. -/
theorem cuspWall_bound (a : Fin 48) (i : Fin 3) (side : Fin 2) {y : CuspE3}
    (hy : y ∈ cubeBox a)
    (hwall : y i = (Work.Cusp.cubeCorner a i : ℝ) + (if side = 0 then 0 else 1)) :
    ∀ j : Fin 3, (Work.Cusp.cubeCorner (wallNb a i side) j : ℝ) - 1 ≤ (y - wallLamV a i side) j
      ∧ (y - wallLamV a i side) j ≤ (Work.Cusp.cubeCorner (wallNb a i side) j : ℝ) + 2 := by
  intro j
  by_cases hj : j = i
  · rw [hj, cuspWall_norm_coord a i side hwall]
    constructor <;> split_ifs <;> linarith
  · have hyj := hy j
    rw [cuspWall_tan_coord a i side hj]
    constructor <;> linarith [hyj.1, hyj.2]

set_option maxHeartbeats 800000 in
theorem cuspWall_step (v : Fin 5) {a : Fin 48} (hca : Cusp.cubeCusp a = v) (i : Fin 3) (side : Fin 2)
    {k : Fin 3 → ℤ} {q : CuspE4} (hs : 11 / 10 ≤ q 3)
    (hu : uhsXj q - cuspCert.lamV v k ∈ cubeBox a)
    (hwall : (uhsXj q - cuspCert.lamV v k) i
      = (Cusp.cubeCorner a i : ℝ) + (if side = 0 then 0 else 1)) :
    ∃ k' : Fin 3 → ℤ, (cuspCert.lamV v k' = cuspCert.lamV v k + wallLamV a i side)
      ∧ cellPt v (wallNb a i side) k' q = FoldInst.act (wallGamK a i side) (cellPt v a k q)
      ∧ (uhsXj q - cuspCert.lamV v k') ∈ cubeBox (wallNb a i side)
      ∧ Cusp.cubeCusp (wallNb a i side) = v
      ∧ (uhsXj q - cuspCert.lamV v k') i = (Cusp.cubeCorner (wallNb a i side) i : ℝ)
          + (if side = 0 then 1 else 0)
      ∧ (∀ j : Fin 3, j ≠ i → ((uhsXj q - cuspCert.lamV v k') j
            = (Cusp.cubeCorner (wallNb a i side) j : ℝ) + 1
          ↔ (uhsXj q - cuspCert.lamV v k) j = (Cusp.cubeCorner a j : ℝ) + 1))
      ∧ (∀ j : Fin 3, j ≠ i → ((uhsXj q - cuspCert.lamV v k') j
            = (Cusp.cubeCorner (wallNb a i side) j : ℝ)
          ↔ (uhsXj q - cuspCert.lamV v k) j = (Cusp.cubeCorner a j : ℝ)))
      ∧ (∀ j : Fin 3, (Cusp.cubeCorner (wallNb a i side) j : ℝ) - 1
            ≤ (uhsXj q - cuspCert.lamV v k') j
          ∧ (uhsXj q - cuspCert.lamV v k') j ≤ (Cusp.cubeCorner (wallNb a i side) j : ℝ) + 2)
      := by
  obtain ⟨_, _, _, _, _, hLat⟩ := cuspWallTableCerts
  obtain ⟨k₀, hk₀⟩ := hLat a i side
  rw [hca] at hk₀
  have hkey : uhsXj q - cuspCert.lamV v (k + k₀)
      = (uhsXj q - cuspCert.lamV v k) - wallLamV a i side := by
    rw [cuspWall_lamV_add, ← hk₀]
    abel
  have hlam : cuspCert.lamV v (k + k₀) = cuspCert.lamV v k + wallLamV a i side := by
    rw [hk₀]; exact cuspWall_lamV_add v k k₀
  have hwall' : (uhsXj q - cuspCert.lamV v k) i
      = (Cusp.cubeCorner a i : ℝ) + (if (side : ℕ) = 0 then 0 else 1) := by
    rw [hwall, cuspWall_ite_side_zero]
  refine ⟨k + k₀, hlam, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cellPt, hkey]
    exact chartKlein_wall a i side hwall' (fun j => hu j) hs
  · rw [hkey]; exact cuspWall_mem_box a i side hu hwall
  · rw [cuspWall_cubeCusp_wallNb, hca]
  · rw [hkey]; exact cuspWall_norm_coord a i side hwall
  · rw [hkey]; intro j hj; exact cuspWall_hi_iff a i side hj
  · rw [hkey]; intro j hj; exact cuspWall_lo_iff a i side hj
  · rw [hkey]; exact cuspWall_bound a i side hu hwall

end Work.RTOwed
