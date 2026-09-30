import Mathlib
import Submission.Work.RTOwed.mbarLow_foldLocal_helpers
import Submission.Work.RTOwed.cuspWall_step
import Submission.Work.RTOwed.mbarLow_eq_mbBranch_pos
import Submission.Work.RTOwed.cuspChartWallReflect
import Submission.Work.FoldInst.Basic
import Submission.Work.FoldInst.Data
import Submission.Work.FoldInst.Cert
import Submission.Work.FoldInst.CertFold
import Submission.Work.FoldInst.Polytope
import Submission.Work.FoldInst.Qbar_geometry
import Submission.Work.FoldInst.Action
import Submission.Work.FoldInst.Continuous
import Submission.Work.FoldInst.Atlas
import Submission.Work.FoldInst.Quotient
import Submission.Work.FoldInst.Connected
import Submission.Work.FoldInst.FoldPiece
import Submission.Work.FoldInst.copies_meet
import Submission.Work.FoldInst.fold_theta_coord
import Submission.Work.FoldInst.fold_theta_orthant
import Submission.Work.FoldInst.fold_cover_sides
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.CertFlip
import Submission.Work.FoldInst.fold_state_flipSet
import Submission.Work.FoldInst.Dvor_disjoint
import Submission.Work.FoldInst.Ksub_eq_wallSum
import Submission.Work.FoldInst.actX_image_Dvor
import Submission.Work.FoldInst.foldTheta_flip
import Submission.Work.FoldInst.foldTheta_injOn
import Submission.Work.FoldInst.fold_chart_of_glued
import Submission.Work.FoldInst.foldPsi_eq
import Submission.Work.FoldInst.foldPsi_hagree
import Submission.Work.FoldInst.foldPsi_hcross
import Submission.Work.FoldInst.foldPsi_continuousOn
import Submission.Work.FoldInst.isOpen_foldTheta_image
import Submission.Work.FoldInst.htarget_open
import Submission.Work.FoldInst.foldPhi_mk
import Submission.Work.FoldInst.foldPhi_continuousOn
import Submission.Work.FoldInst.exists_foldChart
import Submission.Work.FoldInst.CoverData
import Submission.Work.FoldInst.Cover
import Submission.Work.FoldInst.Qbar_of_mem_VoronoiOpen_root
import Submission.Work.FoldInst.foldPsi_image_reflVec
import Submission.Work.FoldInst.FoldInvDefs
import Submission.Work.FoldInst.foldInv_foldTheta
import Submission.Work.FoldInst.continuousOn_foldInv
import Submission.Work.FoldInst.exists_pos_le_foldTheta_height
import Submission.Work.FoldInst.FoldChart
import Submission.Work.RTOwed.cuspWallTableCerts
import Submission.Work.RTOwed.mobius_reflWall_high
import Submission.Work.RTOwed.cubeOf_halfopen
import Submission.Work.RTOwed.wallLo_slack_sign
import Submission.Work.RTOwed.cuspCert.CuspSupport
import Submission.Work.RTOwed.cuspCert.lattice_bridge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Set Topology Function Matrix
open scoped Matrix RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 4000000

/-- The cusp lattice divisors are positive. -/
theorem latMod_posZ : ∀ (v : Fin 5) (i : Fin 3), 0 < (Work.Cusp.latMod v i : ℤ) := by decide +kernel

/-! ## The near-region evaluation of the fold chart

If `q` is a point of the *half-open* cell of the cube `a` at the offset `k`, whose chart point lies
in the fold piece `Dvor i r`, and whose height sits between `11/10` and the ceiling of the cell,
then the fold chart of `mbarLow v` is the single Möbius map `cellMat v i r a k`. -/

theorem near_eval (v : Fin 5) (i : Fin 98) (r : Fin (Work.FoldInst.foldCodim i) → Bool)
    (a : Fin 48) (k : Fin 3 → ℤ) (hcusp : Cusp.cubeCusp a = v)
    (hbit : cubeBit a = Work.FoldInst.foldCr i r) {q : CuspE4}
    (hquad : uhsXj q - cuspCert.lamV v k ∈ cuspCert.halfopenBox a)
    (hs1 : 11 / 10 ≤ q 3) (hs2 : q 3 ≤ ceilH a (uhsXj q - cuspCert.lamV v k))
    (hVor : chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3))
      ∈ Work.FoldInst.VoronoiOpen i r) :
    Work.FoldInst.foldChart i (mbarLow v q) = Work.HypModel.mobius (cellMat v i r a k) q := by
  have hbox : uhsXj q - cuspCert.lamV v k ∈ cubeBox a :=
    cuspCert.halfopenBox_subset_cubeBox a hquad
  have hmem : chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)) ∈ Work.FoldInst.Qbar :=
    chartKlein_mem a hbox hs1 hs2
  have hlow : mbarLow v q = Work.FoldInst.mk
      (xbarOf a (chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3))) hmem) :=
    mbarLow_eq_cellX v a k hcusp hbox hs1 hs2
  have hD : xbarOf a (chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3))) hmem
      ∈ Work.FoldInst.Dvor i r := by
    refine ⟨?_, ?_⟩
    · show cubeBit a = Work.FoldInst.foldCr i r
      exact hbit
    · show chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)) ∈ Work.FoldInst.VoronoiOpen i r
      exact hVor
  rw [hlow, Work.FoldInst.foldChart_apply i r _ hD]
  exact foldTheta_chartKlein_eq_mobius v i r a k q (by linarith)

/-! ## The equivariance law of the fold chart under the identification group

If `x` is a lift of a class of the source of `foldChart i`, then acting on the class by the group
element `wallSum i Δ` multiplies the chart value by the coordinate reflection `reflCoords Δ`. -/

theorem foldChart_actX (i : Fin 98) {x : Work.FoldInst.Xbar}
    (hx : x ∈ ⋃ r : Fin (Work.FoldInst.foldCodim i) → Bool, Work.FoldInst.Dvor i r)
    (Δ : Finset (Fin (Work.FoldInst.foldCodim i))) :
    Work.FoldInst.foldChart i (Work.FoldInst.mk (Work.FoldInst.actX (Work.FoldInst.wallSum i Δ) x))
      = Work.FoldInst.reflCoords Δ (Work.FoldInst.foldChart i (Work.FoldInst.mk x)) := by
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
  have hD : Work.FoldInst.actX (Work.FoldInst.wallSum i Δ) x
      ∈ Work.FoldInst.Dvor i (Work.FoldInst.flipSet r Δ) := by
    rw [← Work.FoldInst.actX_image_Dvor i r Δ]
    exact ⟨x, hr, rfl⟩
  rw [Work.FoldInst.foldChart_apply i (Work.FoldInst.flipSet r Δ) _ hD,
    Work.FoldInst.foldChart_apply i r x hr]
  exact Work.FoldInst.foldTheta_flip i r Δ x.2.1

/-! ## The finite bookkeeping of a wall crossing -/

/-- The cube of the cell one wall further in the direction `m`. -/
theorem cubeOfMod_sub_one (a : Fin 48) (ε : Fin 3 → Fin 2) (m : Fin 3) :
    Work.Cusp.cubeOfMod (Work.Cusp.cubeCusp a)
        (fun j => Work.Cusp.cubeCorner a j - (ε j : ℤ) - (if j = m then 1 else 0))
      = wallNb (Work.Cusp.cubeOfMod (Work.Cusp.cubeCusp a)
          (fun j => Work.Cusp.cubeCorner a j - (ε j : ℤ))) m 0 := by
  revert a ε m; decide +kernel

/-- The floor shift by `-e_m` selects the far cube. -/
theorem cubeOfMod_corner_sub_one (a : Fin 48) (m : Fin 3) :
    Work.Cusp.cubeOfMod (Work.Cusp.cubeCusp a)
        (fun j => Work.Cusp.cubeCorner a j - (if j = m then 1 else 0)) = wallNb a m 0 := by
  revert a m; decide +kernel

/-- The pinned coordinates of `q`: the reduced coordinate sits on the corresponding wall. -/
def wallPinSet (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (q : CuspE4) : Finset (Fin 3) :=
  Finset.univ.filter (fun m => (uhsXj q - cuspCert.lamV v k) m = (Work.Cusp.cubeCorner a m : ℝ))

theorem mem_wallPinSet {v : Fin 5} {a : Fin 48} {k : Fin 3 → ℤ} {q : CuspE4} {m : Fin 3} :
    m ∈ wallPinSet v a k q ↔ (uhsXj q - cuspCert.lamV v k) m = (Work.Cusp.cubeCorner a m : ℝ) := by
  rw [wallPinSet, Finset.mem_filter]
  simp

/-- The floor vector of the walk at the crossing set `S`. -/
def walkFloor (q : CuspE4) (S : Finset (Fin 3)) : Fin 3 → ℤ :=
  fun j => ⌊(uhsXj q) j⌋ - (if j ∈ S then 1 else 0)

/-- The cube of the walk at the crossing set `S`. -/
def walkCube (v : Fin 5) (q : CuspE4) (S : Finset (Fin 3)) : Fin 48 :=
  Work.Cusp.cubeOfMod v (walkFloor q S)

/-- The offset of the walk at the crossing set `S`. -/
def walkK (v : Fin 5) (q : CuspE4) (S : Finset (Fin 3)) : Fin 3 → ℤ :=
  fun j => (walkFloor q S j - (Work.Cusp.cubeCorner (walkCube v q S) j)) / (Work.Cusp.latMod v j : ℤ)

/-- The coordinate `j` of the walk's lattice vector. -/
theorem walkK_coord (v : Fin 5) (q : CuspE4) (S : Finset (Fin 3)) (j : Fin 3) :
    (cuspCert.lamV v (walkK v q S)) j
      = ((walkFloor q S j - (Work.Cusp.cubeCorner (walkCube v q S) j) : ℤ) : ℝ) := by
  have hdvd : (Work.Cusp.latMod v j : ℤ) ∣ (walkFloor q S j - Work.Cusp.cubeCorner (walkCube v q S) j) :=
    cuspCert.cubeOfMod_corner_dvd v (walkFloor q S) j
  simp only [cuspCert.lamV, cuspCert.lamK, PiLp.toLp_apply, walkK]
  rw [Int.mul_ediv_cancel' hdvd]

/-- The floor coordinate of `q` in terms of the walk's cell in the direction `m`. -/
theorem walkFloor_eq (v : Fin 5) (q : CuspE4) (S : Finset (Fin 3)) (m : Fin 3) :
    (⌊(uhsXj q) m⌋ : ℝ) = (Work.Cusp.cubeCorner (walkCube v q S) m : ℝ)
      + (cuspCert.lamV v (walkK v q S)) m + (if m ∈ S then 1 else 0) := by
  rw [walkK_coord v q S m, walkFloor]
  push_cast
  ring_nf

/-- **The frame formula of the walk.**  The offset of any point `y` from the corner of the cell of
the crossing set `S` is the fractional part of `uhsXj q` plus the indicator of `S`. -/
theorem walk_frame (v : Fin 5) (q : CuspE4) (S : Finset (Fin 3)) (y : CuspE4) (j : Fin 3) :
    (uhsXj y - cuspCert.lamV v (walkK v q S)) j - (Work.Cusp.cubeCorner (walkCube v q S) j : ℝ)
      = ((uhsXj y) j - (⌊(uhsXj q) j⌋ : ℝ)) + (if j ∈ S then 1 else 0) := by
  rw [PiLp.sub_apply, walkK_coord v q S j, walkFloor]
  push_cast
  ring

/-- The wall reflection of the walk in the direction `m`, at the wall of the cell of the crossing
set `S` (the centre is `floor (uhsXj q m) - 1/2`, which is independent of `S`). -/
def wallRefl (q : CuspE4) (m : Fin 3) (y : CuspE4) : CuspE4 :=
  reflWall4 m ((⌊(uhsXj q) m⌋ : ℝ) - 1 / 2) y

@[simp] theorem wallRefl_three (q : CuspE4) (m : Fin 3) (y : CuspE4) : (wallRefl q m y) 3 = y 3 :=
  reflWall4_three m _ y

/-- In the frame of the cell of `S` (for `m ∉ S`), the wall reflection is the reflection of the
frame coordinate in the cell wall `u m = cubeCorner (walkCube v q S) m`. -/
theorem uhsXj_wallRefl {v : Fin 5} {q : CuspE4} {S : Finset (Fin 3)} {m : Fin 3} (hmS : m ∉ S)
    (y : CuspE4) :
    uhsXj (wallRefl q m y) - cuspCert.lamV v (walkK v q S)
      = reflWall m (Work.Cusp.cubeCorner (walkCube v q S) m)
          (uhsXj y - cuspCert.lamV v (walkK v q S)) := by
  rw [wallRefl, uhsXj_reflWall4]
  apply PiLp.ext
  intro j
  show (reflWall m (((⌊(uhsXj q) m⌋ : ℝ) - 1 / 2) + 1 / 2) (uhsXj y)
        - cuspCert.lamV v (walkK v q S)) j
    = (reflWall m ((Work.Cusp.cubeCorner (walkCube v q S) m : ℝ))
        (uhsXj y - cuspCert.lamV v (walkK v q S))) j
  rw [PiLp.sub_apply, reflWall_apply, reflWall_apply]
  by_cases hj : j = m
  · rw [hj] at *
    rw [ite_eq_left rfl, ite_eq_left rfl]
    simp only [PiLp.sub_apply]
    have hc : ((⌊(uhsXj q) m⌋ : ℝ) - 1 / 2) + 1 / 2
        = (Work.Cusp.cubeCorner (walkCube v q S) m : ℝ)
          + (cuspCert.lamV v (walkK v q S)) m := by
      have h := walkFloor_eq v q S m
      rw [ite_eq_right hmS] at h
      linarith
    rw [hc]
    ring
  · rw [ite_eq_right hj, ite_eq_right hj]
    simp only [PiLp.sub_apply]

/-! ### The cells of the walk

The cell of the crossing set `S` is the cell of the cube `walkCube v q S`; crossing the wall in the
direction `m` (for `m ∉ S`) gives the cell of `S ∪ {m}`, whose cube is the far cube of the first. -/

/-- The cells of the walk are the iterated far cubes. -/
theorem walkCube_insert (v : Fin 5) (q : CuspE4) (S : Finset (Fin 3)) {m : Fin 3} (hm : m ∉ S) :
    walkCube v q (insert m S) = wallNb (walkCube v q S) m 0 := by
  have hfloor : walkFloor q (insert m S)
      = fun j => walkFloor q S j - (if j = m then 1 else 0) := by
    funext j
    simp only [walkFloor]
    have hif : (if j ∈ insert m S then (1 : ℤ) else 0)
        = (if j ∈ S then 1 else 0) + (if j = m then 1 else 0) := by
      by_cases hj : j = m
      · subst hj
        rw [if_pos (Finset.mem_insert_self _ _), if_pos rfl, if_neg hm]
        norm_num
      · by_cases hjS : j ∈ S
        · rw [if_pos (Finset.mem_insert_of_mem hjS), if_pos hjS, if_neg hj]
          norm_num
        · rw [if_neg (fun h => (Finset.mem_insert.mp h).elim hj hjS), if_neg hjS, if_neg hj]
          norm_num
    rw [hif]
    ring
  have hlat : ∀ j : Fin 3, walkFloor q S j
      = (Work.Cusp.cubeCorner (walkCube v q S) j : ℤ) + cuspCert.lamK v (walkK v q S) j := by
    intro j
    have h := walkK_coord v q S j
    rw [cuspCert.lamV, PiLp.toLp_apply] at h
    simp only [cuspCert.lamK]
    have h2 : (((Work.Cusp.latMod v j : ℤ) * walkK v q S j : ℤ) : ℝ)
        = ((walkFloor q S j - Work.Cusp.cubeCorner (walkCube v q S) j : ℤ) : ℝ) := h
    have h3 : (Work.Cusp.latMod v j : ℤ) * walkK v q S j
        = walkFloor q S j - Work.Cusp.cubeCorner (walkCube v q S) j := by
      exact_mod_cast h2
    linarith [h3]
  have hzero : ∀ j : Fin 3, ((fun _ : Fin 3 => (0 : Fin 2)) j : ℤ) = 0 := fun j => rfl
  have hsplit : walkFloor q (insert m S)
      = fun j => (Work.Cusp.cubeCorner (walkCube v q S) j
            - (if j = m then 1 else 0))
          + (Work.Cusp.latMod v j : ℤ) * (walkK v q S) j := by
    rw [hfloor]
    funext j
    rw [hlat j]
    simp only [cuspCert.lamK]
    ring
  calc walkCube v q (insert m S)
      = Work.Cusp.cubeOfMod v (fun j => (Work.Cusp.cubeCorner (walkCube v q S) j
            - (if j = m then 1 else 0))
          + (Work.Cusp.latMod v j : ℤ) * (walkK v q S) j) := by
        rw [walkCube, hsplit]
    _ = Work.Cusp.cubeOfMod (Work.Cusp.cubeCusp (walkCube v q S))
          (fun j => (Work.Cusp.cubeCorner (walkCube v q S) j
            - (if j = m then 1 else 0))) := by
        rw [cuspCert.cubeOfMod_add_latMod]
        congr 1
        exact (cuspCert.cubeCusp_cubeOfMod v _).symm
    _ = wallNb (walkCube v q S) m 0 := cubeOfMod_corner_sub_one (walkCube v q S) m

/-- The walk's cube at the empty crossing set is the base cube. -/
theorem walkCube_eq_base (v : Fin 5) (a : Fin 48) (q : CuspE4)
    (hca : a = Work.Cusp.cubeOfMod v (fun j => ⌊(uhsXj q) j⌋)) :
    walkCube v q ∅ = a := by
  rw [walkCube, hca]
  congr 1
  funext j
  simp [walkFloor]

/-- The type of the wall in the direction `m` is preserved along the walk. -/
theorem wallLo_walkCube_type (v : Fin 5) (q : CuspE4) (S : Finset (Fin 3)) {m : Fin 3}
    (hm : m ∉ S) :
    Work.FoldInst.sideType (wallLo (walkCube v q S) m)
      = Work.FoldInst.sideType (wallLo (walkCube v q ∅) m) := by
  induction S using Finset.induction_on generalizing m with
  | empty => rfl
  | insert i S' hi ih =>
      have him : i ≠ m := by
        intro h
        exact hm (h ▸ Finset.mem_insert_self i S')
      have hmS' : m ∉ S' := fun h => hm (Finset.mem_insert_of_mem h)
      have hstep : Work.FoldInst.sideType (wallLo (wallNb (walkCube v q S') i 0) m)
          = Work.FoldInst.sideType (wallLo (walkCube v q S') m) := by
        have hcert := cuspWallTableCerts.2.2.2.2.1 (walkCube v q S') i 0 m 0
        rw [if_neg (fun h : m = i => him h.symm), if_pos rfl, if_pos rfl] at hcert
        exact hcert
      rw [walkCube_insert v q S' hi, hstep]
      exact ih hmS'


/-! ### The one-step unfolding

Crossing a wall of the current cell of the walk replaces the fold chart value by the coordinate
reflection of the value at the reflected point.  The group element of the crossing is the wall
element `wallGam` of the cell, which by the type matching of `wallLo_walkCube_type` and the
hypothesis `ht` is the wall sum `wallSum i {t}` of the base wall index `t`; the equivariance law
`foldChart_actX` then produces the reflection `reflCoords {t}`. -/

/-- The offset of the walk's `S ∪ {m}`-cell is the offset of the `S`-cell plus the wall vector. -/
theorem walkK_insert_sub (v : Fin 5) (q : CuspE4) (S : Finset (Fin 3)) {m : Fin 3} (hm : m ∉ S)
    (k₀ : Fin 3 → ℤ) (hk₀ : cuspCert.lamV v k₀ = wallLamV (walkCube v q S) m 0) :
    walkK v q (insert m S) = walkK v q S + k₀ := by
  -- the corner relations across the wall, over `ℤ`
  have hcornerm : Work.Cusp.cubeCorner (wallNb (walkCube v q S) m 0) m
      + wallLam (walkCube v q S) m 0 m + 1 = Work.Cusp.cubeCorner (walkCube v q S) m := by
    have h := cuspWallTableCerts.2.2.1 (walkCube v q S) m 0
    simp only [cuspWall_wallLamV_apply] at h
    rw [if_true, if_true, add_zero] at h
    have h' : ((Work.Cusp.cubeCorner (wallNb (walkCube v q S) m 0) m
        + wallLam (walkCube v q S) m 0 m + 1 : ℤ) : ℝ)
        = ((Work.Cusp.cubeCorner (walkCube v q S) m : ℤ) : ℝ) := by simpa using h
    exact_mod_cast h'
  have hcornert : ∀ j : Fin 3, j ≠ m →
      Work.Cusp.cubeCorner (wallNb (walkCube v q S) m 0) j
        + wallLam (walkCube v q S) m 0 j = Work.Cusp.cubeCorner (walkCube v q S) j := by
    intro j hj
    have h := cuspWallTableCerts.2.2.2.1 (walkCube v q S) m 0 j hj
    simp only [cuspWall_wallLamV_apply] at h
    have h' : ((Work.Cusp.cubeCorner (wallNb (walkCube v q S) m 0) j
        + wallLam (walkCube v q S) m 0 j : ℤ) : ℝ)
        = ((Work.Cusp.cubeCorner (walkCube v q S) j : ℤ) : ℝ) := by simpa using h
    exact_mod_cast h'
  -- the floor identity
  have hfl : ∀ j : Fin 3, walkFloor q (insert m S) j
      = walkFloor q S j - (if j = m then 1 else 0) := by
    intro j
    simp only [walkFloor]
    by_cases hj : j = m
    · subst hj
      rw [if_pos (Finset.mem_insert_self _ _), if_neg hm, if_pos rfl]
      ring
    · rw [show (if j ∈ insert m S then (1 : ℤ) else 0) = (if j ∈ S then 1 else 0) from by
        by_cases hjS : j ∈ S <;> simp [Finset.mem_insert, hj, hjS]]
      rw [if_neg hj]
      ring
  have h1 : ∀ j : Fin 3, (cuspCert.lamV v (walkK v q (insert m S))) j
      = (cuspCert.lamV v (walkK v q S)) j + (wallLamV (walkCube v q S) m 0) j := by
    intro j
    rw [walkK_coord, walkK_coord, cuspWall_wallLamV_apply,
      show Work.Cusp.cubeCorner (walkCube v q (insert m S)) j
        = Work.Cusp.cubeCorner (wallNb (walkCube v q S) m 0) j from by
          rw [walkCube_insert v q S hm],
      hfl j]
    push_cast
    by_cases hj : j = m
    · subst hj
      rw [if_pos rfl]
      push_cast
      have hc := congrArg (fun z : ℤ => (z : ℝ)) hcornerm
      push_cast at hc
      linarith [hc]
    · rw [if_neg hj]
      push_cast
      have hc := congrArg (fun z : ℤ => (z : ℝ)) (hcornert j hj)
      push_cast at hc
      linarith [hc]
  have h2 : cuspCert.lamV v (walkK v q (insert m S))
      = cuspCert.lamV v (walkK v q S) + cuspCert.lamV v k₀ := by
    rw [hk₀]
    apply PiLp.ext
    intro j
    exact h1 j
  have h3 : cuspCert.lamV v (walkK v q S + k₀)
      = cuspCert.lamV v (walkK v q S) + cuspCert.lamV v k₀ := cuspWall_lamV_add v _ _
  have hinj : ∀ k k' : Fin 3 → ℤ, cuspCert.lamV v k = cuspCert.lamV v k' → k = k' := by
    intro k k' h
    funext j
    have hj : (((Work.Cusp.latMod v j : ℤ) * k j : ℤ) : ℝ)
        = (((Work.Cusp.latMod v j : ℤ) * k' j : ℤ) : ℝ) := by
      have := congrArg (fun z : CuspE3 => z j) h
      simpa only [cuspCert.lamV, cuspCert.lamK, PiLp.toLp_apply] using this
    have hmod : 0 < (Work.Cusp.latMod v j : ℤ) := latMod_posZ v j
    have h3 : (Work.Cusp.latMod v j : ℤ) * k j = (Work.Cusp.latMod v j : ℤ) * k' j := by
      exact_mod_cast hj
    exact mul_left_cancel₀ (ne_of_gt hmod) h3
  exact hinj _ _ (by rw [h3]; exact h2)


/-! ## The canonical lift of a point in the cell `(a,k)`
`cellLift v a k x` is the point of `X̄` over the cube `a` whose Klein coordinates are the chart of
the cell coordinate `uhsXj x - lamV v k` at the height `x 3`; it is the junk value `(0, 0)` if that
chart point is not in `Q̄`.  Working with this conditional function (rather than with `xbarOf`
applied to an explicit membership proof) keeps the statements free of proof arguments. -/

def cellLift (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (x : CuspE4) : CuspXbar := by
  classical
  exact if h : chartKlein a (mkE4 (uhsXj x - cuspCert.lamV v k) (x 3)) ∈ Work.FoldInst.Qbar
    then xbarOf a (chartKlein a (mkE4 (uhsXj x - cuspCert.lamV v k) (x 3))) h
    else (0, ⟨0, zero_mem_Qbar⟩)

theorem cellLift_eq {v : Fin 5} {a : Fin 48} {k : Fin 3 → ℤ} {x : CuspE4}
    (h : chartKlein a (mkE4 (uhsXj x - cuspCert.lamV v k) (x 3)) ∈ Work.FoldInst.Qbar) :
    cellLift v a k x
      = xbarOf a (chartKlein a (mkE4 (uhsXj x - cuspCert.lamV v k) (x 3))) h := by
  rw [cellLift, dif_pos h]

theorem cellLift_fst {v : Fin 5} {a : Fin 48} {k : Fin 3 → ℤ} {x : CuspE4}
    (h : chartKlein a (mkE4 (uhsXj x - cuspCert.lamV v k) (x 3)) ∈ Work.FoldInst.Qbar) :
    (cellLift v a k x).1 = cubeBit a := by
  rw [cellLift_eq h]
  rfl

/-- **The cell identity in lift form**: on a cell of the cusp chart, `mbarLow v` is the class of the
canonical lift. -/
theorem mbarLow_eq_cellLift (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (hcusp : Cusp.cubeCusp a = v)
    {q : CuspE4} (hbox : uhsXj q - cuspCert.lamV v k ∈ cubeBox a) (hs1 : 11 / 10 ≤ q 3)
    (hs2 : q 3 ≤ ceilH a (uhsXj q - cuspCert.lamV v k)) :
    mbarLow v q = Work.FoldInst.mk (cellLift v a k q) := by
  rw [cellLift_eq (chartKlein_mem a hbox hs1 hs2)]
  exact mbarLow_eq_cellX v a k hcusp hbox hs1 hs2

/-- The base cell of the walk is the canonical cell of `q`. -/
theorem walkFloor_empty (v : Fin 5) (q : CuspE4) :
    walkFloor q ∅ = Work.RTOwed.floorV (uhsXj q) := by
  funext j
  simp only [walkFloor, Work.RTOwed.floorV]
  rw [if_neg (Finset.notMem_empty j)]
  ring

theorem walkCube_empty (v : Fin 5) (q : CuspE4) :
    walkCube v q ∅ = Work.RTOwed.cubeOf v (uhsXj q) := by
  rw [walkCube, walkFloor_empty v q]
  rfl

theorem walkK_empty (v : Fin 5) (q : CuspE4) :
    walkK v q ∅ = cuspCert.floorK v (uhsXj q) := by
  funext j
  simp only [walkK, cuspCert.floorK]
  rw [walkFloor_empty v q, walkCube_empty v q]

/-- The pinned coordinates are exactly the coordinates at which `q` sits on the lower wall of its
canonical cell. -/
theorem mem_wallPinSet_iff_delta {v : Fin 5} {q : CuspE4} {m : Fin 3} :
    m ∈ wallPinSet v (walkCube v q ∅) (walkK v q ∅) q
      ↔ (uhsXj q) m = (⌊(uhsXj q) m⌋ : ℝ) := by
  rw [mem_wallPinSet]
  have h2 := walkFloor_eq v q ∅ m
  rw [if_neg (Finset.notMem_empty m), add_zero] at h2
  simp only [PiLp.sub_apply]
  constructor <;> intro h <;> linarith

/-- A lift of a class of `foldChart i` lies in a Voronoi piece of the class. -/
theorem mem_iUnion_Dvor_of_mem_source {i : Fin 98} {z : CuspXbar}
    (hz : Work.FoldInst.mk z ∈ (Work.FoldInst.foldChart i).source) :
    z ∈ ⋃ r : Fin (Work.FoldInst.foldCodim i) → Bool, Work.FoldInst.Dvor i r := by
  have h1 : Work.FoldInst.mk z ∈ (⋃ r : Fin (Work.FoldInst.foldCodim i) → Bool,
      Work.FoldInst.mk '' Work.FoldInst.Dvor i r) := by
    rwa [← Work.FoldInst.foldChart_source i]
  have h2 : z ∈ Work.FoldInst.mk ⁻¹' (⋃ r : Fin (Work.FoldInst.foldCodim i) → Bool,
      Work.FoldInst.mk '' Work.FoldInst.Dvor i r) := h1
  rwa [(Work.FoldInst.fold_source_open_dvor i).2] at h2

end

end Work.RTOwed
