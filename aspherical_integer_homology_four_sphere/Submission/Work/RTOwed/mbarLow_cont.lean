import Mathlib
import Submission.Work.RTOwed.cuspChartBeta
import Submission.Work.RTOwed.cuspChartRegion
import Submission.Work.RTOwed.cuspChart
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.TopBox
import Submission.Work.RTOwed.cuspCert.mbarPt_continuous
import Submission.Work.RTOwed.chartKlein_wall
import Submission.Work.RTOwed.cuspCertWalls
import Submission.Work.RTOwed.cuspChartWalls
import Submission.Work.RTOwed.chartKlein_continuousOn
import Submission.Work.RTOwed.sideSlack_wallHi_chartKlein
import Submission.Work.RTOwed.wallNb_upper
import Submission.Work.RTOwed.wallGam_sideType

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Set Topology Function
open scoped BigOperators

noncomputable section

/-! ## The preimage cells of the cusp lattice in `E4` -/

/-- The `E4`-preimage of a cell of the cusp lattice (`Work.RTOwed.cuspCert.cell`): the points whose
*cube* coordinate `uhsXj q` lies in the translate `cubeBox a + lamV v k`.  These are the unit boxes
`[m, m+1]` of the lattice, indexed by the residue class of their floor `m = cubeCorner a + lamV v k`;
they are closed, locally finite and cover `E4`. -/
def cellPre (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) : Set CuspE4 :=
  {q | uhsXj q ∈ cuspCert.cell v a k}

theorem mem_cellPre {v : Fin 5} {a : Fin 48} {k : Fin 3 → ℤ} {q : CuspE4} :
    q ∈ cellPre v a k ↔ uhsXj q - cuspCert.lamV v k ∈ cubeBox a := Iff.rfl

theorem continuous_uhsXj : Continuous (uhsXj : CuspE4 → CuspE3) := by
  unfold uhsXj xOf4
  fun_prop

theorem isClosed_cellPre (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) :
    IsClosed (cellPre v a k) :=
  (cuspCert.isClosed_cell v a k).preimage continuous_uhsXj

theorem locallyFinite_cellPre (v : Fin 5) :
    LocallyFinite (fun p : cuspCert.CIdx v => cellPre v p.1.1 p.2) :=
  (cuspCert.locallyFinite_cells v).preimage_continuous continuous_uhsXj

theorem iUnion_cellPre (v : Fin 5) :
    (⋃ p : cuspCert.CIdx v, cellPre v p.1.1 p.2) = univ := by
  ext q
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨a, k, hca, hx⟩ := cuspCert.exists_cell v (uhsXj q)
  exact ⟨(⟨a, hca⟩, k), hx⟩

/-- The component form of the cell membership: `q ∈ cellPre v a k` iff the cube coordinate of `q`
lies in the unit box with lower corner `cubeCorner a + lamK v k`. -/
theorem mem_cellPre_iff (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (q : CuspE4) :
    q ∈ cellPre v a k ↔
      ∀ j : Fin 3, (Work.Cusp.cubeCorner a j : ℝ) + (cuspCert.lamK v k j : ℝ) ≤ (uhsXj q) j ∧
        (uhsXj q) j ≤ (Work.Cusp.cubeCorner a j : ℝ) + (cuspCert.lamK v k j : ℝ) + 1 := by
  constructor
  · intro h j
    have h' := h j
    simp only [cubeBox, Set.mem_ofPred_eq, cuspCert.lamV, PiLp.sub_apply, PiLp.toLp_apply,
      WithLp.ofLp_toLp] at h'
    constructor <;> linarith [h'.1, h'.2]
  · intro h
    intro j
    have h' := h j
    simp only [cubeBox, Set.mem_ofPred_eq, cuspCert.lamV, PiLp.sub_apply, PiLp.toLp_apply,
      WithLp.ofLp_toLp]
    constructor <;> linarith [h'.1, h'.2]

/-! ## The chart of a cube at a cell offset -/

/-- **The point of `X̄` given by the chart of the cube `a` at the offset `k`**: the cube bit of `a`
together with the Klein point of the reduced point `uhsXj q - lamV v k` at the height `q 3`.  The
junk branch (as in `cuspLowPt`) is taken when the chart value is not in `Q̄`; it is never taken where
`q 3` lies below the ceiling of the cell. -/
def mbX (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (q : CuspE4) : CuspXbar := by
  classical
  exact
    if h : chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)) ∈ Work.FoldInst.Qbar then
      xbarOf a (chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3))) h
    else (0, ⟨0, zero_mem_Qbar⟩)

/-- The same as a point of `M̄`. -/
def mbBranch (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (q : CuspE4) : Work.FoldInst.Mbar :=
  Work.FoldInst.mk (mbX v a k q)

theorem mbX_eq (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) {q : CuspE4}
    (h : chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)) ∈ Work.FoldInst.Qbar) :
    mbX v a k q
      = xbarOf a (chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3))) h := by
  unfold mbX
  rw [dif_pos h]

theorem mbBranch_eq (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) {q : CuspE4}
    (h : chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)) ∈ Work.FoldInst.Qbar) :
    mbBranch v a k q
      = Work.FoldInst.mk (xbarOf a
          (chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3))) h) := by
  unfold mbBranch
  rw [mbX_eq v a k h]

/-- **The definition of `mbarLow` is the branch of the cube of the point.**  The junk branch of
`cuspLowPt` is the junk branch of `mbX` for the cube `chartCube v q` and the offset
`floorK v (uhsXj q)`. -/
theorem mbarLow_eq_mbBranch_self (v : Fin 5) (q : CuspE4) :
    mbarLow v q = mbBranch v (chartCube v q) (cuspCert.floorK v (uhsXj q)) q := by
  have hkey : uhsXj q - cuspCert.lamV v (cuspCert.floorK v (uhsXj q)) = redV v (uhsXj q) :=
    cuspCert.sub_lamV_floorK v (uhsXj q) (fun i => cuspCert.floorV_dvd v (uhsXj q) i)
  have hfun : mbX v (chartCube v q) (cuspCert.floorK v (uhsXj q)) q = cuspLowPt v q := by
    unfold mbX cuspLowPt
    rw [hkey]
    simp only [redChart, chartCube, xbarOf]
    try (split_ifs <;> rfl)
  rw [mbBranch, hfun, mbarLow]

/-! ## The cells as the unit boxes of the lattice -/

/-- The cube of the unit box with lower corner `m`. -/
def cb (v : Fin 5) (m : Fin 3 → ℤ) : Fin 48 := Work.Cusp.cubeOfMod v m

/-- The offset of the unit box with lower corner `m` relative to its cube `cb v m`. -/
def kc (v : Fin 5) (m : Fin 3 → ℤ) : Fin 3 → ℤ :=
  fun j => (m j - (Work.Cusp.cubeCorner (cb v m) j : ℤ)) / (Work.Cusp.latMod v j : ℤ)

theorem cb_dvd (v : Fin 5) (m : Fin 3 → ℤ) (j : Fin 3) :
    (Work.Cusp.latMod v j : ℤ) ∣ (m j - (Work.Cusp.cubeCorner (cb v m) j : ℤ)) :=
  cuspCert.cubeOfMod_corner_dvd v m j

theorem lamK_kc (v : Fin 5) (m : Fin 3 → ℤ) (j : Fin 3) :
    (cuspCert.lamK v (kc v m) j : ℝ)
      = (m j : ℝ) - (Work.Cusp.cubeCorner (cb v m) j : ℝ) := by
  have h := Int.mul_ediv_cancel' (cb_dvd v m j)
  simp only [cuspCert.lamK, kc]
  rw [h]
  push_cast
  ring

/-- **The cell of the floor `m` is the unit box `[m, m+1]`.** -/
theorem cellPre_cb_kc (v : Fin 5) (m : Fin 3 → ℤ) :
    cellPre v (cb v m) (kc v m)
      = {q : CuspE4 | ∀ j : Fin 3, (m j : ℝ) ≤ (uhsXj q) j ∧ (uhsXj q) j ≤ (m j : ℝ) + 1} := by
  ext q
  rw [mem_cellPre_iff]
  constructor
  · intro h j
    have h' := h j
    rw [lamK_kc] at h'
    constructor <;> linarith [h'.1, h'.2]
  · intro h j
    have h' := h j
    rw [lamK_kc]
    constructor <;> linarith [h'.1, h'.2]

/-- The branch of the unit box with lower corner `m`. -/
def mbFloor (v : Fin 5) (m : Fin 3 → ℤ) : CuspE4 → Work.FoldInst.Mbar :=
  mbBranch v (cb v m) (kc v m)

/-- **`mbarLow` is the branch of the canonical cell** (the one whose floor is `floorV (uhsXj q)`). -/
theorem mbarLow_eq_mbFloor_self (v : Fin 5) (q : CuspE4) :
    mbarLow v q = mbFloor v (floorV (uhsXj q)) q := by
  rw [mbarLow_eq_mbBranch_self v q]
  rfl

/-! ## Continuity of a branch -/

/-- The Möbius numerator `MV a (mkE4 x s)` is the normalised chart vector `chartVec a x s`. -/
theorem MV_mkE4 (a : Fin 48) (x : CuspE3) (s : ℝ) :
    MV a (mkE4 x s) = (2 * s)⁻¹ • Work.RTOwed.chartKleinMem.chartVec a x s := by
  simp only [MV, Work.RTOwed.chartKleinMem.chartVec, Work.RTOwed.chartKleinMem.chartMatR,
    Work.RTOwed.chartKleinMem.hypOfUHS_mkE4, Matrix.mulVec_smul]

/-- The fourth coordinate of the Möbius numerator is positive on a cube below its ceiling. -/
theorem MV_mkE4_four_ne (a : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) {s : ℝ}
    (hs : 11 / 10 ≤ s) : MV a (mkE4 x s) 4 ≠ 0 := by
  rw [MV_mkE4, Pi.smul_apply, smul_eq_mul]
  exact mul_ne_zero (inv_ne_zero (by linarith))
    (ne_of_gt (Work.RTOwed.chartKleinMem.chartVec4_pos a hx hs))

/-- The map `q ↦ mkE4 (uhsXj q - lamV v k) (q 3)`. -/
theorem continuous_mkE4_cell (v : Fin 5) (k : Fin 3 → ℤ) :
    Continuous (fun q : CuspE4 => mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)) := by
  have hW : Continuous (fun q : CuspE4 => uhsXj q - cuspCert.lamV v k) :=
    continuous_uhsXj.sub continuous_const
  refine ((PiLp.homeomorph 2 (fun _ : Fin 4 => ℝ)).comp_continuous_iff).mp ?_
  show Continuous (fun q : CuspE4 => fun i : Fin 4 =>
    mkE4 (uhsXj q - cuspCert.lamV v k) (q 3) i)
  refine continuous_pi (fun i => ?_)
  fin_cases i
  · exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).comp hW
  · exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1).comp hW
  · exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).comp hW
  · exact PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 3

/-- **The chart of a cube is continuous on a cell below its ceiling.** -/
theorem continuousOn_chartKlein_cell (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) :
    ContinuousOn
      (fun q : CuspE4 => chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)))
      (cellPre v a k ∩ {q : CuspE4 | 11 / 10 ≤ q 3}) := by
  refine (chartKlein_continuousOn a).comp (continuous_mkE4_cell v k).continuousOn ?_
  rintro q ⟨hcell, hs1⟩
  have hs1' : 11 / 10 ≤ q 3 := hs1
  refine ⟨?_, MV_mkE4_four_ne a (by simpa [mem_cellPre] using hcell) hs1'⟩
  rw [mkE4_three]
  linarith

/-- **The branch of a cell is continuous on the part of the cell below its ceiling.** -/
theorem continuousOn_mbBranch (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) :
    ContinuousOn (mbBranch v a k)
      {q : CuspE4 | q ∈ cellPre v a k ∧ 11 / 10 ≤ q 3 ∧
        q 3 ≤ ceilH a (uhsXj q - cuspCert.lamV v k)} := by
  classical
  set S : Set CuspE4 := {q : CuspE4 | q ∈ cellPre v a k ∧ 11 / 10 ≤ q 3 ∧
    q 3 ≤ ceilH a (uhsXj q - cuspCert.lamV v k)} with hS
  have hφ : ContinuousOn
      (fun q : CuspE4 => chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3))) S :=
    (continuousOn_chartKlein_cell v a k).mono
      (fun q hq => ⟨hq.1, hq.2.1⟩)
  have hmem : ∀ q : CuspE4, q ∈ S →
      chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)) ∈ Work.FoldInst.Qbar :=
    fun q hq => chartKlein_mem a (by simpa [mem_cellPre] using hq.1) hq.2.1 hq.2.2
  have hnice : Continuous (fun q : S => (cubeBit a,
      (⟨chartKlein a (mkE4 (uhsXj q.1 - cuspCert.lamV v k) (q.1 3)), hmem q.1 q.2⟩ :
        Work.FoldInst.Qbar))) := by
    refine Continuous.prodMk continuous_const ?_
    exact Continuous.subtype_mk (hφ.domRestrict) _
  have hnice' : Continuous (fun q : S => Work.FoldInst.mk (cubeBit a,
      (⟨chartKlein a (mkE4 (uhsXj q.1 - cuspCert.lamV v k) (q.1 3)), hmem q.1 q.2⟩ :
        Work.FoldInst.Qbar))) :=
    (continuous_quotient_mk').comp hnice
  rw [continuousOn_iff_continuous_domRestrict]
  refine hnice'.congr (fun q => ?_)
  exact (mbBranch_eq v a k (hmem q.1 q.2)).symm

/-! ## The ceiling of a translated cube -/

/-- **The ceiling is invariant under a lattice translation of the cube**: for `y` in the cube `a`
whose translate `y - lamV v k` lies in the cube `b`, the two ceilings agree (they are both
`β (· - cuspH)` and the arguments differ by the integer vector `lamV v k`). -/
theorem ceilH_sub_lamV (v : Fin 5) (a b : Fin 48) (k : Fin 3 → ℤ) {y : CuspE3}
    (hya : y ∈ cubeBox a) (hyb : y - cuspCert.lamV v k ∈ cubeBox b) :
    ceilH a y = ceilH b (y - cuspCert.lamV v k) := by
  have h1 : ceilH a y = Work.Cusp.beta (y - cuspH) := by
    have h := ceilH_eq_beta a (y := y - cuspH) (by rw [sub_add_cancel]; exact hya)
    rwa [sub_add_cancel] at h
  have h2 : ceilH b (y - cuspCert.lamV v k)
      = Work.Cusp.beta ((y - cuspCert.lamV v k) - cuspH) := by
    have h := ceilH_eq_beta b (y := (y - cuspCert.lamV v k) - cuspH)
      (by rw [sub_add_cancel]; exact hyb)
    rwa [sub_add_cancel] at h
  have h3 : (y - cuspCert.lamV v k) - cuspH
      = (y - cuspH) + Work.Cusp.ofInt3 (fun i => -(cuspCert.lamK v k i)) := by
    apply PiLp.ext; intro i
    fin_cases i <;>
      simp only [PiLp.sub_apply, PiLp.add_apply, cuspH, Work.Cusp.ofInt3, cuspCert.lamV,
        cuspCert.lamK, PiLp.toLp_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] <;>
      push_cast <;> ring
  rw [h1, h2, h3]
  exact (Work.Cusp.beta_add_int (y - cuspH) _).symm

/-! ## The floor bookkeeping of the wall step -/

/-- The cube of the unit box with lower corner `cubeCorner a` is `a`. -/
theorem cubeOfMod_corner (a : Fin 48) :
    Work.Cusp.cubeOfMod (Work.Cusp.cubeCusp a) (Work.Cusp.cubeCorner a) = a := by
  revert a
  decide

/-- Cubes of a cusp with corners congruent modulo the lattice divisors coincide. -/
theorem cubeCorner_inj_mod : ∀ (v : Fin 5) (a b : Fin 48), Work.Cusp.cubeCusp a = v →
    Work.Cusp.cubeCusp b = v →
    (∀ i : Fin 3, (Work.Cusp.latMod v i : ℤ) ∣
      Work.Cusp.cubeCorner a i - Work.Cusp.cubeCorner b i) → a = b := by
  decide

/-- `cubeOfMod` depends only on the residues modulo the lattice divisors. -/
theorem cubeOfMod_residue (v : Fin 5) {p p' : Fin 3 → ℤ}
    (h : ∀ i : Fin 3, (Work.Cusp.latMod v i : ℤ) ∣ p i - p' i) :
    Work.Cusp.cubeOfMod v p = Work.Cusp.cubeOfMod v p' := by
  refine cubeCorner_inj_mod v _ _ (cuspCert.cubeCusp_cubeOfMod v p)
    (cuspCert.cubeCusp_cubeOfMod v p') (fun i => ?_)
  have h1 := cuspCert.cubeOfMod_corner_dvd v p i
  have h2 := cuspCert.cubeOfMod_corner_dvd v p' i
  have h3 := h i
  have hsum : (Work.Cusp.latMod v i : ℤ) ∣
      (p i - Work.Cusp.cubeCorner (Work.Cusp.cubeOfMod v p) i)
        - (p' i - Work.Cusp.cubeCorner (Work.Cusp.cubeOfMod v p') i) := dvd_sub h1 h2
  have hkey : Work.Cusp.cubeCorner (Work.Cusp.cubeOfMod v p) i
      - Work.Cusp.cubeCorner (Work.Cusp.cubeOfMod v p') i
      = (p i - p' i) - ((p i - Work.Cusp.cubeCorner (Work.Cusp.cubeOfMod v p) i)
        - (p' i - Work.Cusp.cubeCorner (Work.Cusp.cubeOfMod v p') i)) := by ring
  rw [hkey]
  exact dvd_sub h3 hsum

/-- Raising the `j`-th coordinate of a floor by one. -/
def eFloor (m : Fin 3 → ℤ) (j : Fin 3) : Fin 3 → ℤ := fun l => m l + (if l = j then 1 else 0)

@[simp] theorem eFloor_self (m : Fin 3 → ℤ) (j : Fin 3) : eFloor m j j = m j + 1 := by
  simp [eFloor]

theorem eFloor_of_ne (m : Fin 3 → ℤ) {j l : Fin 3} (h : l ≠ j) : eFloor m j l = m l := by
  simp [eFloor, h]

/-- The cube of the raised floor is the upper wall neighbour of the cube. -/
theorem cb_eFloor (v : Fin 5) (m : Fin 3 → ℤ) (j : Fin 3) :
    cb v (eFloor m j) = wallNb (cb v m) j 1 := by
  have hres : Work.Cusp.cubeOfMod v (eFloor m j)
      = Work.Cusp.cubeOfMod v
        (fun l => Work.Cusp.cubeCorner (cb v m) l + (if l = j then 1 else 0)) := by
    refine cubeOfMod_residue v (fun i => ?_)
    have h := cb_dvd v m i
    have hkey : eFloor m j i - (Work.Cusp.cubeCorner (cb v m) i + (if i = j then 1 else 0))
        = m i - Work.Cusp.cubeCorner (cb v m) i := by
      simp only [eFloor]
      ring
    rw [hkey]
    exact h
  calc cb v (eFloor m j)
      = Work.Cusp.cubeOfMod v
          (fun l => Work.Cusp.cubeCorner (cb v m) l + (if l = j then 1 else 0)) := hres
    _ = Work.Cusp.cubeOfMod (Work.Cusp.cubeCusp (cb v m))
          (fun l => Work.Cusp.cubeCorner (cb v m) l + (if l = j then 1 else 0)) := by
        rw [show cb v m = Work.Cusp.cubeOfMod v m from rfl, cuspCert.cubeCusp_cubeOfMod]
    _ = wallNb (cb v m) j 1 := (wallNb_upper (cb v m) j).1

/-- The lattice offset of the raised floor is the offset of the wall neighbour. -/
theorem lamV_kc_eFloor (v : Fin 5) (m : Fin 3 → ℤ) (j : Fin 3) :
    cuspCert.lamV v (kc v (eFloor m j))
      = cuspCert.lamV v (kc v m) + wallLamV (cb v m) j 1 := by
  apply PiLp.ext; intro i
  simp only [cuspCert.lamV, PiLp.add_apply, PiLp.toLp_apply, wallLamV]
  have h2 := (wallNb_upper (cb v m) j).2 i
  rw [lamK_kc, lamK_kc, cb_eFloor, h2]
  simp only [eFloor]
  push_cast
  ring

/-! ## The wall step of the floor induction -/

/-- The ceiling `β` of the cusp chapter is periodic: it is the ceiling of the unit cube with corner
`⌊x⌋`, so it is invariant under an integer translation of the cube coordinates. -/
private lemma beta_sub_ofInt3 (x : CuspE3) (mm : Fin 3 → ℤ) :
    Work.Cusp.beta (x - Work.Cusp.ofInt3 mm) = Work.Cusp.beta x := by
  have h : (x - Work.Cusp.ofInt3 mm) + Work.Cusp.ofInt3 mm = x := sub_add_cancel _ _
  have h1 := Work.Cusp.beta_add_int (x - Work.Cusp.ofInt3 mm) mm
  rw [h] at h1
  exact h1.symm

/-- **The wall step of the floor induction.**  If the cube coordinate `uhsXj q` of `q` sits on the
upper `j`-face of the unit box of the floor `m` (i.e. `(uhsXj q) j = m j + 1`, so that the `j`-th
coordinate is an integer) and `q` lies in the chimney region `11/10 ≤ q 3 ≤ β (xOf q)`, then the
chart of the box of the floor `m` and the chart of the box of the raised floor `eFloor m j` give the
same point of `M̄`: the identification of the upper wall of the cube.

Route.  Let `a := cb v m`, `k := kc v m`, `a' := cb v (eFloor m j)`, `k' := kc v (eFloor m j)` and
`y := uhsXj q - lamV v k`; by `cellPre_cb_kc`/`mem_cellPre` the point `y` lies in `cubeBox a` and
`y j = cubeCorner a j + 1` (by `lamK_kc` and the face condition).  By `cb_eFloor` and
`lamV_kc_eFloor` the cube `a'` is the upper wall neighbour `wallNb a j 1` and the offset satisfies
`y - wallLamV a j 1 = uhsXj q - lamV v k'`.  The finite certificate `chartKlein_wall a j 1` then
gives

  `chartKlein a' (mkE4 (uhsXj q - lamV v k') (q 3)) = act (wallGamK a j 1) (chartKlein a (mkE4 y (q 3)))`,

and both chart values lie in `Q̄` (`chartKlein_mem`, with the ceiling bound `ceilH a y = β (xOf q)`
from `ceilH_eq_beta` and the periodicity of `β`).  Finally the relation `rel` is exhibited with the
group element `γ := (wallGamK a j 1, wallGamFlip a j 1)`: the copy bit is `wallGam_sideType.1`, the
action on the Klein coordinate is the certificate above, and `γ ∈ Ksub (chartKlein a (mkE4 y s))`
because `γ = sideType (wallHi a j)` (`wallGam_sideType.2`) and
`sideSlack (wallHi a j) (chartKlein a (mkE4 y s)) = 0` (`sideSlack_wallHi_chartKlein`).

(Inlined from the delegated certificate `Work.RTOwed.mbFloor_step` of the module
`Submission.Work.RTOwed.mbFloor_step`, which cannot be imported here because that module imports
this one.) -/
theorem mbFloor_step_tmp (v : Fin 5) (m : Fin 3 → ℤ) (j : Fin 3) (q : CuspE4)
    (hbox : ∀ l : Fin 3, (m l : ℝ) ≤ (uhsXj q) l ∧ (uhsXj q) l ≤ (m l : ℝ) + 1)
    (hface : (uhsXj q) j = (m j : ℝ) + 1)
    (hs1 : 11 / 10 ≤ q 3) (hs2 : q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)) :
    mbFloor v m q = mbFloor v (eFloor m j) q := by
  set V1 : CuspE4 := chartKlein (cb v m) (mkE4 (uhsXj q - cuspCert.lamV v (kc v m)) (q 3)) with hV1
  set V2 : CuspE4 := chartKlein (cb v (eFloor m j))
      (mkE4 (uhsXj q - cuspCert.lamV v (kc v (eFloor m j))) (q 3)) with hV2
  have hcell : q ∈ cellPre v (cb v m) (kc v m) := by
    rw [cellPre_cb_kc]; exact hbox
  have hy1mem : uhsXj q - cuspCert.lamV v (kc v m) ∈ cubeBox (cb v m) :=
    (mem_cellPre (v := v) (a := cb v m) (k := kc v m) (q := q)).mp hcell
  have hface1 : (uhsXj q - cuspCert.lamV v (kc v m)) j
      = (Work.Cusp.cubeCorner (cb v m) j : ℝ) + 1 := by
    have h1 : (uhsXj q - cuspCert.lamV v (kc v m)) j
        = (uhsXj q) j - (cuspCert.lamK v (kc v m) j : ℝ) := by
      simp only [PiLp.sub_apply, cuspCert.lamV]
    rw [h1, lamK_kc, hface]
    ring
  have hy1 : (uhsXj q - cuspCert.lamV v (kc v m)) j
      = (Work.Cusp.cubeCorner (cb v m) j : ℝ) + (if ((1 : Fin 2) : ℕ) = 0 then 0 else 1) := by
    rw [hface1]
    norm_num
  have hlam : cuspCert.lamV v (kc v m) = Work.Cusp.ofInt3 (cuspCert.lamK v (kc v m)) := by
    apply PiLp.ext; intro i
    fin_cases i <;> simp [cuspCert.lamV, Work.Cusp.ofInt3]
  have hceil : ceilH (cb v m) (uhsXj q - cuspCert.lamV v (kc v m))
      = Work.Cusp.beta (Work.Cusp.xOf q) := by
    have hmem2 : (xOf4 q - cuspCert.lamV v (kc v m)) + cuspH
        = uhsXj q - cuspCert.lamV v (kc v m) := by
      simp only [uhsXj]; abel
    rw [← hmem2,
      ceilH_eq_beta (cb v m) (y := xOf4 q - cuspCert.lamV v (kc v m))
        (by rw [hmem2]; exact hy1mem),
      hlam, beta_sub_ofInt3, xOf4_eq_xOf]
  have hQ1 : V1 ∈ Work.FoldInst.Qbar := by
    rw [hV1]
    exact chartKlein_mem (cb v m) hy1mem hs1 (by rw [hceil]; exact hs2)
  have hcert := chartKlein_wall (cb v m) j 1 hy1 hy1mem hs1
  rw [← hV1] at hcert
  have hkb : cuspCert.lamV v (kc v (eFloor m j))
      = cuspCert.lamV v (kc v m) + wallLamV (cb v m) j 1 := lamV_kc_eFloor v m j
  have hy2 : uhsXj q - cuspCert.lamV v (kc v (eFloor m j))
      = (uhsXj q - cuspCert.lamV v (kc v m)) - wallLamV (cb v m) j 1 := by
    rw [hkb]; abel
  have hV2eq : V2 = Work.FoldInst.act (wallGamK (cb v m) j 1) V1 := by
    rw [hV2, cb_eFloor, hy2]
    exact hcert
  have hQ2 : V2 ∈ Work.FoldInst.Qbar := by
    rw [hV2eq]
    exact (Work.FoldInst.Qbar_act (wallGamK (cb v m) j 1) V1).mpr hQ1
  have hslack : Work.FoldInst.sideSlack (wallHi (cb v m) j) V1 = 0 := by
    rw [hV1]
    exact sideSlack_wallHi_chartKlein (cb v m) j hy1mem hface1 hs1
  have hK : (wallGamK (cb v m) j 1, wallGamFlip (cb v m) j 1) ∈ Work.FoldInst.Ksub V1 :=
    AddSubgroup.subset_closure ⟨wallHi (cb v m) j, hslack, (wallGam_sideType (cb v m) j).2⟩
  have hact : Work.FoldInst.actX (wallGamK (cb v m) j 1, wallGamFlip (cb v m) j 1)
      (xbarOf (cb v m) V1 hQ1) = xbarOf (cb v (eFloor m j)) V2 hQ2 := by
    refine Prod.ext ?_ ?_
    · show cubeBit (cb v m) + wallGamFlip (cb v m) j 1 = cubeBit (cb v (eFloor m j))
      rw [cb_eFloor]
      exact ((wallGam_sideType (cb v m) j).1).symm
    · apply Subtype.ext
      show Work.FoldInst.act (wallGamK (cb v m) j 1) V1 = V2
      exact hV2eq.symm
  have hm1 : mbFloor v m q = Work.FoldInst.mk (xbarOf (cb v m) V1 hQ1) := by
    rw [mbFloor]
    exact congrArg Work.FoldInst.mk (mbX_eq v (cb v m) (kc v m) hQ1)
  have hm2 : mbFloor v (eFloor m j) q
      = Work.FoldInst.mk (xbarOf (cb v (eFloor m j)) V2 hQ2) := by
    rw [mbFloor]
    exact congrArg Work.FoldInst.mk (mbX_eq v (cb v (eFloor m j)) (kc v (eFloor m j)) hQ2)
  rw [hm1, hm2]
  apply Quotient.sound
  exact ⟨(wallGamK (cb v m) j 1, wallGamFlip (cb v m) j 1), hK, hact⟩

/-! ## The floor induction -/

/-- The coordinates in which the floor `m` lies strictly below the floor of the cube coordinate. -/
def belowSet (m : Fin 3 → ℤ) (x : CuspE3) : Finset (Fin 3) :=
  Finset.univ.filter (fun l => m l < floorV x l)

theorem mem_belowSet {m : Fin 3 → ℤ} {x : CuspE3} {l : Fin 3} :
    l ∈ belowSet m x ↔ m l < floorV x l := by
  simp [belowSet]

theorem belowSet_eFloor_subset (m : Fin 3 → ℤ) (x : CuspE3) (j : Fin 3) :
    belowSet (eFloor m j) x ⊆ belowSet m x := by
  intro l hl
  rw [mem_belowSet] at hl ⊢
  by_cases h : l = j
  · subst h
    rw [eFloor_self] at hl
    omega
  · rwa [eFloor_of_ne m h] at hl

theorem belowSet_eFloor_card_lt (m : Fin 3 → ℤ) (x : CuspE3) (j : Fin 3)
    (hbox : ∀ l : Fin 3, (m l : ℝ) ≤ x l ∧ x l ≤ (m l : ℝ) + 1)
    (hj : m j < floorV x j) :
    (belowSet (eFloor m j) x).card < (belowSet m x).card := by
  have hsub := belowSet_eFloor_subset m x j
  have hjmem : j ∈ belowSet m x := by rw [mem_belowSet]; exact hj
  have hnotmem : j ∉ belowSet (eFloor m j) x := by
    rw [mem_belowSet, eFloor_self]
    have hle : floorV x j ≤ m j + 1 := by
      have hfl : (floorV x j : ℝ) ≤ x j := Int.floor_le _
      have h := hfl.trans (hbox j).2
      exact_mod_cast h
    omega
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_subset_ne]
  exact ⟨hsub, fun h => hnotmem (h.symm ▸ hjmem)⟩

/-- **The chart of a box of the lattice is the chart of the canonical cell**: the floor induction. -/
theorem mbFloor_eq_mbarLow (v : Fin 5) (m : Fin 3 → ℤ) (q : CuspE4)
    (hbox : ∀ l : Fin 3, (m l : ℝ) ≤ (uhsXj q) l ∧ (uhsXj q) l ≤ (m l : ℝ) + 1)
    (hs1 : 11 / 10 ≤ q 3) (hs2 : q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)) :
    mbFloor v m q = mbarLow v q := by
  have H : ∀ (N : ℕ) (m : Fin 3 → ℤ) (q : CuspE4),
      (belowSet m (uhsXj q)).card = N →
      (∀ l : Fin 3, (m l : ℝ) ≤ (uhsXj q) l ∧ (uhsXj q) l ≤ (m l : ℝ) + 1) →
      11 / 10 ≤ q 3 → q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q) →
      mbFloor v m q = mbarLow v q := by
    intro N
    refine Nat.strong_induction_on N (fun N ih => ?_)
    intro m q hcard hbox hs1 hs2
    by_cases hne : (belowSet m (uhsXj q)).Nonempty
    · obtain ⟨j, hj⟩ := hne
      rw [mem_belowSet] at hj
      have hxj : (uhsXj q) j = (m j : ℝ) + 1 := by
        have h1 : (m j : ℝ) + 1 ≤ (uhsXj q) j := by
          have hle : m j + 1 ≤ floorV (uhsXj q) j := by omega
          have hle' : ((m j + 1 : ℤ) : ℝ) ≤ (floorV (uhsXj q) j : ℝ) := by exact_mod_cast hle
          have hfl : (floorV (uhsXj q) j : ℝ) ≤ (uhsXj q) j := Int.floor_le _
          push_cast at hle'
          linarith
        linarith [(hbox j).2]
      have hstep := mbFloor_step_tmp v m j q hbox hxj hs1 hs2
      have hcard' : (belowSet (eFloor m j) (uhsXj q)).card < N := by
        rw [← hcard]
        exact belowSet_eFloor_card_lt m (uhsXj q) j hbox hj
      have hbox' : ∀ l : Fin 3, (eFloor m j l : ℝ) ≤ (uhsXj q) l ∧
          (uhsXj q) l ≤ (eFloor m j l : ℝ) + 1 := by
        intro l
        by_cases h : l = j
        · rw [h, eFloor_self]
          constructor
          · push_cast; linarith [hxj]
          · push_cast; linarith [(hbox j).2]
        · rw [eFloor_of_ne m h]
          exact hbox l
      rw [hstep]
      exact ih _ hcard' (eFloor m j) q rfl hbox' hs1 hs2
    · have hempty : belowSet m (uhsXj q) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hm : m = floorV (uhsXj q) := by
        funext l
        have hnot : ¬ (m l < floorV (uhsXj q) l) := by
          intro hlt
          have : l ∈ belowSet m (uhsXj q) := by rw [mem_belowSet]; exact hlt
          rw [hempty] at this
          exact absurd this (Finset.notMem_empty l)
        have h1 : floorV (uhsXj q) l ≤ m l := by omega
        have h2 : m l ≤ floorV (uhsXj q) l := (Int.le_floor).mpr (hbox l).1
        omega
      rw [hm, mbarLow_eq_mbFloor_self]
  exact H _ m q rfl hbox hs1 hs2

/-- **The ceiling of a cell is the ceiling of the canonical cube over the point.** -/
theorem ceilH_cell_eq_chartRed (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) {q : CuspE4}
    (hbox : uhsXj q - cuspCert.lamV v k ∈ cubeBox a) :
    ceilH a (uhsXj q - cuspCert.lamV v k) = ceilH (chartCube v q) (chartRed v q) := by
  have hfloor : uhsXj q - cuspCert.lamV v (cuspCert.floorK v (uhsXj q)) = redV v (uhsXj q) :=
    cuspCert.sub_lamV_floorK v (uhsXj q) (fun i => cuspCert.floorV_dvd v (uhsXj q) i)
  have hlam : cuspCert.lamV v (fun i => cuspCert.floorK v (uhsXj q) i - k i)
      = cuspCert.lamV v (cuspCert.floorK v (uhsXj q)) - cuspCert.lamV v k := by
    apply PiLp.ext; intro i
    simp only [cuspCert.lamV, PiLp.sub_apply, PiLp.toLp_apply]
    rw [cuspCert.lamK_sub]
    push_cast
    ring
  have hpoint : (uhsXj q - cuspCert.lamV v k)
      - cuspCert.lamV v (fun i => cuspCert.floorK v (uhsXj q) i - k i) = redV v (uhsXj q) := by
    rw [hlam]
    have : (uhsXj q - cuspCert.lamV v k)
        - (cuspCert.lamV v (cuspCert.floorK v (uhsXj q)) - cuspCert.lamV v k)
        = uhsXj q - cuspCert.lamV v (cuspCert.floorK v (uhsXj q)) := by abel
    rw [this, hfloor]
  have htrans := ceilH_sub_lamV v a (cubeOf v (uhsXj q))
    (fun i => cuspCert.floorK v (uhsXj q) i - k i) hbox
    (by rw [hpoint]; exact redV_mem_cubeBox v (uhsXj q))
  rw [hpoint] at htrans
  rw [htrans, chartCube, chartRed]

/-- **The branch of an arbitrary cell of the cusp is the value of `mbarLow`.** -/
theorem mbarLow_eq_mbBranch (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) {q : CuspE4}
    (hcusp : Work.Cusp.cubeCusp a = v)
    (hbox : uhsXj q - cuspCert.lamV v k ∈ cubeBox a)
    (hs1 : 11 / 10 ≤ q 3) (hs2 : q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)) :
    mbarLow v q = mbBranch v a k q := by
  set mm : Fin 3 → ℤ := fun l => Work.Cusp.cubeCorner a l + cuspCert.lamK v k l with hmm
  have hq : q ∈ cellPre v a k := hbox
  have hmem := (mem_cellPre_iff v a k q).mp hq
  have hbox' : ∀ l : Fin 3, (mm l : ℝ) ≤ (uhsXj q) l ∧ (uhsXj q) l ≤ (mm l : ℝ) + 1 := by
    intro l
    have h := hmem l
    have hcast : (mm l : ℝ) = (Work.Cusp.cubeCorner a l : ℝ) + (cuspCert.lamK v k l : ℝ) := by
      simp only [hmm]
      push_cast
      ring
    rw [hcast]
    exact h
  have hcb : cb v mm = a := by
    calc cb v mm = Work.Cusp.cubeOfMod v (Work.Cusp.cubeCorner a) := by
          refine cubeOfMod_residue v (fun i => ?_)
          have h : mm i - Work.Cusp.cubeCorner a i = cuspCert.lamK v k i := by
            simp only [hmm]
            ring
          rw [h]
          exact ⟨k i, by simp only [cuspCert.lamK]⟩
      _ = Work.Cusp.cubeOfMod (Work.Cusp.cubeCusp a) (Work.Cusp.cubeCorner a) := by rw [hcusp]
      _ = a := cubeOfMod_corner a
  have hkc : kc v mm = k := by
    funext i
    simp only [kc, hcb]
    have h : mm i - Work.Cusp.cubeCorner a i = k i * (Work.Cusp.latMod v i : ℤ) := by
      simp only [hmm, cuspCert.lamK]
      ring
    rw [h]
    exact Int.mul_ediv_cancel _ (ne_of_gt (cuspCert.latMod_pos v i))
  have h1 := mbFloor_eq_mbarLow v mm q hbox' hs1 hs2
  have h2 : mbFloor v mm q = mbBranch v a k q := by
    rw [mbFloor, hcb, hkc]
  exact h1.symm.trans h2

/-! ## The continuity of `mbarLow` on the chimney region -/

/-- The chimney region of the cusp chart: heights between `s₁ = 11/10` and the ceiling `β`. -/
def chimneyRegion : Set CuspE4 :=
  {q : CuspE4 | 11 / 10 ≤ q 3 ∧ q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)}

theorem continuous_beta_xOf : Continuous (fun q : CuspE4 => Work.Cusp.beta (Work.Cusp.xOf q)) :=
  Work.Cusp.beta_continuous.comp (by unfold Work.Cusp.xOf; fun_prop)

theorem isClosed_chimneyRegion : IsClosed chimneyRegion := by
  refine IsClosed.inter ?_ ?_
  · exact isClosed_le (f := fun _ : CuspE4 => (11 / 10 : ℝ)) (g := fun q => q 3)
      continuous_const (by fun_prop)
  · exact isClosed_le (f := fun q : CuspE4 => q 3)
      (g := fun q => Work.Cusp.beta (Work.Cusp.xOf q)) (by fun_prop) continuous_beta_xOf

theorem mbarLow_continuousOn_region (v : Fin 5) :
    ContinuousOn (mbarLow v) chimneyRegion := by
  set F : cuspCert.CIdx v → Set CuspE4 := fun p => cellPre v p.1.1 p.2 ∩ chimneyRegion with hFdef
  have hFclosed : ∀ p : cuspCert.CIdx v, IsClosed (F p) :=
    fun p => (isClosed_cellPre v p.1.1 p.2).inter isClosed_chimneyRegion
  have hFlf : LocallyFinite F :=
    (locallyFinite_cellPre v).subset (fun p => Set.inter_subset_left)
  have hFcont : ∀ p : cuspCert.CIdx v, ContinuousOn (mbarLow v) (F p) := by
    intro p
    have hbr : ContinuousOn (mbBranch v p.1.1 p.2) (F p) := by
      refine (continuousOn_mbBranch v p.1.1 p.2).mono ?_
      rintro q ⟨hq1, hq2⟩
      exact ⟨hq1, hq2.1,
        by rw [ceilH_cell_eq_chartRed v p.1.1 p.2 hq1]; exact le_ceilH_chartRed hq2.2⟩
    exact hbr.congr (fun q hq =>
      mbarLow_eq_mbBranch v p.1.1 p.2 p.1.2 hq.1 hq.2.1 hq.2.2)
  have hunion : (⋃ p : cuspCert.CIdx v, F p) = chimneyRegion := by
    rw [hFdef]
    rw [← Set.iUnion_inter]
    rw [iUnion_cellPre v, Set.univ_inter]
  have := hFlf.continuousOn_iUnion hFclosed hFcont
  rwa [hunion] at this

/-- **Continuity of the cusp chart on the chimney region** (the fields `mbarLow_cont` and `mbarLow_contTop` of `Work.Cusp.CuspGlueData`, for the concrete `Work.RTOwed.mbarLow`).

Route: on the region `{11/10 ≤ q 3 ∧ q 3 ≤ β (xOf q)}` the junk branch of `cuspLowPt` is never taken (`Work.RTOwed.mbarLow_eq_beta`, with `Work.RTOwed.le_ceilH_chartRed`), so `mbarLow v q = mk (cubeBit (chartCube v q), ⟨redChart v (chartCube v q) q, _⟩)`.  Split by the cell of the *cube* coordinate `uhsXj q = xOf q + cuspH`: `Work.RTOwed.cuspCert.cell v a k` and the locally finite closed cover `Work.RTOwed.cuspCert.locallyFinite_cells`, gluing with `LocallyFinite.continuous` exactly as in `Work.RTOwed.cuspCert.mbarPt_continuous` (whose `branch`/`continuous_branch`/`mbarPt_eq_branch` are the template).  On the cell of `a` at the offset `k` the function is `q ↦ mk (xbarOf a (chartKlein a (mkE4 (uhsXj q - lamV v k) (q 3))) _)`, continuous because `chartKlein a` is continuous where the height is positive (here `q 3 ≥ 11/10`).  The two box regions are then restrictions (`ContinuousOn.mono`) of the region `{11/10 ≤ q 3 ∧ q 3 ≤ β (xOf q)}`, which is closed; note `Work.Cusp.cuspChartBox v c δ ⊆ cuspBoxTop v c δ` and `sJ < sTop`. -/
theorem mbarLow_cont (v : Fin 5) (c : Work.Cusp.E3) (δ : ℝ) :
    ContinuousOn (Work.RTOwed.mbarLow v)
      {q : Work.Cusp.E4 | q ∈ Work.Cusp.cuspChartBox v c δ ∧
        q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)} ∧
    ContinuousOn (Work.RTOwed.mbarLow v)
      {q : Work.Cusp.E4 | q ∈ Work.Cusp.cuspBoxTop v c δ ∧
        q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)} := by
  have hR := mbarLow_continuousOn_region v
  constructor
  · refine hR.mono ?_
    rintro q ⟨hbox, hle⟩
    rw [Work.Cusp.cuspChartBox] at hbox
    exact ⟨le_of_lt hbox.2.1, hle⟩
  · refine hR.mono ?_
    rintro q ⟨hbox, hle⟩
    rw [Work.Cusp.cuspBoxTop] at hbox
    exact ⟨le_of_lt hbox.2.1, hle⟩

end

end Work.RTOwed
