import Mathlib
import Submission.Work.RTOwed.cuspChartWallReflect
import Submission.Work.RTOwed.chartKlein_self_facet
import Submission.Work.RTOwed.cuspChartBeta
import Submission.Work.RTOwed.CuspRigid
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
import Submission.Work.RTOwed.chartKlein_image_open
import Submission.Work.RTOwed.coordPermMat_isLorentz
import Submission.Work.RTOwed.coordPerm_eq_mobius
import Submission.Work.RTOwed.hypOfUHS_add_of_four_eq_zero
import Submission.Work.RTOwed.foldTrans_local
import Submission.Work.RTOwed.actX_Ksub_walk
import Submission.Work.RTOwed.mbarLow_eq_mbBranch_pos
import Submission.Work.RTOwed.mbarLow_cont
import Submission.Work.RTOwed.cuspChartRegion

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

/-! ## The reference Möbius chart of a cube cell -/

/-- The translation vector carrying the chart coordinate `q` to the cube coordinate of the cell
`(a,k)`: `mkE4 (uhsXj q - lamV v k) (q 3) = q + cellUhsVect v k`. -/
def cellUhsVect (v : Fin 5) (k : Fin 3 → ℤ) : CuspE4 := liftE4 (cuspH - cuspCert.lamV v k)

lemma cellUhsVect_three (v : Fin 5) (k : Fin 3 → ℤ) : cellUhsVect v k 3 = 0 := by
  rw [cellUhsVect, liftE4_apply]
  norm_num

lemma mkE4_eq_add_cellUhsVect (v : Fin 5) (k : Fin 3 → ℤ) (q : CuspE4) :
    mkE4 (uhsXj q - cuspCert.lamV v k) (q 3) = q + cellUhsVect v k := by
  ext i
  fin_cases i <;>
    simp [mkE4, uhsXj, xOf4, cuspH, cellUhsVect, liftE4_apply, cuspCert.lamV] <;> ring

/-- **The reference Möbius matrix of the cube cell `(a,k)` and the fold piece `r`**: the matrix of
the map `q ↦ foldTheta i r (chartKlein a (mkE4 (uhsXj q - lamV v k) (q 3)))`. -/
def cellMat (v : Fin 5) (i : Fin 98) (r : Fin (Work.FoldInst.foldCodim i) → Bool)
    (a : Fin 48) (k : Fin 3 → ℤ) : Matrix (Fin 5) (Fin 5) ℝ :=
  coordPermMat i * (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) * chartK a
    * Work.HypModel.uhsTranslation (cellUhsVect v k)

theorem cellMat_isLorentz (v : Fin 5) (i : Fin 98)
    (r : Fin (Work.FoldInst.foldCodim i) → Bool) (a : Fin 48) (k : Fin 3 → ℤ) :
    Work.HypModel.IsLorentzMat (cellMat v i r a k) := by
  have h1 : Work.HypModel.IsLorentzMat (coordPermMat i) := coordPermMat_isLorentz i
  have h2 : Work.HypModel.IsLorentzMat (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) :=
    Work.FoldInst.foldInst_foldNr_mul_foldDrR_isLorentz i r
  have h3 : Work.HypModel.IsLorentzMat (chartK a) := chartK_isLorentz a
  have h4 : Work.HypModel.IsLorentzMat (Work.HypModel.uhsTranslation (cellUhsVect v k)) :=
    Work.HypModel.isLorentzMat_uhsTranslation _
  rw [cellMat]
  exact ((h1.mul h2).mul h3).mul h4

/-- **The cube chart composed with a fold piece is the reference Möbius map.** -/
theorem foldTheta_chartKlein_eq_mobius (v : Fin 5) (i : Fin 98)
    (r : Fin (Work.FoldInst.foldCodim i) → Bool) (a : Fin 48) (k : Fin 3 → ℤ) (q : CuspE4)
    (hq : 0 < q 3) :
    Work.FoldInst.foldTheta i r (chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)))
      = Work.HypModel.mobius (cellMat v i r a k) q := by
  have hL1 : Work.HypModel.IsLorentzMat (coordPermMat i) := coordPermMat_isLorentz i
  have hL2 : Work.HypModel.IsLorentzMat (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) :=
    Work.FoldInst.foldInst_foldNr_mul_foldDrR_isLorentz i r
  have hL3 : Work.HypModel.IsLorentzMat (chartK a) := chartK_isLorentz a
  have hL4 : Work.HypModel.IsLorentzMat (Work.HypModel.uhsTranslation (cellUhsVect v k)) :=
    Work.HypModel.isLorentzMat_uhsTranslation _
  have hX : Work.HypModel.IsLorentzMat
      (((Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) * chartK a)
        * Work.HypModel.uhsTranslation (cellUhsVect v k)) := (hL2.mul hL3).mul hL4
  have hP : chartK a *ᵥ Work.HypModel.hypOfUHS (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3))
      ∈ Work.HypModel.upperSheet :=
    Work.HypModel.isLorentzMat_mem_upperSheet hL3
      (hypOfUHS_mem_upperSheet (by
        show 0 < (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)) 3
        simp only [mkE4, PiLp.toLp_apply]
        exact hq))
  have hhyp : Work.HypModel.hypOfUHS (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3))
      = Work.HypModel.uhsTranslation (cellUhsVect v k) *ᵥ Work.HypModel.hypOfUHS q := by
    rw [mkE4_eq_add_cellUhsVect v k q]
    exact Work.RTOwed.hypOfUHS_add_of_four_eq_zero (cellUhsVect v k) q
      (cellUhsVect_three v k) hq
  have hu : 0 < (Work.HypModel.uhsOfHyp
      ((((Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) * chartK a)
        * Work.HypModel.uhsTranslation (cellUhsVect v k)) *ᵥ Work.HypModel.hypOfUHS q)) 3 := by
    rw [Work.HypModel.uhsOfHyp_apply_three]
    exact inv_pos.mpr (Work.HypModel.upperSheet_four_sub_three_pos
      (Work.HypModel.isLorentzMat_mem_upperSheet hX (hypOfUHS_mem_upperSheet hq)))
  calc Work.FoldInst.foldTheta i r (chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)))
      = Work.FoldInst.coordPerm i (Work.HypModel.uhsOfHyp
          ((Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r)
            *ᵥ (chartK a *ᵥ Work.HypModel.hypOfUHS
                (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3))))) := by
          rw [chartKlein_eq a, Work.FoldInst.foldTheta, Work.HypModel.mobiusKlein,
            Work.HypModel.hypOfKlein_kleinOfHyp hP, Matrix.mulVec_mulVec]
    _ = Work.FoldInst.coordPerm i (Work.HypModel.uhsOfHyp
          (((Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) * chartK a)
            *ᵥ Work.HypModel.hypOfUHS (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)))) := by
          rw [Matrix.mulVec_mulVec]
    _ = Work.FoldInst.coordPerm i (Work.HypModel.uhsOfHyp
          ((((Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) * chartK a)
            * Work.HypModel.uhsTranslation (cellUhsVect v k)) *ᵥ Work.HypModel.hypOfUHS q)) := by
          rw [hhyp, Matrix.mulVec_mulVec]
    _ = Work.HypModel.mobius (coordPermMat i)
          (Work.HypModel.mobius
            (((Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) * chartK a)
              * Work.HypModel.uhsTranslation (cellUhsVect v k)) q) := by
          rw [coordPerm_eq_mobius i hu]
          rfl
    _ = Work.HypModel.mobius
          (coordPermMat i * (((Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) * chartK a)
            * Work.HypModel.uhsTranslation (cellUhsVect v k))) q :=
          (Work.HypModel.mobius_mul hL1 hX hq).symm
    _ = Work.HypModel.mobius (cellMat v i r a k) q := by
          rw [cellMat]
          simp only [Matrix.mul_assoc]


/-! ## The cell identity and the one-wall unfolding -/

/-- **`mbarLow` is the chart of any cell whose box contains the reduced coordinate.**
For a cube `a` of the cusp `v`, an offset `k` with `uhsXj q - lamV v k ∈ cubeBox a` and a height in
`[11/10, ceilH a (uhsXj q - lamV v k)]`, the chart value of `mbarLow v` at `q` is the `mk` of the
chart point of the cube `a` at the cell offset `k`. -/
theorem mbarLow_eq_cellX (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (hcusp : Cusp.cubeCusp a = v)
    {q : CuspE4} (hbox : uhsXj q - cuspCert.lamV v k ∈ cubeBox a)
    (hs1 : 11 / 10 ≤ q 3) (hs2 : q 3 ≤ ceilH a (uhsXj q - cuspCert.lamV v k)) :
    mbarLow v q = Work.FoldInst.mk (xbarOf a
      (chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)))
      (chartKlein_mem a hbox hs1 hs2)) := by
  rw [mbarLow_eq_mbBranch_pos v a k hcusp hbox (by linarith)]
  exact mbBranch_eq v a k (chartKlein_mem a hbox hs1 hs2)

/-- **The one-wall unfolding (whole-hyperplane form of `chartKlein_wall`).**
For every point `q` of positive height, the chart of the far cube `wallNb a i 0` at the *shifted*
near-cell coordinate `(uhsXj q - lamV v k) - wallLamV a i 0` equals the group translate of the chart
of the cube `a` at the *reflected* near-cell coordinate. -/
theorem chartKlein_wall_refl_zero (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (i : Fin 3)
    (q : CuspE4) (hs : 0 < q 3) :
    chartKlein (wallNb a i 0)
        (mkE4 ((uhsXj q - cuspCert.lamV v k) - wallLamV a i 0) (q 3))
      = Work.FoldInst.act (wallGamK a i 0)
          (chartKlein a (mkE4
            (reflWall i (Work.Cusp.cubeCorner a i) (uhsXj q - cuspCert.lamV v k)) (q 3))) := by
  have h := chartKlein_wall_refl (a := a) (i := i) (side := 0)
    (y := uhsXj q - cuspCert.lamV v k) (s := q 3) hs
  have hc : ((cwC a i 0 : ℤ) : ℝ) = (Work.Cusp.cubeCorner a i : ℝ) := by
    rw [cwC_eq_corner]; norm_num
  rw [hc] at h
  exact h

/-- **The lattice form of the one-wall unfolding.**  If `k₀` is a lattice shift realising the wall
vector (`lamV v k₀ = wallLamV a i 0`), then the chart of the far cell `(wallNb a i 0, k + k₀)` at
`q` is the group translate of the chart of the cube `a` at the reflected near-cell coordinate. -/
theorem chartKlein_wall_refl_zero' (v : Fin 5) (a : Fin 48) (k k₀ : Fin 3 → ℤ) (i : Fin 3)
    (hk₀ : cuspCert.lamV v k₀ = wallLamV a i 0) (q : CuspE4) (hs : 0 < q 3) :
    chartKlein (wallNb a i 0)
        (mkE4 (uhsXj q - cuspCert.lamV v (k + k₀)) (q 3))
      = Work.FoldInst.act (wallGamK a i 0)
          (chartKlein a (mkE4
            (reflWall i (Work.Cusp.cubeCorner a i) (uhsXj q - cuspCert.lamV v k)) (q 3))) := by
  have h1 : uhsXj q - cuspCert.lamV v (k + k₀)
      = (uhsXj q - cuspCert.lamV v k) - wallLamV a i 0 := by
    rw [cuspWall_lamV_add, hk₀]
    rw [sub_sub]
  rw [h1]
  exact chartKlein_wall_refl_zero v a k i q hs

/-- **The cube coordinate of the reflected point.** -/
theorem uhsXj_reflWall4 (i : Fin 3) (c : ℝ) (q : CuspE4) :
    uhsXj (reflWall4 i c q) = reflWall i (c + 1 / 2) (uhsXj q) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp only [uhsXj, xOf4, cuspH, reflWall4_apply, reflWall_apply, PiLp.add_apply,
      PiLp.toLp_apply, PiLp.sub_apply] <;>
    norm_num <;> ring

/-- The reflected near-cell coordinate of a point is the near-cell coordinate of its reflection. -/
theorem uhsXj_reflWall4_sub (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (i : Fin 3) (q : CuspE4) :
    uhsXj (reflWall4 i ((Work.Cusp.cubeCorner a i : ℝ) + (cuspCert.lamV v k) i - 1 / 2) q)
        - cuspCert.lamV v k
      = reflWall i (Work.Cusp.cubeCorner a i) (uhsXj q - cuspCert.lamV v k) := by
  rw [uhsXj_reflWall4]
  apply PiLp.ext
  intro j
  show (reflWall i ((Work.Cusp.cubeCorner a i : ℝ) + (cuspCert.lamV v k) i - 1 / 2 + 1 / 2)
      (uhsXj q) - cuspCert.lamV v k) j
    = (reflWall i (Work.Cusp.cubeCorner a i) (uhsXj q - cuspCert.lamV v k)) j
  rw [PiLp.sub_apply, reflWall_apply, reflWall_apply]
  by_cases hj : j = i
  · subst hj
    rw [ite_eq_left rfl, ite_eq_left rfl]
    simp only [PiLp.sub_apply]
    ring
  · rw [ite_eq_right hj, ite_eq_right hj]
    simp only [PiLp.sub_apply]

/-- The reflection preserves the height. -/
@[simp] theorem reflWall4_three (i : Fin 3) (c : ℝ) (q : CuspE4) :
    reflWall4 i c q 3 = q 3 := by
  rw [reflWall4_apply]
  have h : ((3 : Fin 4) : ℕ) ≠ (i : ℕ) := by have := i.isLt; omega
  rw [if_neg h]

end

end Work.RTOwed
