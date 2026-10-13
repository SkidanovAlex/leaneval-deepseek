import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Route
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Defs
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNDefs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_b4
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.wlInfMul6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.mulPhi6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongPersist.Fstar_W6
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.DzFstar_W6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNAux
import Submission.Work.FTS.StrongEps.HkSq_const_mul
import Submission.Work.FTS.StrongPersist.H6Aux.Facts
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0Aux
import Submission.Work.FTS.EllipticEst.UopHk.hkMemDzPth_of_shifted
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.N_b6_star.Tools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N_b6_star` — the nine *star* pieces of the level-`6` `N`-block

See `N_b6_star/Tools.lean` for the elementary tools and the module docstring of the pieces.
-/

namespace Work.FTS.StrongEps.E4R3.Nblock6

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open MeasureTheory Set Filter
open scoped Real Topology

open Work.FTS.Galerkin (Fn)

theorem N_b6_star : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    (∀ k ∈ ({1, 2, 3, 5, 6, 7, 9, 10, 11} : Finset ℕ),
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by
  intro C₀ Ce Cs α hαmem
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  -- ## the four product rules and the fixed-atom prices
  obtain ⟨Cw, hCwpos, hwl0⟩ := Work.FTS.StrongEps.E4R3.RawE6Aux.wlInfMul6
  obtain ⟨Cφ, hCφpos, hmphi⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.mulPhi6
  obtain ⟨Csl, hCslpos, hslot⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
  obtain ⟨C1, hC1pos, hF6⟩ := Work.FTS.StrongPersist.Fstar_W6
  obtain ⟨C2, hC2pos, hDF6⟩ := Work.FTS.StrongPersist.DthFstar_W6
  obtain ⟨C3, hC3pos, hDZ6⟩ := Work.FTS.StrongPersist.DzFstar_W6
  -- ## the nine constants of the pieces
  set Zsl : ℝ := (Csl * α ^ (-(1 : ℝ))) ^ 2 with hZsl
  set κ1 : ℝ := 4 * (Cw * C1 ^ 2) * (1 + Ce ^ 2) with hκ1
  set κ2 : ℝ := 4 * (Cw * Cs ^ 2) * (1 + Cφ ^ 2) with hκ2
  set κ3 : ℝ := 4 * (Cw * Cs ^ 2) * (1 + Zsl) with hκ3
  set κ5 : ℝ := 4 * (Cw * C2 ^ 2) * (1 + Ce ^ 2) with hκ5
  set κ6 : ℝ := 4 * (Cw * Cs ^ 2) * (1 + Cφ ^ 2) with hκ6
  set κ7 : ℝ := 4 * (Cw * Cs ^ 2) * (1 + Zsl) with hκ7
  set κ9 : ℝ := 4 * (Cw * C3 ^ 2) * (1 + Ce ^ 2) with hκ9
  set κ10 : ℝ := 4 * (Cw * Cs ^ 2) * (1 + Cφ ^ 2) with hκ10
  set κ11 : ℝ := 4 * (Cw * Cs ^ 2) * (1 + Zsl) with hκ11
  set KK : ℝ := 1 + (κ1 + κ2 + κ3 + κ5 + κ6 + κ7 + κ9 + κ10 + κ11) with hKK
  -- nonnegativity of the constants
  have hZsl_nn : 0 ≤ Zsl := by rw [hZsl]; exact sq_nonneg _
  have hn1 : 0 ≤ κ1 := by
    rw [hκ1]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCwpos.le (sq_nonneg C1)))
      (add_nonneg zero_le_one (sq_nonneg Ce))
  have hn2 : 0 ≤ κ2 := by
    rw [hκ2]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCwpos.le (sq_nonneg Cs)))
      (add_nonneg zero_le_one (sq_nonneg Cφ))
  have hn3 : 0 ≤ κ3 := by
    rw [hκ3]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCwpos.le (sq_nonneg Cs)))
      (add_nonneg zero_le_one hZsl_nn)
  have hn5 : 0 ≤ κ5 := by
    rw [hκ5]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCwpos.le (sq_nonneg C2)))
      (add_nonneg zero_le_one (sq_nonneg Ce))
  have hn6 : 0 ≤ κ6 := by
    rw [hκ6]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCwpos.le (sq_nonneg Cs)))
      (add_nonneg zero_le_one (sq_nonneg Cφ))
  have hn7 : 0 ≤ κ7 := by
    rw [hκ7]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCwpos.le (sq_nonneg Cs)))
      (add_nonneg zero_le_one hZsl_nn)
  have hn9 : 0 ≤ κ9 := by
    rw [hκ9]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCwpos.le (sq_nonneg C3)))
      (add_nonneg zero_le_one (sq_nonneg Ce))
  have hn10 : 0 ≤ κ10 := by
    rw [hκ10]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCwpos.le (sq_nonneg Cs)))
      (add_nonneg zero_le_one (sq_nonneg Cφ))
  have hn11 : 0 ≤ κ11 := by
    rw [hκ11]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCwpos.le (sq_nonneg Cs)))
      (add_nonneg zero_le_one hZsl_nn)
  have hKKpos : 0 < KK := by
    rw [hKK]; linarith
  refine ⟨KK, hKKpos, ?_⟩
  intro Φs w Φg hw hXw hzero hell hK6 hstar
  -- ## the hypotheses of the pieces
  have hsw : Work.FTS.VocabO.StarPkgo α Cs Φs := hstar.toStarPkgo2.toStarPkgo
  have hF6' : Work.Spaces.WlInfMem α 6 (Work.Construction.Fstar α)
      ∧ Work.Spaces.WlInf α 6 (Work.Construction.Fstar α) ≤ C1 * α := hF6 α hα0 hα1
  have hDF6' : Work.Spaces.WlInfMem α 6 (Work.Spaces.Dth (Work.Construction.Fstar α))
      ∧ Work.Spaces.WlInf α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C2 * α ^ 2 :=
    hDF6 α hα0 hα1
  have hDZ6' : Work.Spaces.WlInfMem α 6 (Work.Spaces.Dz (Work.Construction.Fstar α))
      ∧ Work.Spaces.WlInf α 6 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C3 * α :=
    hDZ6 α hα0 hα1
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  -- the three star coefficients
  have hRsc : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_Rs_of_star hα0 hα1 hsw
  have hRwm : Work.Spaces.WlInfMem α 6
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    Work.FTS.StrongPersist.StarPkg6.RW6_mem hstar
  have hRwb : Work.Spaces.WlInf α 6
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      ≤ Cs * α := Work.FTS.StrongPersist.StarPkg6.RW6_bd hstar
  have hUsc : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
      * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_Us_of_star hα0 hα1 hsw
  have hUwm : Work.Spaces.WlInfMem α 6 (fun z θ => (z + 1) / z
      * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) :=
    Work.FTS.StrongPersist.StarPkg6.UszW6_mem hstar
  have hUwb : Work.Spaces.WlInf α 6 (fun z θ => (z + 1) / z
      * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ))
      ≤ Cs * α := Work.FTS.StrongPersist.StarPkg6.UszW6_bd hstar
  have hVsc : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_Vs_of_star hα0 hα1 hsw
  have hVwm : Work.Spaces.WlInfMem α 6
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    Work.FTS.StrongPersist.StarPkg6.VzW6_mem hstar
  have hVwb : Work.Spaces.WlInf α 6
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      ≤ Cs * α := Work.FTS.StrongPersist.StarPkg6.VzW6_bd hstar
  -- the `w`-level data
  have hm6w : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 6 (by norm_num) hw.mem
  have hm6Dthw : Work.Spaces.HkMem α 6 (Work.Spaces.Dth w) :=
    Work.FTS.StrongEps.ClassCRHS.hkMem_Dth_of_smoothOpen hα0 6 hw.reg hw.mem
  have hm6Dzw : Work.Spaces.HkMem α 6 (Work.Spaces.Dz w) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 6 hw.reg hw.mem
  have hE6 : 0 ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
  have hα2 : α ^ 2 ≤ 1 := pow_le_one₀ (n := 2) hα0.le hα1
  have hc2le9 : (-(2 * α)) ^ 2 ≤ 4 := by
    rw [show (-(2 * α)) ^ 2 = 4 * α ^ 2 by ring]
    linarith
  have hE7 : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  -- the `φ`-shifted atoms of the datum `w`
  have hphw := hmphi (α := α) hα0 hα1 hw.reg hm6w
  have hphDthw := hmphi (α := α) hα0 hα1 hw.reg.Dth hm6Dthw
  have hphDzw := hmphi (α := α) hα0 hα1 hw.reg.Dz hm6Dzw
  have hSP2 : Work.Spaces.HkSq α 6 (fun z θ => z / (1 + z) * w z θ)
      ≤ Cφ ^ 2 * Work.Spaces.HkSq α 6 w := hkSq_le_of_hkNorm_le 6 hphw.2.2
  have hSP6 : Work.Spaces.HkSq α 6 (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ)
      ≤ Cφ ^ 2 * Work.Spaces.HkSq α 7 w := by
    refine le_trans (hkSq_le_of_hkNorm_le 6 hphDthw.2.2) ?_
    exact mul_le_mul_of_nonneg_left
      (Work.FTS.StrongPersist.H6Aux.HkSq_Dth_le_succ' α (by linarith) 6 hw.mem)
      (sq_nonneg Cφ)
  have hSP10 : Work.Spaces.HkSq α 6 (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ)
      ≤ Cφ ^ 2 * Work.Spaces.HkSq α 7 w := by
    refine le_trans (hkSq_le_of_hkNorm_le 6 hphDzw.2.2) ?_
    exact mul_le_mul_of_nonneg_left
      (Work.FTS.StrongPersist.H6Aux.HkSq_Dz_le_succ' α 6 hw.reg hw.mem) (sq_nonneg Cφ)
  -- the three shifted `F_*`-slots
  obtain ⟨⟨hslFsm, hslFm, hslFb⟩, ⟨hslDFsm, hslDFm, hslDFb⟩, ⟨hslDZsm, hslDZm, hslDZb⟩⟩ :=
    hslot α hαmem
  have hSP3 : Work.Spaces.HkSq α 6 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ)
      ≤ Zsl := by
    exact le_trans (hkSq_le_sq_of_le 6 hslFb) (le_of_eq (by rw [hZsl]))
  have hSP7 : Work.Spaces.HkSq α 6
        (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ Zsl := by
    exact le_trans (hkSq_le_sq_of_le 6 hslDFb) (le_of_eq (by rw [hZsl]))
  have hSP11 : Work.Spaces.HkSq α 6
        (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ Zsl := by
    exact le_trans (hkSq_le_sq_of_le 6 hslDZb) (le_of_eq (by rw [hZsl]))
  -- ## the elliptic atoms of the perturbation
  have hRp : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg))
      ∧ Work.Spaces.HkMem α 6 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) :=
    ⟨by simpa only [Work.FTS.Nonlin.PhiTg] using hK6.R.1.1,
     by simpa only [Work.FTS.Nonlin.PhiTg] using hK6.R.1.2⟩
  have hRn : Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg))
      ≤ Ce * Work.Spaces.HkNorm α 6 w := by
    simpa only [Work.FTS.Nonlin.PhiTg] using hK6.R.2
  have hSP1 : Work.Spaces.HkSq α 6 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg))
      ≤ Ce ^ 2 * Work.Spaces.HkSq α 6 w := hkSq_le_of_hkNorm_le 6 hRn
  have hUp : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ)
      ∧ Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) :=
    ⟨by simpa only [Work.FTS.Nonlin.PhiTg] using hK6.U.1.1,
     by simpa only [Work.FTS.Nonlin.PhiTg] using hK6.U.1.2⟩
  have hUn : Work.Spaces.HkNorm α 6 (fun z θ => Work.Construction.Uop α
      (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ)
      ≤ Ce * Work.Spaces.HkNorm α 6 w := by
    simpa only [Work.FTS.Nonlin.PhiTg] using hK6.U.2
  have hSP5 : Work.Spaces.HkSq α 6 (fun z θ => Work.Construction.Uop α
      (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ)
      ≤ Ce ^ 2 * Work.Spaces.HkSq α 6 w := hkSq_le_of_hkNorm_le 6 hUn
  have hVp : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg))
      ∧ Work.Spaces.HkMem α 6 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) :=
    ⟨by simpa only [Work.FTS.Nonlin.PhiTg] using hK6.V.1.1,
     by simpa only [Work.FTS.Nonlin.PhiTg] using hK6.V.1.2⟩
  have hVn : Work.Spaces.HkNorm α 6 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg))
      ≤ Ce * Work.Spaces.HkNorm α 6 w := by
    simpa only [Work.FTS.Nonlin.PhiTg] using hK6.V.2
  have hSP9 : Work.Spaces.HkSq α 6 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg))
      ≤ Ce ^ 2 * Work.Spaces.HkSq α 6 w := hkSq_le_of_hkNorm_le 6 hVn
  -- ## the bound `B` and the product rule
  set B : ℝ := (1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2 with hB
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith [hE6, hE7, sq_nonneg (1 + Work.Spaces.HkSq α 6 w)]
  have hBnn : 0 ≤ B := le_trans zero_le_one hB1
  have hE6B : Work.Spaces.HkSq α 6 w ≤ B := by
    rw [hB]; nlinarith [hE6, hE7, sq_nonneg (1 + Work.Spaces.HkSq α 6 w)]
  have hE7B : Work.Spaces.HkSq α 7 w ≤ B := by rw [hB]; nlinarith [sq_nonneg (1 + Work.Spaces.HkSq α 6 w)]
  have hwl : ∀ (A P : ℝ → ℝ → ℝ) (K : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ K →
      Work.FTS.EllipticEst.SmoothOpen P → Work.Spaces.HkMem α 6 P →
      Work.Spaces.HkSq α 6 (fun z θ => A z θ * P z θ)
        ≤ Cw * α ^ (-(1 : ℝ)) * K ^ 2 * (1 + Work.Spaces.HkSq α 6 P) :=
    fun A P K hA hAm hAK hP hPm => hwl0 α hαmem A P K hA hAm hAK hP hPm
  have hcore1 : ∀ Ci : ℝ, α ^ (-(1 : ℝ)) * (Ci * α) ^ 2 ≤ Ci ^ 2 :=
    fun Ci => inv_mul_sq_le hα1 hα0
  have hcore2 : ∀ Ci : ℝ, α ^ (-(1 : ℝ)) * (Ci * α ^ 2) ^ 2 ≤ Ci ^ 2 :=
    fun Ci => inv_mul_sq_sq_le hα1 hα0
  -- ## the nine pieces
  have hN1 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 1) ≤ κ1 * B := by
    have hb := piece_le (α := α) (Cw := Cw) (c := (2 : ℝ)) (KA := C1 * α)
      (SP := Ce ^ 2 * Work.Spaces.HkSq α 6 w) (A := Work.Construction.Fstar α)
      (P := Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg))
      hwl hCwpos.le hα0 hFsm hF6'.1 hF6'.2 hRp.1 hRp.2 hSP1
    have harith := piece_arith_e1 (α := α) (Cw := Cw) (Ci := C1) (A := Ce ^ 2)
      (E := Work.Spaces.HkSq α 6 w) (c2 := (2 : ℝ) ^ 2) (B := B)
      hCwpos.le (hcore1 C1) (by norm_num) (by norm_num) (sq_nonneg Ce) hE6 hE6B hB1
    exact le_trans (le_trans hb harith) (le_of_eq (by rw [hκ1]; ring))
  have hN2 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 2) ≤ κ2 * B := by
    have hb := piece_le (α := α) (Cw := Cw) (c := (2 : ℝ)) (KA := Cs * α)
      (SP := Cφ ^ 2 * Work.Spaces.HkSq α 6 w)
      (A := fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      (P := fun z θ => z / (1 + z) * w z θ)
      hwl hCwpos.le hα0 hRsc hRwm hRwb hphw.1 hphw.2.1 hSP2
    have harith := piece_arith_e1 (α := α) (Cw := Cw) (Ci := Cs) (A := Cφ ^ 2)
      (E := Work.Spaces.HkSq α 6 w) (c2 := (2 : ℝ) ^ 2) (B := B)
      hCwpos.le (hcore1 Cs) (by norm_num) (by norm_num) (sq_nonneg Cφ) hE6 hE6B hB1
    exact le_trans (le_trans hb harith) (le_of_eq (by rw [hκ2]; ring))
  have hN3 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 3) ≤ κ3 * B := by
    have hb := piece_le (α := α) (Cw := Cw) (c := (2 : ℝ)) (KA := Cs * α) (SP := Zsl)
      (A := fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      (P := fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ)
      hwl hCwpos.le hα0 hRsc hRwm hRwb hslFsm hslFm hSP3
    have harith := piece_arith_sl1 (α := α) (Cw := Cw) (Ci := Cs) (Z := Zsl)
      (c2 := (2 : ℝ) ^ 2) (B := B)
      hCwpos.le (hcore1 Cs) (by norm_num) (by norm_num) hB1 hZsl_nn
    exact le_trans (le_trans hb harith) (le_of_eq (by rw [hκ3]; ring))
  have hN5 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 5) ≤ κ5 * B := by
    have hb := piece_le (α := α) (Cw := Cw) (c := (-2 : ℝ))
      (KA := C2 * α ^ 2) (SP := Ce ^ 2 * Work.Spaces.HkSq α 6 w)
      (A := Work.Spaces.Dth (Work.Construction.Fstar α))
      (P := fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ
        / Work.Construction.s2 θ)
      hwl hCwpos.le hα0 hFsm.Dth hDF6'.1 hDF6'.2 hUp.1 hUp.2 hSP5
    have harith := piece_arith_e2 (α := α) (Cw := Cw) (Ci := C2) (A := Ce ^ 2)
      (E := Work.Spaces.HkSq α 6 w) (c2 := (-2 : ℝ) ^ 2) (B := B)
      hCwpos.le (hcore2 C2) (by norm_num) (by norm_num) (sq_nonneg Ce) hE6 hE6B hB1
    exact le_trans (le_trans hb harith) (le_of_eq (by rw [hκ5]; ring))
  have hN6 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 6) ≤ κ6 * B := by
    have hb := piece_le (α := α) (Cw := Cw) (c := (-2 : ℝ)) (KA := Cs * α)
      (SP := Cφ ^ 2 * Work.Spaces.HkSq α 7 w)
      (A := fun z θ => (z + 1) / z
        * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ))
      (P := fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ)
      hwl hCwpos.le hα0 hUsc hUwm hUwb hphDthw.1 hphDthw.2.1 hSP6
    have harith := piece_arith_e1 (α := α) (Cw := Cw) (Ci := Cs) (A := Cφ ^ 2)
      (E := Work.Spaces.HkSq α 7 w) (c2 := (-2 : ℝ) ^ 2) (B := B)
      hCwpos.le (hcore1 Cs) (by norm_num) (by norm_num) (sq_nonneg Cφ) hE7 hE7B hB1
    exact le_trans (le_trans hb harith) (le_of_eq (by rw [hκ6]; ring))
  have hN7 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 7) ≤ κ7 * B := by
    have hb := piece_le (α := α) (Cw := Cw) (c := (-2 : ℝ)) (KA := Cs * α) (SP := Zsl)
      (A := fun z θ => (z + 1) / z
        * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ))
      (P := fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
      hwl hCwpos.le hα0 hUsc hUwm hUwb hslDFsm hslDFm hSP7
    have harith := piece_arith_sl1 (α := α) (Cw := Cw) (Ci := Cs) (Z := Zsl)
      (c2 := (-2 : ℝ) ^ 2) (B := B)
      hCwpos.le (hcore1 Cs) (by norm_num) (by norm_num) hB1 hZsl_nn
    exact le_trans (le_trans hb harith) (le_of_eq (by rw [hκ7]; ring))
  have hN9 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 9) ≤ κ9 * B := by
    have hb := piece_le (α := α) (Cw := Cw) (c := -(2 * α)) (KA := C3 * α)
      (SP := Ce ^ 2 * Work.Spaces.HkSq α 6 w)
      (A := Work.Spaces.Dz (Work.Construction.Fstar α))
      (P := Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg))
      hwl hCwpos.le hα0 hFsm.Dz hDZ6'.1 hDZ6'.2 hVp.1 hVp.2 hSP9
    have harith := piece_arith_e1 (α := α) (Cw := Cw) (Ci := C3) (A := Ce ^ 2)
      (E := Work.Spaces.HkSq α 6 w) (c2 := (-(2 * α)) ^ 2) (B := B)
      hCwpos.le (hcore1 C3) (sq_nonneg _) hc2le9
      (sq_nonneg Ce) hE6 hE6B hB1
    exact le_trans (le_trans hb harith) (le_of_eq (by rw [hκ9]; ring))
  have hN10 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 10) ≤ κ10 * B := by
    have hb := piece_le (α := α) (Cw := Cw) (c := -(2 * α)) (KA := Cs * α)
      (SP := Cφ ^ 2 * Work.Spaces.HkSq α 7 w)
      (A := fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      (P := fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ)
      hwl hCwpos.le hα0 hVsc hVwm hVwb hphDzw.1 hphDzw.2.1 hSP10
    have harith := piece_arith_e1 (α := α) (Cw := Cw) (Ci := Cs) (A := Cφ ^ 2)
      (E := Work.Spaces.HkSq α 7 w) (c2 := (-(2 * α)) ^ 2) (B := B)
      hCwpos.le (hcore1 Cs) (sq_nonneg _) hc2le9
      (sq_nonneg Cφ) hE7 hE7B hB1
    exact le_trans (le_trans hb harith) (le_of_eq (by rw [hκ10]; ring))
  have hN11 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 11) ≤ κ11 * B := by
    have hb := piece_le (α := α) (Cw := Cw) (c := -(2 * α)) (KA := Cs * α) (SP := Zsl)
      (A := fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      (P := fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      hwl hCwpos.le hα0 hVsc hVwm hVwb hslDZsm hslDZm hSP11
    have harith := piece_arith_sl1 (α := α) (Cw := Cw) (Ci := Cs) (Z := Zsl)
      (c2 := (-(2 * α)) ^ 2) (B := B)
      hCwpos.le (hcore1 Cs) (sq_nonneg _) hc2le9 hB1 hZsl_nn
    exact le_trans (le_trans hb harith) (le_of_eq (by rw [hκ11]; ring))
  -- ## dispatch
  intro k hk
  have hKc : κ1 ≤ KK := by rw [hKK]; linarith
  have hKc2 : κ2 ≤ KK := by rw [hKK]; linarith
  have hKc3 : κ3 ≤ KK := by rw [hKK]; linarith
  have hKc5 : κ5 ≤ KK := by rw [hKK]; linarith
  have hKc6 : κ6 ≤ KK := by rw [hKK]; linarith
  have hKc7 : κ7 ≤ KK := by rw [hKK]; linarith
  have hKc9 : κ9 ≤ KK := by rw [hKK]; linarith
  have hKc10 : κ10 ≤ KK := by rw [hKK]; linarith
  have hKc11 : κ11 ≤ KK := by rw [hKK]; linarith
  have hBexp : KK * B = KK * (1 + Work.Spaces.HkSq α 7 w)
      + KK * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by rw [hB]; ring
  have key : ∀ j ∈ ({1, 2, 3, 5, 6, 7, 9, 10, 11} : Finset ℕ),
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg j) ≤ KK * B := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact le_trans hN1 (mul_le_mul_of_nonneg_right hKc hBnn)
    · exact le_trans hN2 (mul_le_mul_of_nonneg_right hKc2 hBnn)
    · exact le_trans hN3 (mul_le_mul_of_nonneg_right hKc3 hBnn)
    · exact le_trans hN5 (mul_le_mul_of_nonneg_right hKc5 hBnn)
    · exact le_trans hN6 (mul_le_mul_of_nonneg_right hKc6 hBnn)
    · exact le_trans hN7 (mul_le_mul_of_nonneg_right hKc7 hBnn)
    · exact le_trans hN9 (mul_le_mul_of_nonneg_right hKc9 hBnn)
    · exact le_trans hN10 (mul_le_mul_of_nonneg_right hKc10 hBnn)
    · exact le_trans hN11 (mul_le_mul_of_nonneg_right hKc11 hBnn)
  rw [← hBexp]
  exact key k hk

end Work.FTS.StrongEps.E4R3.Nblock6
