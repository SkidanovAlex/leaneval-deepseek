/-
# `Work.FTS.EllSol.EllPkgAux.uopSlotCore` — the level-`4` `U/sin 2θ` slot, modulo the elliptic closure

For `X := ellShift α g Ψ`, `Ξ := PhiTil α g Ψ = EllResid α g Ψ`, `Ḡ := Gbar α g`, `F_* := Fstar g`
and `σ := sin 2θ`, the exact identity on the open quadrant

  `Uop α Ξ / σ = -3·(X/σ) - α·(D_zX/σ) - (2Ḡ + (3/4)F_*)`

(`Work.FTS.EllSol.EllPkgAux.uopPointwiseId`) reduces the slot to the open-class DivisionBySin at `X` and at `D_zX`
(`PkgK5.divSinK5`), the `ℋ⁴`-wall of the trace-class §7 interpolation at `X`
(`PkgK5.wall_of_interp 4`, hypothesis `hwall`), the Poincaré/Agmon package
(`PkgK5.uopDzIter2Bound 4`) and the radial layer (`Gbar_Hk_le_open`, `Fstar_Hk_le_open`,
`PkgK5.radialHkNorm_le_sinMul`).

This module proves the resulting estimate with the right-hand side
`α²‖z²∂²_zX‖₄ + ‖∂²_θX‖₄ + ‖g‖₄` (the elliptic closure to `C‖g‖₄` is done in `uopSlotLe4.lean`).
The traces of `X` for `j ≤ 5`, the level-`4` weak class `EllWeakPos α 4 (orthSource g) X` and the
two honesty inputs of the wall all come from the level-`7` class `EllClassOk 7 α g Ψ`
(`PkgK5.tracesK5`, `ClassC.ellWeakPos_descend`, `TT.HkMem_descend_open`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.uopSlotAux
import Submission.Work.FTS.EllSol.PkgK5.wall_of_interp
import Submission.Work.FTS.EllSol.PkgK5.divSinK5
import Submission.Work.FTS.EllSol.PkgK5.tracesK5
import Submission.Work.FTS.EllSol.PkgK5.uopDzIter2Bound
import Submission.Work.FTS.EllSol.PkgK5.radialHkNorm_le_sinMul
import Submission.Work.FTS.EllSol.PkgK5.uopRadialSinMulTransfer
import Submission.Work.FTS.EllSol.PkgK5.residTracesK5
import Submission.Work.FTS.EllipticEst.Gbar_Hk_le_open
import Submission.Work.FTS.EllipticEst.Fstar_Hk_le_open
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.Cert.HkMem_Gbar_sin
import Submission.Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.RPFresh.DivSinOpen.Defs
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.ClassC.removingL12_classC_aux
import Submission.Work.FTS.EllExist.ClassCInputs
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- **The level-`4` `U/sin 2θ` slot, with the wall form of the right-hand side.** -/
theorem uopSlot_core (hwall : Work.FTS.EllSol.PkgK5.WallK5 4) :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (g Ψ : Work.FTS.Galerkin.Fn),
      0 < α → α ≤ 1 / 4 → Work.FTS.EllSol.ClassC α g →
      Work.FTS.EllExist.EllClassOk 7 α g Ψ →
      Work.FTS.VocabO.HQo α 4 (fun z θ =>
          Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ) z θ / Work.Construction.s2 θ) ∧
      Work.Spaces.HkNorm α 4 (fun z θ =>
          Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ) z θ / Work.Construction.s2 θ)
        ≤ K * (α ^ 2 * Work.Spaces.HkNorm α 4
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Ψ) z θ)
            + Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Ψ))
            + Work.Spaces.HkNorm α 4 g) := by
  obtain ⟨Cw, hCwpos, hwall'⟩ := hwall
  obtain ⟨CD, hCDpos, hD⟩ := Work.FTS.EllSol.PkgK5.uopDzIter2Bound 4 (by norm_num)
  obtain ⟨Cdiv, hCdivpos, hdiv⟩ := Work.FTS.EllSol.PkgK5.divSinK5 4 (by norm_num)
  obtain ⟨Crad, hCradpos, hrad⟩ := Work.FTS.EllSol.PkgK5.radialHkNorm_le_sinMul 4
  obtain ⟨Cgb, hCgbpos, hgb⟩ := Work.FTS.EllipticEst.Gbar_Hk_le_open 4
  obtain ⟨Cfs, hCfspos, hfs⟩ := Work.FTS.EllipticEst.Fstar_Hk_le_open 4
  set K3 : ℝ := Real.sqrt 2 * (2 * Crad * Cgb + (3 / 4) * Crad * Cfs) with hK3
  set K : ℝ := Real.sqrt 2 * (3 * (Cdiv * CD)
    + Real.sqrt 2 * (Cdiv * Cw * (2 * CD + 1) + K3)) + 1 with hK
  have hK3pos : 0 < K3 := by rw [hK3]; positivity
  have hKpos : 0 < K := by rw [hK]; positivity
  refine ⟨K, hKpos, ?_⟩
  intro α g Ψ hα hα4 hC hOk
  have hα1 : α ≤ 1 := by linarith
  set X : ℝ → ℝ → ℝ := Work.FTS.EllSol.ellShift α g Ψ with hXdef
  set Gb : ℝ → ℝ := Work.Elliptic.Gbar α g with hGbdef
  set Fs : ℝ → ℝ := Work.Elliptic.Fstar g with hFsdef
  -- ## the class data
  have hsol : Work.FTS.StrongGlobal.IsBslSolPos α g Ψ :=
    Work.FTS.StrongGlobal.IsBslSol.toPos hOk.1
  have hsmΦ : Work.FTS.EllipticEst.SmoothOpen Ψ := hOk.2.1
  have hweak7 : Work.FTS.EllipticEst.TT.EllWeakPos α 7 (Work.Elliptic.orthSource g) X := by
    have hshift : Work.FTS.EllExist.shiftSing α g Ψ = Work.FTS.EllSol.ellShift α g Ψ := rfl
    rw [hXdef, ← hshift]
    exact hOk.2.2
  have hOsSm : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) :=
    Work.FTS.EllExist.smoothOpen_orthSource_of_Fstar_smooth hC.reg hC.fsm
  have hXsm : Work.FTS.EllipticEst.SmoothOpen X :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (F := X) (by
      intro n
      have h := hweak7.smooth n
      simpa only [hXdef, Work.FTS.EllipticEst.Q0] using h)
  have hweak : Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g) X :=
    Work.FTS.ClassC.ellWeakPos_descend (α := α) (k := 4) (l := 7)
      (F := Work.Elliptic.orthSource g) (Ψ := X) (by norm_num) hOsSm hXsm hweak7
  have hAh : Work.Spaces.HkMem α 7 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) := hweak7.memA
  have hFmem : Work.Spaces.HkMem α 6 (Work.Elliptic.orthSource g) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 6) (l := 7)
      (f := Work.Elliptic.orthSource g) (by norm_num) hOsSm.forall hweak7.memF
  -- ## the traces of `X` (via the level-`7` class)
  have htr : ∀ j : ℕ, j ≤ 5 → ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j X z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j X z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    intro j hj z hz
    simpa only [hXdef] using
      Work.FTS.EllSol.PkgK5.tracesK5 4 (by norm_num) α g Ψ hα hα4 hC hsol hsmΦ hweak hAh hFmem
        j (by omega) z hz
  have hAhk : Work.Spaces.HkMem α 4 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) :=
    hweak.memA
  -- ## the angular Poincaré/Agmon package for `X`
  obtain ⟨hXmem, hXpthmem, hXnorm, hXpthnorm, hDzXmem, hDzXle, hDz2Xmem, hDz2Xle⟩ :=
    hD α X hα hα4 hXsm (fun j hj z hz => htr j (by omega) z hz) hweak.memB hAhk
  -- ## the wall at `X`
  obtain ⟨hDzpthmem, hDzpthle⟩ :=
    hwall' α X hα hα4 hXsm
      (fun z => by simpa only [hXdef] using hweak.zero z)
      (fun z => by simpa only [hXdef] using hweak.pi_half z)
      (fun j hj z hz => htr j (by omega) z hz) hDzXmem hDz2Xmem hweak.memB hweak.memZPth2
  -- ## Clairaut: `D_z∂_θX = ∂_θD_zX` on the open quadrant
  have hcommQ : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.Dz (Work.Spaces.pth X) z θ = Work.Spaces.pth (Work.Spaces.Dz X) z θ := by
    intro z θ hz hθ hlt
    have hcd : ContDiffAt ℝ 2 (Function.uncurry X) (z, θ) :=
      (hXsm.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hlt⟩))
    have hcomm := Work.Spaces.pz_pth_comm (f := X) hcd
    have h1 : Work.Spaces.Dz (Work.Spaces.pth X) z θ
        = z * Work.Spaces.pth (Work.Spaces.pz X) z θ := by
      show z * Work.Spaces.pz (Work.Spaces.pth X) z θ = z * Work.Spaces.pth (Work.Spaces.pz X) z θ
      rw [hcomm]
    have h2 : Work.Spaces.pth (Work.Spaces.Dz X) z θ
        = z * Work.Spaces.pth (Work.Spaces.pz X) z θ := by
      have hd : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz X z θ') θ :=
        (((hXsm.pz).curry_θ hz).contDiffAt (isOpen_Ioo.mem_nhds ⟨hθ, hlt⟩)).differentiableAt
          (by simp [Work.Stability.smoothOrder])
      show deriv (fun θ' => Work.Spaces.Dz X z θ') θ
        = z * Work.Spaces.pth (Work.Spaces.pz X) z θ
      rw [show (fun θ' => Work.Spaces.Dz X z θ') = fun θ' => z * Work.Spaces.pz X z θ' from rfl,
        deriv_const_mul _ hd]
      rfl
    rw [h1, h2]
  have hDzXpthmem : Work.Spaces.HkMem α 4 (Work.Spaces.pth (Work.Spaces.Dz X)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hDzpthmem
      (fun z hz θ hθ => hcommQ z θ hz hθ.1 hθ.2)
  -- ## the two division steps
  obtain ⟨hA1mem, hA1le⟩ :=
    hdiv α X hα hα1 hXsm
      (fun z hz j _ => (hXsm.DzIter j).curry_θ hz)
      (fun z hz j hj => (htr j (by omega) z hz).1)
      (fun z hz j hj => (htr j (by omega) z hz).2)
      hXpthmem
  have htrDz0 : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ 4 → Filter.Tendsto
      (fun θ : ℝ => Work.Spaces.DzIter j (Work.Spaces.Dz X) z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    intro z hz j hj
    have h := (htr (j + 1) (by omega) z hz).1
    have heq : (fun θ : ℝ => Work.Spaces.DzIter j (Work.Spaces.Dz X) z θ)
        = fun θ : ℝ => Work.Spaces.DzIter (j + 1) X z θ := by
      funext θ
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
        (congrFun (congrFun (Work.Spaces.DzIter_add_right j 1 X) z) θ).symm
    rw [heq]
    exact h
  have htrDz1 : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ 4 → Filter.Tendsto
      (fun θ : ℝ => Work.Spaces.DzIter j (Work.Spaces.Dz X) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    intro z hz j hj
    have h := (htr (j + 1) (by omega) z hz).2
    have heq : (fun θ : ℝ => Work.Spaces.DzIter j (Work.Spaces.Dz X) z θ)
        = fun θ : ℝ => Work.Spaces.DzIter (j + 1) X z θ := by
      funext θ
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
        (congrFun (congrFun (Work.Spaces.DzIter_add_right j 1 X) z) θ).symm
    rw [heq]
    exact h
  have hsliceDz : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ 4 → ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Spaces.DzIter j (Work.Spaces.Dz X) z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    intro z hz j _
    have h := (hXsm.Dz.DzIter j).curry_θ hz
    simpa only [Work.Spaces.DzIter_succ] using h
  obtain ⟨hA2mem, hA2le⟩ :=
    hdiv α (Work.Spaces.Dz X) hα hα1 hXsm.Dz hsliceDz htrDz0 htrDz1 hDzXpthmem
  have hnorm_eq : Work.Spaces.HkNorm α 4 (Work.Spaces.pth (Work.Spaces.Dz X))
      = Work.Spaces.HkNorm α 4 (Work.Spaces.Dz (Work.Spaces.pth X)) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm,
      Work.FTS.EllipticEst.HkSq_congr_open α 4
        (f := Work.Spaces.pth (Work.Spaces.Dz X))
        (g := Work.Spaces.Dz (Work.Spaces.pth X))
        (fun z θ hz hθ hlt => (hcommQ z θ hz hθ hlt).symm)]
  have hA2alpha : α * Work.Spaces.HkNorm α 4
        (fun z θ => Work.Spaces.Dz X z θ / Real.sin (2 * θ))
      ≤ Cdiv * (α * Work.Spaces.HkNorm α 4 (Work.Spaces.Dz (Work.Spaces.pth X))) := by
    calc α * Work.Spaces.HkNorm α 4 (fun z θ => Work.Spaces.Dz X z θ / Real.sin (2 * θ))
        ≤ α * (Cdiv * Work.Spaces.HkNorm α 4 (Work.Spaces.pth (Work.Spaces.Dz X))) :=
          mul_le_mul_of_nonneg_left hA2le hα.le
      _ = Cdiv * (α * Work.Spaces.HkNorm α 4 (Work.Spaces.Dz (Work.Spaces.pth X))) := by
          rw [hnorm_eq]; ring
  -- ## the radial layer
  have hgk : Work.Spaces.HkMem α 4 g :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 4) (l := 7) (by norm_num)
      hC.reg.forall hC.mem
  have hGbsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α g) (Set.Ioi 0) :=
    Work.FTS.EllSol.PkgK5.gbar_contDiffOn_classC hα hC.reg hC.fsm hC.mem
  have hGbSin : Work.Spaces.HkMem α 4 (fun z θ => Gb z * Real.sin (2 * θ)) := by
    simpa only [hGbdef] using
      Work.FTS.EllipticEst.Cert.HkMem_target_of_smoothOpen α hα hα1 4 g hC.reg hgk
  have hFsSin : Work.Spaces.HkMem α 4 (fun z θ => Fs z * Real.sin (2 * θ)) := by
    simpa only [hFsdef, Work.FTS.EllipticEst.Bmom_zero] using
      Work.FTS.EllipticEst.Cert.HkMem_bmom_sin_of_smoothOpen α 4 g hα hα1 hC.reg hgk
  have hGbRad : Work.Spaces.HkMem α 4 (fun z θ => Gb z) :=
    Work.FTS.EllSol.PkgK5.uopRadialSinMulTransfer (Λ := Gb) hGbsm hGbSin
  have hFsRad : Work.Spaces.HkMem α 4 (fun z θ => Fs z) :=
    Work.FTS.EllSol.PkgK5.uopRadialSinMulTransfer (Λ := Fs) hC.fsm hFsSin
  have hGbsmOpen : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Gb z) :=
    smoothOpen_radial_slot hGbsm
  have hFssmOpen : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Fs z) :=
    smoothOpen_radial_slot hC.fsm
  have hsumRadSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * Gb z + (3 / 4) * Fs z) :=
    Work.FTS.EllipticEst.smoothOpen_add (hGbsmOpen.const_mul' 2) (hFssmOpen.const_mul' (3 / 4))
  have hsumRadMem : Work.Spaces.HkMem α 4 (fun z θ => 2 * Gb z + (3 / 4) * Fs z) :=
    Work.FTS.EllipticEst.HkMem_add_open (hGbsmOpen.const_mul' 2) (hFssmOpen.const_mul' (3 / 4))
      (Work.FTS.LocData.HkMem_const_mul α 4 2 hGbRad)
      (Work.FTS.LocData.HkMem_const_mul α 4 (3 / 4) hFsRad)
  -- ## the pieces
  set A1 : ℝ → ℝ → ℝ := fun z θ => X z θ / Real.sin (2 * θ) with hA1def
  set A2 : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.Dz X z θ / Real.sin (2 * θ) with hA2def
  set A3 : ℝ → ℝ → ℝ := fun z θ => (-1 : ℝ) * (2 * Gb z + (3 / 4) * Fs z) with hA3def
  set u : ℝ → ℝ → ℝ :=
    fun z θ => (-3 : ℝ) * A1 z θ + ((-α) * A2 z θ + A3 z θ) with hudef
  have hA1sm : Work.FTS.EllipticEst.SmoothOpen A1 := by
    rw [hA1def]; exact Work.FTS.EllipticEst.RPFresh.smoothOpen_div_sin hXsm
  have hA2sm : Work.FTS.EllipticEst.SmoothOpen A2 := by
    rw [hA2def]; exact Work.FTS.EllipticEst.RPFresh.smoothOpen_div_sin hXsm.Dz
  have hA3sm : Work.FTS.EllipticEst.SmoothOpen A3 := by
    rw [hA3def]
    exact hsumRadSm.const_mul' (-1)
  have hA1mem' : Work.Spaces.HkMem α 4 A1 := by rw [hA1def]; exact hA1mem
  have hA2mem' : Work.Spaces.HkMem α 4 A2 := by rw [hA2def]; exact hA2mem
  have hA3mem : Work.Spaces.HkMem α 4 A3 := by
    rw [hA3def]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-1) hsumRadMem
  have husm : Work.FTS.EllipticEst.SmoothOpen u := by
    rw [hudef]
    exact Work.FTS.EllipticEst.smoothOpen_add (hA1sm.const_mul' (-3))
      (Work.FTS.EllipticEst.smoothOpen_add (hA2sm.const_mul' (-α)) hA3sm)
  have humem : Work.Spaces.HkMem α 4 u := by
    rw [hudef]
    exact Work.FTS.EllipticEst.HkMem_add_open (hA1sm.const_mul' (-3))
      (Work.FTS.EllipticEst.smoothOpen_add (hA2sm.const_mul' (-α)) hA3sm)
      (Work.FTS.LocData.HkMem_const_mul α 4 (-3) hA1mem')
      (Work.FTS.EllipticEst.HkMem_add_open (hA2sm.const_mul' (-α)) hA3sm
        (Work.FTS.LocData.HkMem_const_mul α 4 (-α) hA2mem')
        hA3mem)
  -- ## the pointwise identity
  have hqid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Ψ) z θ / Real.sin (2 * θ)
        = u z θ := by
    intro z θ hz hθ hlt
    have h := Work.FTS.EllSol.EllPkgAux.uopPointwiseId α g Ψ hα hα1 hC hsmΦ z θ hz hθ hlt
    have h2 : u z θ = -3 * (X z θ / Real.sin (2 * θ))
        - α * (Work.Spaces.Dz X z θ / Real.sin (2 * θ))
        - (2 * Gb z + (3 / 4) * Fs z) := by
      rw [hudef, hA1def, hA2def, hA3def, hXdef, hGbdef, hFsdef]
      ring
    rw [h2]
    simpa only [hXdef, hGbdef, hFsdef] using h
  have hqid' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ) z θ / Work.Construction.s2 θ
        = u z θ := by
    intro z θ hz hθ hlt
    have h1 : Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ) z θ
          / Work.Construction.s2 θ
        = Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Ψ) z θ
          / Real.sin (2 * θ) := by
      rw [Work.FTS.EllipticEst.PhiTil_eq_EllResid]
      rfl
    rw [h1]
    exact hqid z θ hz hθ hlt
  -- ## membership, smoothness and norm of the target
  have hQmem : Work.Spaces.HkMem α 4 (fun z θ =>
      Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ) z θ / Work.Construction.s2 θ) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 humem
      (fun z hz θ hθ => (hqid' z θ hz hθ.1 hθ.2).symm)
  have hQsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ) z θ / Work.Construction.s2 θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl husm
      (fun z θ hz hθ hlt => (hqid' z θ hz hθ hlt).symm)
  have hQnormEq : Work.Spaces.HkNorm α 4 (fun z θ =>
      Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ) z θ / Work.Construction.s2 θ)
      = Work.Spaces.HkNorm α 4 u := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm,
      Work.FTS.EllipticEst.HkSq_congr_open α 4
        (f := fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ) z θ
          / Work.Construction.s2 θ) (g := u)
        (fun z θ hz hθ hlt => hqid' z θ hz hθ hlt)]
  -- ## the norm bound
  set R : ℝ := α ^ 2 * Work.Spaces.HkNorm α 4
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ)
      + Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 X)
      + Work.Spaces.HkNorm α 4 g with hRdef
  have hN1 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 4
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) := Real.sqrt_nonneg _
  have hN2 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 X) := Real.sqrt_nonneg _
  have hNg : (0 : ℝ) ≤ Work.Spaces.HkNorm α 4 g := Real.sqrt_nonneg _
  have hR0 : 0 ≤ R := by rw [hRdef]; nlinarith [hN1, hN2, hNg, sq_nonneg α]
  have hP_R : Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 X) ≤ R := by
    rw [hRdef]; nlinarith [hN1, hN2, hNg, sq_nonneg α]
  have hg_R : Work.Spaces.HkNorm α 4 g ≤ R := by rw [hRdef]; nlinarith [hN1, hN2, hNg]
  have hterm1 : Work.Spaces.HkNorm α 4 A1 ≤ (Cdiv * CD) * R := by
    calc Work.Spaces.HkNorm α 4 A1 ≤ Cdiv * Work.Spaces.HkNorm α 4 (Work.Spaces.pth X) := hA1le
      _ ≤ Cdiv * (CD * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 X)) :=
          mul_le_mul_of_nonneg_left hXpthnorm hCdivpos.le
      _ = (Cdiv * CD) * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 X) := by ring
      _ ≤ (Cdiv * CD) * R := mul_le_mul_of_nonneg_left hP_R (by positivity)
  have hstep : α ^ 2 * Work.Spaces.HkNorm α 4 (Work.Spaces.DzIter 2 X)
        + Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 X)
        + α * Work.Spaces.HkNorm α 4 (Work.Spaces.Dz X) ≤ (2 * CD + 1) * R := by
    have h1 : α ^ 2 * Work.Spaces.HkNorm α 4 (Work.Spaces.DzIter 2 X) ≤ CD * R := by
      refine le_trans hDz2Xle ?_
      rw [hRdef]
      refine mul_le_mul_of_nonneg_left ?_ hCDpos.le
      linarith [hNg]
    have h3 : α * Work.Spaces.HkNorm α 4 (Work.Spaces.Dz X) ≤ CD * R := by
      refine le_trans hDzXle ?_
      rw [hRdef]
      refine mul_le_mul_of_nonneg_left ?_ hCDpos.le
      linarith [hNg]
    nlinarith [h1, h3, hP_R, hR0, hCDpos]
  have hterm2 : α * Work.Spaces.HkNorm α 4 A2 ≤ (Cdiv * Cw * (2 * CD + 1)) * R := by
    calc α * Work.Spaces.HkNorm α 4 A2
        ≤ Cdiv * (α * Work.Spaces.HkNorm α 4 (Work.Spaces.Dz (Work.Spaces.pth X))) := by
          rw [hA2def]; exact hA2alpha
      _ ≤ Cdiv * (Cw * (α ^ 2 * Work.Spaces.HkNorm α 4 (Work.Spaces.DzIter 2 X)
            + Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 X)
            + α * Work.Spaces.HkNorm α 4 (Work.Spaces.Dz X))) :=
          mul_le_mul_of_nonneg_left hDzpthle hCdivpos.le
      _ ≤ Cdiv * (Cw * ((2 * CD + 1) * R)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep hCwpos.le) hCdivpos.le
      _ = (Cdiv * Cw * (2 * CD + 1)) * R := by ring
  have hGbSinN : Work.Spaces.HkNorm α 4 (fun z θ => Gb z * Real.sin (2 * θ))
      ≤ Cgb * Work.Spaces.HkNorm α 4 g := by
    simpa only [hGbdef] using hgb α g hα hα1 hC.reg.forall hgk
  have hFsSinN : Work.Spaces.HkNorm α 4 (fun z θ => Fs z * Real.sin (2 * θ))
      ≤ Cfs * Work.Spaces.HkNorm α 4 g := by
    simpa only [hFsdef] using hfs α g hα hα1 hC.reg.forall hgk
  have hGbn : Work.Spaces.HkNorm α 4 (fun z θ => Gb z)
      ≤ Crad * (Cgb * Work.Spaces.HkNorm α 4 g) := by
    calc Work.Spaces.HkNorm α 4 (fun z θ => Gb z)
        ≤ Crad * Work.Spaces.HkNorm α 4 (fun z θ => Gb z * Real.sin (2 * θ)) :=
          hrad α Gb hα hα4 hGbsm
      _ ≤ Crad * (Cgb * Work.Spaces.HkNorm α 4 g) :=
          mul_le_mul_of_nonneg_left hGbSinN hCradpos.le
  have hFsn : Work.Spaces.HkNorm α 4 (fun z θ => Fs z)
      ≤ Crad * (Cfs * Work.Spaces.HkNorm α 4 g) := by
    calc Work.Spaces.HkNorm α 4 (fun z θ => Fs z)
        ≤ Crad * Work.Spaces.HkNorm α 4 (fun z θ => Fs z * Real.sin (2 * θ)) :=
          hrad α Fs hα hα4 hC.fsm
      _ ≤ Crad * (Cfs * Work.Spaces.HkNorm α 4 g) :=
          mul_le_mul_of_nonneg_left hFsSinN hCradpos.le
  have hterm3 : Work.Spaces.HkNorm α 4 A3 ≤ K3 * R := by
    have hA3eq : Work.Spaces.HkNorm α 4 A3
        = Work.Spaces.HkNorm α 4 (fun z θ => 2 * Gb z + (3 / 4) * Fs z) := by
      rw [hA3def, Work.FTS.EllipticEst.HkNorm_const_mul α 4 (-1) hsumRadSm.forall]
      norm_num
    have hsumN : Work.Spaces.HkNorm α 4 (fun z θ => 2 * Gb z + (3 / 4) * Fs z)
        ≤ Real.sqrt 2 * (2 * Work.Spaces.HkNorm α 4 (fun z θ => Gb z)
            + (3 / 4) * Work.Spaces.HkNorm α 4 (fun z θ => Fs z)) := by
      have h1 := Work.FTS.EllipticEst.HkNorm_add_le (α := α) (k := 4)
        (f := fun z θ => (2 : ℝ) * Gb z) (g := fun z θ => (3 / 4 : ℝ) * Fs z)
        (hGbsmOpen.const_mul' 2).forall (hFssmOpen.const_mul' (3 / 4)).forall
        (Work.FTS.LocData.HkMem_const_mul α 4 2 hGbRad)
        (Work.FTS.LocData.HkMem_const_mul α 4 (3 / 4) hFsRad)
      have h2 : Work.Spaces.HkNorm α 4 (fun z θ => (2 : ℝ) * Gb z)
          = 2 * Work.Spaces.HkNorm α 4 (fun z θ => Gb z) := by
        rw [Work.FTS.EllipticEst.HkNorm_const_mul α 4 2 hGbsmOpen.forall]
        norm_num
      have h3 : Work.Spaces.HkNorm α 4 (fun z θ => (3 / 4 : ℝ) * Fs z)
          = (3 / 4) * Work.Spaces.HkNorm α 4 (fun z θ => Fs z) := by
        rw [Work.FTS.EllipticEst.HkNorm_const_mul α 4 (3 / 4) hFssmOpen.forall]
        norm_num
      rw [h2, h3] at h1
      exact h1
    calc Work.Spaces.HkNorm α 4 A3
        = Work.Spaces.HkNorm α 4 (fun z θ => 2 * Gb z + (3 / 4) * Fs z) := hA3eq
      _ ≤ Real.sqrt 2 * (2 * Work.Spaces.HkNorm α 4 (fun z θ => Gb z)
            + (3 / 4) * Work.Spaces.HkNorm α 4 (fun z θ => Fs z)) := hsumN
      _ ≤ Real.sqrt 2 * (2 * (Crad * (Cgb * Work.Spaces.HkNorm α 4 g))
            + (3 / 4) * (Crad * (Cfs * Work.Spaces.HkNorm α 4 g))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
          have ha : 2 * Work.Spaces.HkNorm α 4 (fun z θ => Gb z)
              ≤ 2 * (Crad * (Cgb * Work.Spaces.HkNorm α 4 g)) :=
            mul_le_mul_of_nonneg_left hGbn (by norm_num)
          have hb : (3 / 4) * Work.Spaces.HkNorm α 4 (fun z θ => Fs z)
              ≤ (3 / 4) * (Crad * (Cfs * Work.Spaces.HkNorm α 4 g)) :=
            mul_le_mul_of_nonneg_left hFsn (by norm_num)
          linarith
      _ ≤ K3 * R := by
        have h : K3 * Work.Spaces.HkNorm α 4 g ≤ K3 * R :=
          mul_le_mul_of_nonneg_left hg_R hK3pos.le
        have heq : Real.sqrt 2 * (2 * (Crad * (Cgb * Work.Spaces.HkNorm α 4 g))
            + (3 / 4) * (Crad * (Cfs * Work.Spaces.HkNorm α 4 g)))
            = K3 * Work.Spaces.HkNorm α 4 g := by
          rw [hK3]; ring
        rw [heq]; exact h
  have hmain : Work.Spaces.HkNorm α 4 u ≤ K * R := by
    have htri1 := Work.FTS.EllipticEst.HkNorm_add_le (α := α) (k := 4)
      (f := fun z θ => (-3 : ℝ) * A1 z θ) (g := fun z θ => (-α) * A2 z θ + A3 z θ)
      (hA1sm.const_mul' (-3)).forall
      (Work.FTS.EllipticEst.smoothOpen_add (hA2sm.const_mul' (-α)) hA3sm).forall
      (Work.FTS.LocData.HkMem_const_mul α 4 (-3) hA1mem')
      (Work.FTS.EllipticEst.HkMem_add_open (hA2sm.const_mul' (-α)) hA3sm
        (Work.FTS.LocData.HkMem_const_mul α 4 (-α) hA2mem') hA3mem)
    have htri2 := Work.FTS.EllipticEst.HkNorm_add_le (α := α) (k := 4)
      (f := fun z θ => (-α) * A2 z θ) (g := A3)
      (hA2sm.const_mul' (-α)).forall hA3sm.forall
      (Work.FTS.LocData.HkMem_const_mul α 4 (-α) hA2mem') hA3mem
    have hn3 : Work.Spaces.HkNorm α 4 (fun z θ => (-3 : ℝ) * A1 z θ)
        = 3 * Work.Spaces.HkNorm α 4 A1 := by
      rw [Work.FTS.EllipticEst.HkNorm_const_mul α 4 (-3) hA1sm.forall]
      norm_num
    have hna : Work.Spaces.HkNorm α 4 (fun z θ => (-α) * A2 z θ)
        = α * Work.Spaces.HkNorm α 4 A2 := by
      rw [Work.FTS.EllipticEst.HkNorm_const_mul α 4 (-α) hA2sm.forall, abs_neg,
        abs_of_nonneg hα.le]
    have hnub : Work.Spaces.HkNorm α 4 (fun z θ => (-α) * A2 z θ + A3 z θ)
        ≤ Real.sqrt 2 * (α * Work.Spaces.HkNorm α 4 A2 + Work.Spaces.HkNorm α 4 A3) := by
      refine le_trans htri2 (le_of_eq ?_)
      rw [hna]
    have h1 : Work.Spaces.HkNorm α 4 u
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 (fun z θ => (-3 : ℝ) * A1 z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => (-α) * A2 z θ + A3 z θ)) := by
      rw [hudef]; exact htri1
    have h2 : Real.sqrt 2 * (Work.Spaces.HkNorm α 4 (fun z θ => (-3 : ℝ) * A1 z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => (-α) * A2 z θ + A3 z θ))
        ≤ Real.sqrt 2 * (3 * Work.Spaces.HkNorm α 4 A1
            + Real.sqrt 2 * (α * Work.Spaces.HkNorm α 4 A2 + Work.Spaces.HkNorm α 4 A3)) := by
      rw [hn3]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
      linarith [hnub]
    have h3 : Real.sqrt 2 * (3 * Work.Spaces.HkNorm α 4 A1
            + Real.sqrt 2 * (α * Work.Spaces.HkNorm α 4 A2 + Work.Spaces.HkNorm α 4 A3))
        ≤ Real.sqrt 2 * (3 * ((Cdiv * CD) * R)
            + Real.sqrt 2 * ((Cdiv * Cw * (2 * CD + 1)) * R + K3 * R)) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
      have h1' : 3 * Work.Spaces.HkNorm α 4 A1 ≤ 3 * ((Cdiv * CD) * R) :=
        mul_le_mul_of_nonneg_left hterm1 (by norm_num)
      have h2' : α * Work.Spaces.HkNorm α 4 A2 + Work.Spaces.HkNorm α 4 A3
          ≤ (Cdiv * Cw * (2 * CD + 1)) * R + K3 * R := by
        linarith [hterm2, hterm3]
      have h2'' : Real.sqrt 2 * (α * Work.Spaces.HkNorm α 4 A2 + Work.Spaces.HkNorm α 4 A3)
          ≤ Real.sqrt 2 * ((Cdiv * Cw * (2 * CD + 1)) * R + K3 * R) :=
        mul_le_mul_of_nonneg_left h2' (Real.sqrt_nonneg 2)
      linarith [h1', h2'']
    have h4 : Real.sqrt 2 * (3 * ((Cdiv * CD) * R)
            + Real.sqrt 2 * ((Cdiv * Cw * (2 * CD + 1)) * R + K3 * R))
        = (Real.sqrt 2 * (3 * (Cdiv * CD)
            + Real.sqrt 2 * (Cdiv * Cw * (2 * CD + 1) + K3))) * R := by ring
    rw [h4] at h3
    have h5 : (Real.sqrt 2 * (3 * (Cdiv * CD)
            + Real.sqrt 2 * (Cdiv * Cw * (2 * CD + 1) + K3))) * R
        ≤ (Real.sqrt 2 * (3 * (Cdiv * CD)
            + Real.sqrt 2 * (Cdiv * Cw * (2 * CD + 1) + K3)) + 1) * R := by
      nlinarith [hR0]
    have h6 : (Real.sqrt 2 * (3 * (Cdiv * CD)
            + Real.sqrt 2 * (Cdiv * Cw * (2 * CD + 1) + K3)) + 1) * R = K * R := by
      rw [hK]
    rw [h6] at h5
    exact le_trans h1 (le_trans h2 (le_trans h3 h5))
  refine ⟨⟨hQsm, hQmem⟩, ?_⟩
  refine le_trans (le_of_eq hQnormEq) ?_
  refine le_trans hmain ?_
  rw [hRdef, hXdef]

end Work.FTS.EllSol.EllPkgAux
