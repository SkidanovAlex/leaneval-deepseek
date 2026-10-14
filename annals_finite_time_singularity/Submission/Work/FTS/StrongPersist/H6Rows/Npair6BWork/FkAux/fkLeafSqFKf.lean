import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingSup
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkPsi6TermBound
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowDthTopRow
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkStarPieces
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumGamSin
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.NS6.Pieces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Row6.NS6

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

variable {α Ce Cs : ℝ} {f Ef Φs : Fn}

theorem piece0 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 0) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 0) := by
  refine piece_both (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      * (2 * (z / (1 + z) * Work.Construction.Fstar α z θ))) _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_mul D.hR1c (cd6_const_mul 2 (D.hSh1s.forall 6))
  · exact Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 D.hα D.hα1
      D.hR1c D.hR1w (cd6_const_mul 2 (D.hSh1s.forall 6))
      (Work.FTS.LocData.HkMem_const_mul α 6 2 D.hSh1m)
  · show ((z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ)
        * (2 * (z / (1 + z) * Work.Construction.Fstar α z θ))
      = 2 * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        * Work.Construction.Fstar α z θ
    exact shift_mul 2 _ _ z (ne_zero_of_mem hzθ) (ne_add_one_of_mem hzθ)

theorem piece1 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 1) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 1) := by
  refine piece_both (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      * (2 * (z / (1 + z) * f z θ))) _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_mul D.hR1c (cd6_const_mul 2 D.hSh4s)
  · exact Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 D.hα D.hα1
      D.hR1c D.hR1w (cd6_const_mul 2 D.hSh4s)
      (Work.FTS.LocData.HkMem_const_mul α 6 2 D.hSh4m)
  · show ((z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ)
        * (2 * (z / (1 + z) * f z θ))
      = 2 * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ * f z θ
    exact shift_mul 2 _ _ z (ne_zero_of_mem hzθ) (ne_add_one_of_mem hzθ)

theorem piece2 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 2) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 2) := by
  refine piece_both (fun z θ => Work.Construction.Fstar α z θ
      * (2 * Work.Construction.Rop α (Work.Construction.PhiTil α f Ef) z θ))
    _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_mul D.hS1c (cd6_const_mul 2 D.hR2c)
  · exact Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 D.hα D.hα1
      D.hS1c D.hS1w (cd6_const_mul 2 D.hR2c)
      (Work.FTS.LocData.HkMem_const_mul α 6 2 D.hR2m)
  · show Work.Construction.Fstar α z θ
        * (2 * Work.Construction.Rop α (Work.Construction.PhiTil α f Ef) z θ)
      = 2 * Work.Construction.Rop α (Work.Construction.PhiTil α f Ef) z θ
        * Work.Construction.Fstar α z θ
    ring

theorem piece3 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 3) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 3) := by
  refine piece_both (fun z θ => (2 * Work.Construction.Rop α (Work.Construction.PhiTil α f Ef)
      z θ) * f z θ) _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_mul (cd6_const_mul 2 D.hR2c) D.hfcd
  · exact D.mulSm (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α f Ef)
        z θ) f (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul 2 D.hR2s)
      (Work.FTS.LocData.HkMem_const_mul α 6 2 D.hR2m) D.fsm D.fm
  · show (2 * Work.Construction.Rop α (Work.Construction.PhiTil α f Ef) z θ) * f z θ
      = 2 * Work.Construction.Rop α (Work.Construction.PhiTil α f Ef) z θ * f z θ
    ring

theorem piece4 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 4) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 4) := by
  refine piece_both (fun z θ => (z + 1) / z
        * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ)
      * (-2 * (z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)))
    _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_mul D.hU1c (cd6_const_mul (-2) (D.hSh2s.forall 6))
  · exact Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 D.hα D.hα1
      D.hU1c D.hU1w (cd6_const_mul (-2) (D.hSh2s.forall 6))
      (Work.FTS.LocData.HkMem_const_mul α 6 (-2) D.hSh2m)
  · show ((z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
          / Work.Construction.s2 θ))
        * (-2 * (z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ))
      = -2 * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
          / Work.Construction.s2 θ) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ
    exact shift_mul (-2) _ _ z (ne_zero_of_mem hzθ) (ne_add_one_of_mem hzθ)

theorem piece5 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 5) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 5) := by
  refine piece_both (fun z θ => (z + 1) / z
        * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ)
      * (-2 * (z / (1 + z) * Work.Spaces.Dth f z θ))) _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_mul D.hU1c (cd6_const_mul (-2) D.hSh5s)
  · exact Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 D.hα D.hα1
      D.hU1c D.hU1w (cd6_const_mul (-2) D.hSh5s)
      (Work.FTS.LocData.HkMem_const_mul α 6 (-2) D.hSh5m)
  · show ((z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
          / Work.Construction.s2 θ))
        * (-2 * (z / (1 + z) * Work.Spaces.Dth f z θ))
      = -2 * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
          / Work.Construction.s2 θ) * Work.Spaces.Dth f z θ
    exact shift_mul (-2) _ _ z (ne_zero_of_mem hzθ) (ne_add_one_of_mem hzθ)

theorem piece6 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 6) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 6) := by
  refine piece_both (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
      * (-2 * (Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
        / Work.Construction.s2 θ))) _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_mul D.hS2c (cd6_const_mul (-2) D.hU2c)
  · exact Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 D.hα D.hα1
      D.hS2c D.hS2w (cd6_const_mul (-2) D.hU2c)
      (Work.FTS.LocData.HkMem_const_mul α 6 (-2) D.hU2m)
  · show Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        * (-2 * (Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
          / Work.Construction.s2 θ))
      = -2 * (Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
          / Work.Construction.s2 θ) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ
    ring

theorem piece7 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 7) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 7) := by
  refine piece_both (fun z θ => (-2 * (Work.Construction.Uop α (Work.Construction.PhiTil α f Ef)
      z θ / Work.Construction.s2 θ)) * Work.Spaces.Dth f z θ) _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_mul (cd6_const_mul (-2) D.hU2c) D.hTfcd
  · exact D.mulSm (fun z θ => -2 * (Work.Construction.Uop α (Work.Construction.PhiTil α f Ef)
        z θ / Work.Construction.s2 θ)) (Work.Spaces.Dth f)
      (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (-2) D.hU2s)
      (Work.FTS.LocData.HkMem_const_mul α 6 (-2) D.hU2m) D.fsm.Dth D.hTfm
  · show (-2 * (Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
          / Work.Construction.s2 θ)) * Work.Spaces.Dth f z θ
      = -2 * (Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
          / Work.Construction.s2 θ) * Work.Spaces.Dth f z θ
    ring

theorem piece8 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 8) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 8) := by
  refine piece_both (fun z θ => ((z + 1) / z
        * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ)
      * ((-2 * α) * (z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)))
    _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_mul D.hV1zc (cd6_const_mul (-2 * α) (D.hSh3s.forall 6))
  · exact Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 D.hα D.hα1
      D.hV1zc D.hV1zw (cd6_const_mul (-2 * α) (D.hSh3s.forall 6))
      (Work.FTS.LocData.HkMem_const_mul α 6 (-2 * α) D.hSh3m)
  · show ((z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ)
        * ((-2 * α) * (z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ))
      = -2 * α * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
        * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
    exact shift_mul (-2 * α) _ _ z (ne_zero_of_mem hzθ) (ne_add_one_of_mem hzθ)

theorem piece9 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 9) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 9) := by
  refine piece_both (fun z θ => ((z + 1) / z
        * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ)
      * ((-2 * α) * (z / (1 + z) * Work.Spaces.Dz f z θ))) _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_mul D.hV1zc (cd6_const_mul (-2 * α) D.hSh6s)
  · exact Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 D.hα D.hα1
      D.hV1zc D.hV1zw (cd6_const_mul (-2 * α) D.hSh6s)
      (Work.FTS.LocData.HkMem_const_mul α 6 (-2 * α) D.hSh6m)
  · show ((z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ)
        * ((-2 * α) * (z / (1 + z) * Work.Spaces.Dz f z θ))
      = -2 * α * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
        * Work.Spaces.Dz f z θ
    exact shift_mul (-2 * α) _ _ z (ne_zero_of_mem hzθ) (ne_add_one_of_mem hzθ)

theorem piece10 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 10) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 10) := by
  refine piece_both (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      * ((-2 * α) * Work.Construction.Vop (Work.Construction.PhiTil α f Ef) z θ))
    _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_mul D.hS3c (cd6_const_mul (-2 * α) D.hV2c)
  · exact Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 D.hα D.hα1
      D.hS3c D.hS3w (cd6_const_mul (-2 * α) D.hV2c)
      (Work.FTS.LocData.HkMem_const_mul α 6 (-2 * α) D.hV2m)
  · show Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        * ((-2 * α) * Work.Construction.Vop (Work.Construction.PhiTil α f Ef) z θ)
      = -2 * α * Work.Construction.Vop (Work.Construction.PhiTil α f Ef) z θ
        * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
    ring

theorem piece11 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 11) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 11) := by
  refine piece_both (fun z θ => ((-2 * α) * Work.Construction.Vop
      (Work.Construction.PhiTil α f Ef) z θ) * Work.Spaces.Dz f z θ) _ ?_ ?_
    (fun z θ hzθ => ?_)
  · exact cd6_mul (cd6_const_mul (-2 * α) D.hV2c) D.hTzcd
  · exact D.mulSm (fun z θ => (-2 * α) * Work.Construction.Vop (Work.Construction.PhiTil α f Ef)
        z θ) (Work.Spaces.Dz f)
      (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (-2 * α) D.hV2s)
      (Work.FTS.LocData.HkMem_const_mul α 6 (-2 * α) D.hV2m) D.fsm.Dz D.hTzm
  · show ((-2 * α) * Work.Construction.Vop (Work.Construction.PhiTil α f Ef) z θ)
        * Work.Spaces.Dz f z θ
      = -2 * α * Work.Construction.Vop (Work.Construction.PhiTil α f Ef) z θ
        * Work.Spaces.Dz f z θ
    ring

theorem piece12 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 12) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 12) := by
  refine piece_both (fun z θ => ((-α) / (1 + z))
      * (z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)) _ ?_ ?_
    (fun z θ hzθ => ?_)
  · exact cd6_mul D.hKinc (D.hSh2s.forall 6)
  · exact Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 D.hα D.hα1
      D.hKinc D.hKinw (D.hSh2s.forall 6) D.hSh2m
  · show ((-α) / (1 + z)) * (z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
      = -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z * Work.Spaces.Dth (Work.Construction.Fstar α) z θ
    rw [Work.FTS.Nonlin.FK_Fstar D.hα D.hα1]
    exact shift_fk α _ z (ne_add_one_of_mem hzθ)

theorem piece13 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 13) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 13) := by
  refine piece_both (fun z θ => ((-α) / (1 + z))
      * (z / (1 + z) * Work.Spaces.Dth f z θ)) _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_mul D.hKinc D.hSh5s
  · exact Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 D.hα D.hα1
      D.hKinc D.hKinw D.hSh5s D.hSh5m
  · show ((-α) / (1 + z)) * (z / (1 + z) * Work.Spaces.Dth f z θ)
      = -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z * Work.Spaces.Dth f z θ
    rw [Work.FTS.Nonlin.FK_Fstar D.hα D.hα1]
    exact shift_fk α _ z (ne_add_one_of_mem hzθ)

theorem piece14 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 14) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 14) := by
  refine piece_both (fun z θ => (-(1 / 2)) * (Work.Construction.FK f z
      * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)) _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_const_mul (-(1 / 2)) (cd6_mul D.hKfcd D.hS2c)
  · exact Work.FTS.LocData.HkMem_const_mul α 6 (-(1 / 2)) D.fk7.2.2.2.1
  · show (-(1 / 2)) * (Work.Construction.FK f z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
      = -(1 / 2) * Work.Construction.FK f z * Work.Spaces.Dth (Work.Construction.Fstar α) z θ
    ring

theorem piece15 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 15) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 15) := by
  refine piece_both (fun z θ => (-(1 / 2)) * (Work.Construction.FK f z
      * Work.Spaces.Dth f z θ)) _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_const_mul (-(1 / 2)) (cd6_mul D.hKfcd D.hTfcd)
  · exact Work.FTS.LocData.HkMem_const_mul α 6 (-(1 / 2)) D.fk7.2.1
  · show (-(1 / 2)) * (Work.Construction.FK f z * Work.Spaces.Dth f z θ)
      = -(1 / 2) * Work.Construction.FK f z * Work.Spaces.Dth f z θ
    ring

theorem piece16 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 16) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 16) := by
  refine piece_both (fun z θ => ((-2 * α) / (1 + z))
      * (Real.sin θ ^ 2 * (z / (1 + z) * Work.Construction.Fstar α z θ))) _ ?_ ?_
    (fun z θ hzθ => ?_)
  · exact cd6_mul D.hKin2c (cd6_mul cd6_sinSq (D.hSh1s.forall 6))
  · exact Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 D.hα D.hα1
      D.hKin2c D.hKin2w (cd6_mul cd6_sinSq (D.hSh1s.forall 6))
      (Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 D.hα D.hα1
        cd6_sinSq D.hSqW (D.hSh1s.forall 6) D.hSh1m)
  · show ((-2 * α) / (1 + z)) * (Real.sin θ ^ 2
        * (z / (1 + z) * Work.Construction.Fstar α z θ))
      = -(Real.sin θ ^ 2) * Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ
    rw [Work.FTS.Nonlin.FK_Fstar D.hα D.hα1]
    exact shift_fk_sq2 α _ _ z (ne_add_one_of_mem hzθ)

theorem piece17 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 17) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 17) := by
  refine piece_both (fun z θ => ((-2 * α) / (1 + z))
      * (Real.sin θ ^ 2 * (z / (1 + z) * f z θ))) _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_mul D.hKin2c (cd6_mul cd6_sinSq D.hSh4s)
  · exact Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 D.hα D.hα1
      D.hKin2c D.hKin2w (cd6_mul cd6_sinSq D.hSh4s)
      (Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 D.hα D.hα1
        cd6_sinSq D.hSqW D.hSh4s D.hSh4m)
  · show ((-2 * α) / (1 + z)) * (Real.sin θ ^ 2 * (z / (1 + z) * f z θ))
      = -(Real.sin θ ^ 2) * Work.Construction.FK (Work.Construction.Fstar α) z * f z θ
    rw [Work.FTS.Nonlin.FK_Fstar D.hα D.hα1]
    exact shift_fk_sq2 α _ _ z (ne_add_one_of_mem hzθ)

theorem piece18 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 18) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 18) := by
  refine piece_both (fun z θ => (-1) * (Real.sin θ ^ 2 * Work.Construction.FK f z
      * Work.Construction.Fstar α z θ)) _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_const_mul (-1) (cd6_mul (cd6_mul cd6_sinSq D.hKfcd) D.hS1c)
  · exact Work.FTS.LocData.HkMem_const_mul α 6 (-1) D.fk7.2.2.2.2.2.2
  · show (-1) * (Real.sin θ ^ 2 * Work.Construction.FK f z
        * Work.Construction.Fstar α z θ)
      = -(Real.sin θ ^ 2) * Work.Construction.FK f z * Work.Construction.Fstar α z θ
    ring

theorem piece19 (D : Data α Ce Cs f Ef Φs) :
    CD6 (pcs α f Ef Φs 19) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs 19) := by
  refine piece_both (fun z θ => (-1) * (Real.sin θ ^ 2 * Work.Construction.FK f z
      * f z θ)) _ ?_ ?_ (fun z θ hzθ => ?_)
  · exact cd6_const_mul (-1) (cd6_mul (cd6_mul cd6_sinSq D.hKfcd) D.hfcd)
  · exact Work.FTS.LocData.HkMem_const_mul α 6 (-1) D.fk7.2.2.2.2.1
  · show (-1) * (Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ)
      = -(Real.sin θ ^ 2) * Work.Construction.FK f z * f z θ
    ring

/-- **All twenty pieces** are `C⁶` on the open quadrant and honest in `ℋ⁶`. -/
theorem pieces (D : Data α Ce Cs f Ef Φs) :
    ∀ k : ℕ, k < 20 → CD6 (pcs α f Ef Φs k) ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs k) := by
  have h0 := piece0 D
  have h1 := piece1 D
  have h2 := piece2 D
  have h3 := piece3 D
  have h4 := piece4 D
  have h5 := piece5 D
  have h6 := piece6 D
  have h7 := piece7 D
  have h8 := piece8 D
  have h9 := piece9 D
  have h10 := piece10 D
  have h11 := piece11 D
  have h12 := piece12 D
  have h13 := piece13 D
  have h14 := piece14 D
  have h15 := piece15 D
  have h16 := piece16 D
  have h17 := piece17 D
  have h18 := piece18 D
  have h19 := piece19 D
  intro k hk
  interval_cases k <;> assumption

end Work.FTS.StrongPersist.H6Row6.NS6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkLeafSqFKf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 3200000

/-! ## The dominating function on the radial line

`G z = Σ_{b ≤ 6} (D_z^b (FK f)(z))² · ∫_θ HkIntegrand α (6-b) f (z,θ)`: the matched
(releveled) majorant of the level-six integrand of the product `(FK f) · f`, integrated over
the angle.  The three analytic inputs of the crux are

* `fkMulHkSqSliceLe` — the pointwise-in-`θ` matched majorant of `radialMatchedMajorant`,
  integrated over `θ` (a.e. in `z`);
* `fkPsi6TermBound` — integrability of each summand and the level-table bound
  `∫_z (D_z^b (FK f)(z))² · ∫_θ HkIntegrand α (6-b) f ≤ C M² |f|²_{ℋ⁶}`;
* `hkMem_fk_mul` — `(FK f) · f ∈ ℋ⁶` (honesty of the left-hand side).
-/



end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
