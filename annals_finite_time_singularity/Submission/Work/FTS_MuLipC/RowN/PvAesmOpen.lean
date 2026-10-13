import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.meas_open
import Submission.Work.FTS.NonlinRows.Rl1.PvecMeasOpen
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.Pvec

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLipC.RowN

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin Work.Construction Work.Spaces
open Work.FTS.Nonlinear.Pieces.rl1Tools (aesm_congr aesm_mul aesm_const_mul aesm_neg
  aesm_s2_mul aesm_sinsq_mul aesm_FK aesm_Uop_of_div aesm_of_contOn_Qd
  aesm_F_ops QdMeas pv)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem PvAesmOpen {α Ce Cs : ℝ} {g Φs Ξg : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hα1 : α ≤ 1) (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Ξg) :
    ∀ k : Fin 20, MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun r θ => Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Ξg k r θ))
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  obtain ⟨hg', hpthg, hDzg, hDthg⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.aesm_f_ops_open hg
  obtain ⟨hF, hpthF, hDzF⟩ := aesm_F_ops α
  obtain ⟨hRopTg, hUopTg, hVopTg⟩ := Work.FTS.NonlinRows.Rl1.aesm_Tg_ops_open hell
  have hFKg : AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Construction.FK g z)) QdMeas := aesm_FK hg'
  have hFKF : AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z))
      QdMeas := aesm_FK hF
  obtain ⟨hRopTs, hUopTs, hVopTs⟩ :=
    Work.FTS.NonlinRows.Rl1.aesm_star_ops_open hα hα1 hs
  -- the twenty pieces of `pv`
  have hpiece : ∀ k : Fin 20, AEStronglyMeasurable (Function.uncurry (fun r θ =>
      Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Ξg k r θ)) QdMeas := by
    intro k
    fin_cases k
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α g Ξg) z θ * g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hg')) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α g Ξg) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hg')) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α g Ξg) z θ * pth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α g Ξg) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α g Ξg) z θ * Dz g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α g Ξg) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK g z * Dth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKg hDthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK g z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKg hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK (Fstar α) z * Dth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKF hDthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK (Fstar α) z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKF hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK g z * g z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKg hg'))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK g z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKg hF))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * g z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hg'))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hF))) (fun z θ => ?_)
      ring
  exact hpiece

end

end Work.FTS_MuLipC.RowN
