import Mathlib
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.fold_theta_coord
import Submission.Work.FoldInst.fold_theta_orthant
import Submission.Work.FoldInst.foldPsi_continuousOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

/-- The Klein sign-change action preserves the open unit ball (it is a coordinate sign change). -/
theorem ball_act (g : Fin 4 → ZMod 2) {y : E4} (hy : y ∈ HypModel.ball) :
    act g y ∈ HypModel.ball := by
  have h := one_sub_norm_sq_act g y
  rw [HypModel.ball, Set.mem_ofPred_eq] at hy ⊢
  nlinarith [norm_nonneg y, norm_nonneg (act g y), h]

theorem Qbar_of_mem_VoronoiOpen_root (i : Fin 98) {y : Work.FoldInst.E4}
    (hyV : y ∈ Work.FoldInst.VoronoiOpen i (fun _ : Fin (Work.FoldInst.foldCodim i) => false))
    (hyb : y ∈ Work.HypModel.ball)
    (hyθ : Work.FoldInst.foldTheta i (fun _ : Fin (Work.FoldInst.foldCodim i) => false) y ∈
      Work.Fold.posOrthant (Work.FoldInst.foldCodim i)) :
    y ∈ Work.FoldInst.Qbar := by
  change (∀ S : Fin 24, 0 ≤ sideSlack S y) ∧ (∀ w : Fin 24, 0 ≤ truncSlack w y)
  refine ⟨fun S => ?_, fun w => ?_⟩
  · by_cases hS : ∃ t : Fin (foldCodim i), foldWalls i (fun _ => false) t = S
    · obtain ⟨t, rfl⟩ := hS
      have hθt : 0 ≤ (foldTheta i (fun _ : Fin (foldCodim i) => false) y)
          (⟨t, by have := t.isLt; have := foldCodim_le i; omega⟩ : Fin 4) :=
        (Work.Fold.mem_posOrthant_iff.mp hyθ) _
          (by have := t.isLt; have := foldCodim_le i; omega)
      have hsqrt : 0 < Real.sqrt (1 - ‖y‖ ^ 2) := by
        refine Real.sqrt_pos.mpr ?_
        have h1 : ‖y‖ < 1 := hyb
        nlinarith [norm_nonneg y]
      have hH : 0 < (HypModel.mobiusKlein (foldNr i)
          (act (toG (foldKr i (fun _ => false))) y)) 3 :=
        HypModel.mobiusKlein_mem (FoldThetaOrthantAux.foldNr_isLorentz i) (ball_act _ hyb)
      have hcoord := fold_theta_coord i (fun _ : Fin (foldCodim i) => false) y hyb t
      have hsign : (if (fun _ : Fin (foldCodim i) => false) t then (-1 : ℝ) else 1) = 1 := by
        simp
      rw [hsign, one_mul] at hcoord
      have hL : 0 ≤ Real.sqrt (1 - ‖y‖ ^ 2) *
          (foldTheta i (fun _ : Fin (foldCodim i) => false) y)
            (⟨t, by have := t.isLt; have := foldCodim_le i; omega⟩ : Fin 4) :=
        mul_nonneg (le_of_lt hsqrt) hθt
      rw [hcoord] at hL
      exact (mul_nonneg_iff_of_pos_right hH).mp hL
    · exact le_of_lt (hyV.1 S (fun t ht => hS ⟨t, ht⟩)).1
  · exact le_of_lt (hyV.2 w).1

end Work.FoldInst
