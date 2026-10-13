import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.EllipticEst.Core.i0Aux.Basic
import Submission.Work.EllipticEst.Core.i0Aux.Honest
import Submission.Work.EllipticEst.Core.i0Aux.i0_fubini_package
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.ClassC.NormPieces.prodIntegrableNonneg
import Submission.Work.Blocks.interp_amgm
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.TraceEngine

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! # Basic bookkeeping for `TraceEngine.slotBounds`

The domain facts, the commutativity of the iterates of `D_z` and the continuity of the
angular weight `w²·σ_η` on the open quadrant, all used by `slotBounds`. -/

theorem slotAux_measurableSet_dom : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
  measurableSet_Ici.prod measurableSet_Icc

theorem slotAux_volume_restrict_dom :
    (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
  (Measure.prod_restrict _ _).symm

/-- Almost every angle of `Iθ` is interior. -/
theorem slotAux_ae_mem_Ioo_Itheta :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  change ∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  rw [← Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- `D_z` commutes with its own iterates. -/
theorem slotAux_Dz_DzIter_comm (r : ℕ) (V : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (Work.Spaces.DzIter r V) = Work.Spaces.DzIter r (Work.Spaces.Dz V) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      show Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V))
        = Work.Spaces.Dz (Work.Spaces.DzIter r (Work.Spaces.Dz V))
      rw [ih]

/-- The iterates of `D_z` commute (they are all iterates of the same operator). -/
theorem slotAux_DzIter_comm (a b : ℕ) (V : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter a (Work.Spaces.DzIter b V)
      = Work.Spaces.DzIter b (Work.Spaces.DzIter a V) := by
  rw [← Work.Spaces.DzIter_add_right a b V, ← Work.Spaces.DzIter_add_right b a V,
    Nat.add_comm a b]

theorem slotAux_Dz_iter_comm_apply (r : ℕ) (V : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ
      = Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ :=
  congrFun (congrFun (slotAux_Dz_DzIter_comm r V) z) θ

theorem slotAux_DzIter_two_comm (r : ℕ) (V : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V)
      = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) := by
  have h1 : Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V)
      = Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V)) := rfl
  have h2 : Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V))
      = Work.Spaces.Dz (Work.Spaces.DzIter r (Work.Spaces.Dz V)) :=
    congrArg Work.Spaces.Dz (slotAux_Dz_DzIter_comm r V)
  have h3 : Work.Spaces.Dz (Work.Spaces.DzIter r (Work.Spaces.Dz V))
      = Work.Spaces.DzIter r (Work.Spaces.Dz (Work.Spaces.Dz V)) :=
    slotAux_Dz_DzIter_comm r (Work.Spaces.Dz V)
  have h4 : Work.Spaces.DzIter r (Work.Spaces.Dz (Work.Spaces.Dz V))
      = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) := rfl
  exact h1.trans (h2.trans (h3.trans h4))

theorem slotAux_DzIter_two_comm_apply (r : ℕ) (V : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ
      = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ :=
  congrFun (congrFun (slotAux_DzIter_two_comm r V) z) θ

theorem slotAux_pthIter_two_eq (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter 2 f = Work.Spaces.pth (Work.Spaces.pth f) := rfl

theorem slotAux_DzIter_two_eq (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter 2 f = Work.Spaces.Dz (Work.Spaces.Dz f) := rfl

/-- The weight `w²·σ_η` is continuous on the open quadrant. -/
theorem slotAux_continuousOn_w2_thEta :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    have h1 : (0 : ℝ) < p.2 := hp.2.1
    have h2 : p.2 < Real.pi / 2 := hp.2.2
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 := by
      funext p; simp only [Work.Spaces.w]
    rw [hfun]
    refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
    · exact (continuousOn_const.add continuousOn_fst).pow 2
    · exact continuousOn_fst.pow 2
    · intro p hp
      have hp1 : (0 : ℝ) < p.1 := hp.1
      exact pow_ne_zero 2 (ne_of_gt hp1)
  have hth : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    simp only [Work.FTS.EllipticEst.thEta]
    refine ContinuousOn.rpow_const ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    · intro p hp; exact Or.inl (ne_of_gt (hsinpos p hp))
  exact hw.mul hth

end Work.FTS.EllSol.PkgK5.TraceEngine
