import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.ClassC.RopGen.sliceSecNonposBochner
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.Base
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `pureGamFamSix` — auxiliary lemmas

Helpers for `Work.FTS.StrongPersist.N6Trans.SixRoute.pureGamFamSix`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The open quadrant. -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- The product measure on the quadrant. -/
abbrev pm : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-! ## Continuity on the open quadrant -/

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) := by
  have h3 : (0 : ℝ) < 2 * θ := by linarith [hθ.1]
  have h4 : 2 * θ < Real.pi := by linarith [hθ.2, Real.pi_pos]
  exact Real.sin_pos_of_pos_of_lt_pi h3 h4

theorem continuousOn_sin_two_rpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd := by
  refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const ?_
  intro p hp
  exact Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo ⟨hp.2.1, hp.2.2⟩))

theorem continuousOn_w_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := rfl
  rw [hfun]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

theorem continuousOn_Wt_Qd (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := rfl
  rw [hfun]
  exact continuousOn_w_Qd.mul (continuousOn_sin_two_rpow_Qd _)





/-! ## Fubini for nonnegative functions on the quadrant -/


/-! ## The weight identities and comparisons -/

theorem Wt_sq_eq {α z θ : ℝ} (hγ : Work.Spaces.gam α ≠ 0) (hσ : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rcases eq_or_lt_of_le hσ with h | h
  · rw [← h, Real.zero_rpow (by simpa using hγ),
      Real.zero_rpow (by simpa using (div_ne_zero hγ (by norm_num : (2:ℝ) ≠ 0)))]
    ring
  · have h1 : (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
      rw [sq, ← Real.rpow_add h]
      congr 1
      ring
    rw [h1]

theorem Wt_sq_Iθ {α z θ : ℝ} (hγ : Work.Spaces.gam α ≠ 0) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
  Wt_sq_eq hγ (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)

theorem gam_ne_zero {α : ℝ} (hα : 0 < α) : Work.Spaces.gam α ≠ 0 :=
  ne_of_gt (by rw [Work.Spaces.gam]; linarith)




theorem pm_eq_restrict :
    pm = MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  show (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    = MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]

/-! ## The `σ`-weight of the angular derivative of a pure `D_z`-slot -/


/-! ## Product integrability from a pointwise domination by the `ℋ⁶`-integrand -/






end Work.FTS.StrongPersist.N6Trans.SixRoute
