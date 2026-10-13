import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.SlotData

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1Hon

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Continuity of the slot data on the open quadrant -/

theorem continuousOn_t1W (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => t1W q p.1 p.2) Work.FTS.H2.Qd := by
  show ContinuousOn (fun p : ℝ × ℝ =>
    (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)) Work.FTS.H2.Qd
  exact (Work.FTS.H2.continuousOn_w_Qd.pow 2).mul
    (Work.FTS.H2.continuousOn_sin_rpow_Qd (-q))

theorem continuousOn_t1Leib {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (a b : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => t1Leib f g a b p.1 p.2) Work.FTS.H2.Qd := by
  show ContinuousOn (fun p : ℝ × ℝ => ∑ a1 ∈ Finset.range (a + 1),
      ∑ b1 ∈ Finset.range (b + 1), (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
        ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
          * (Work.Spaces.mixed b1 a1 f p.1 p.2
             * Work.Spaces.mixed (b - b1) (a - a1 + 1) g p.1 p.2))) Work.FTS.H2.Qd
  refine continuousOn_finset_sum (Finset.range (a + 1))
    (fun a1 _ => continuousOn_finset_sum (Finset.range (b + 1)) (fun b1 _ => ?_))
  by_cases h : a1 = 0 ∧ b1 = 0
  · simpa only [if_pos h] using continuousOn_const (c := (0 : ℝ)) (s := Work.FTS.H2.Qd)
  · simp only [if_neg h]
    exact continuousOn_const.mul (((hf.mixed b1 a1).continuousOn).mul
      ((hg.mixed (b - b1) (a - a1 + 1)).continuousOn))

theorem continuousOn_t1Easy {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (a b : ℕ) (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => t1Easy q f g a b p.1 p.2) Work.FTS.H2.Qd := by
  show ContinuousOn (fun p : ℝ × ℝ => t1W q p.1 p.2 * t1Leib f g a b p.1 p.2
    * Work.Spaces.mixed b a g p.1 p.2) Work.FTS.H2.Qd
  exact ((continuousOn_t1W q).mul (continuousOn_t1Leib hf hg a b)).mul
    ((hg.mixed b a).continuousOn)

theorem continuousOn_t1EasyAbs {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (a b : ℕ) (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => t1EasyAbs q f g a b p.1 p.2) Work.FTS.H2.Qd := by
  show ContinuousOn (fun p : ℝ × ℝ => |t1W q p.1 p.2| * (∑ a1 ∈ Finset.range (a + 1),
      ∑ b1 ∈ Finset.range (b + 1), (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
        |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
          * (Work.Spaces.mixed b1 a1 f p.1 p.2
             * Work.Spaces.mixed (b - b1) (a - a1 + 1) g p.1 p.2)|))
      * |Work.Spaces.mixed b a g p.1 p.2|) Work.FTS.H2.Qd
  refine (((continuousOn_t1W q).abs).mul ?_).mul ((hg.mixed b a).continuousOn).abs
  refine continuousOn_finset_sum (Finset.range (a + 1))
    (fun a1 _ => continuousOn_finset_sum (Finset.range (b + 1)) (fun b1 _ => ?_))
  by_cases h : a1 = 0 ∧ b1 = 0
  · simpa only [if_pos h] using continuousOn_const (c := (0 : ℝ)) (s := Work.FTS.H2.Qd)
  · simp only [if_neg h]
    exact (continuousOn_const.mul (((hf.mixed b1 a1).continuousOn).mul
      ((hg.mixed (b - b1) (a - a1 + 1)).continuousOn))).abs

/-- Almost every point of the product measure `pm` lies in the open quadrant. -/
theorem ae_pm_mem_Qd_T1Hon : ∀ᵐ p ∂Work.FTS.H2.pm, p ∈ Work.FTS.H2.Qd := by
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) =ᵐ[volume.prod volume] Work.FTS.H2.Qd :=
    MeasureTheory.Measure.set_prod_ae_eq
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have h1 : Work.FTS.H2.pm
      = (volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [Work.FTS.H2.pm, MeasureTheory.Measure.prod_restrict]
  rw [h1, MeasureTheory.Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_mem Work.FTS.H2.isOpen_Qd.measurableSet


/-- The slot easy majorant `slotEasySum` is continuous on the open quadrant. -/
theorem continuousOn_slotEasySum (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (a b : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => slotEasySum α f g a b p.1 p.2) Work.FTS.H2.Qd := by
  have hW : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.slotW α a p.1 p.2)
      Work.FTS.H2.Qd := by
    rcases eq_or_ne a 0 with ha | ha
    · subst ha
      have hfun : (fun p : ℝ × ℝ => Work.FTS.TransportS.slotW α 0 p.1 p.2)
          = fun p : ℝ × ℝ => (Work.FTS.H2.Whz p.1 p.2) ^ 2 := by
        funext p
        simp only [Work.FTS.TransportS.slotW_zero]
      have hfun2 : ((fun p : ℝ × ℝ => Work.FTS.H2.Whz p.1 p.2) ^ 2)
          = fun p : ℝ × ℝ => (Work.FTS.H2.Whz p.1 p.2) ^ 2 := by
        funext p; simp only [Pi.pow_apply]
      rw [hfun, ← hfun2]
      exact Work.FTS.H2.continuousOn_Whz_Qd.pow 2
    · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
      have hfun : (fun p : ℝ × ℝ => Work.FTS.TransportS.slotW α a p.1 p.2)
          = fun p : ℝ × ℝ => (Work.FTS.H2.Wm α p.1 p.2) ^ 2 := by
        funext p
        simp only [Work.FTS.TransportS.slotW_of_pos' α ha1]
      have hfun2 : ((fun p : ℝ × ℝ => Work.FTS.H2.Wm α p.1 p.2) ^ 2)
          = fun p : ℝ × ℝ => (Work.FTS.H2.Wm α p.1 p.2) ^ 2 := by
        funext p; simp only [Pi.pow_apply]
      rw [hfun, ← hfun2]
      exact (Work.FTS.H2.continuousOn_Wm_Qd α).pow 2
  show ContinuousOn (fun p : ℝ × ℝ => ∑ a1 ∈ Finset.range (a + 1),
      ∑ b1 ∈ Finset.range (b + 1), (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
        Work.FTS.TransportS.slotW α a p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
          * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g p.1 p.2|
          * |Work.Spaces.mixed b a g p.1 p.2|)) Work.FTS.H2.Qd
  refine continuousOn_finset_sum (Finset.range (a + 1))
    (fun a1 _ => continuousOn_finset_sum (Finset.range (b + 1)) (fun b1 _ => ?_))
  by_cases h : a1 = 0 ∧ b1 = 0
  · simpa only [if_pos h] using continuousOn_const (c := (0 : ℝ)) (s := Work.FTS.H2.Qd)
  · simp only [if_neg h]
    exact (((hW.mul ((hf.mixed b1 a1).continuousOn).abs).mul
      ((hg.mixed (b - b1) (a - a1 + 1)).continuousOn).abs).mul
      ((hg.mixed b a).continuousOn).abs)

end

end Work.FTS.StrongPersist.N6Trans.T1Hon
