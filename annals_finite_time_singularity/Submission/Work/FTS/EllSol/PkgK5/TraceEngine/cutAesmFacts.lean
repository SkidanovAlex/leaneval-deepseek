import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.PkgK5.InterpTraceCore
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.TraceEngine

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# A.e. strong measurability of the cut-off family and of the weight `w²·thEta`

All three functions in `cutAesmFacts` are continuous on the *open* quadrant
`(0,∞) × (0,π/2)`; the closed quadrant `Iz ×ˢ Iθ = [0,∞) × [0,π/2]` differs from it by the
null set of the coordinate axes.  Since the product `(volume.restrict Iz).prod
(volume.restrict Iθ)` is `volume.restrict (Iz ×ˢ Iθ)` (`Measure.prod_restrict`) and
`volume.restrict` only sees the set up to a.e. equality (`Measure.restrict_congr_set`),
continuity on the open quadrant is enough.
-/

/-- A real function continuous on the open quadrant `(0,∞) × (0,π/2)` is a.e. strongly
measurable for `(volume.restrict Iz).prod (volume.restrict Iθ)`. -/
theorem aestronglyMeasurable_of_continuousOn_openQuad {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable F
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- The closed quadrant and the open quadrant agree a.e. for the planar Lebesgue measure.
  have hz : Work.Spaces.Iz =ᵐ[(volume : Measure ℝ)] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm
  have hθ : Work.Spaces.Iθ =ᵐ[(volume : Measure ℝ)] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[(volume : Measure (ℝ × ℝ))] (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  have hmain : MeasureTheory.AEStronglyMeasurable F
      ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hF.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have heq : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_congr_set hprod
  rw [heq]
  exact hmain

/-- The cut-off `χ k` is continuous on the open quadrant: it is `C^∞` on `(0,∞)` by
`CutFam.sm` and the quadrant coordinate is continuous. -/
theorem continuousOn_cut_quad {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => χ k p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hc : ContinuousOn (χ k) (Set.Ioi (0 : ℝ)) := (hχ.sm k).continuousOn
  exact hc.comp continuousOn_fst (fun p hp => hp.1)

/-- The derivative of the cut-off is continuous on the open quadrant: `χ k` is `C^∞` on the
*open* set `(0,∞)`, so `deriv (χ k)` agrees there with the continuous `derivWithin`. -/
theorem continuousOn_deriv_cut_quad {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (χ k) p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hle : (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    rw [Work.Stability.smoothOrder]
    exact WithTop.coe_le_coe.mpr le_top
  have h1 : ContinuousOn (derivWithin (χ k) (Set.Ioi (0 : ℝ))) (Set.Ioi (0 : ℝ)) :=
    (hχ.sm k).continuousOn_derivWithin isOpen_Ioi.uniqueDiffOn hle
  have h2 : ContinuousOn (fun p : ℝ × ℝ => derivWithin (χ k) (Set.Ioi (0 : ℝ)) p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    h1.comp continuousOn_fst (fun p hp => hp.1)
  exact h2.congr (fun p hp => (derivWithin_of_isOpen isOpen_Ioi hp.1).symm)

/-- The weight `w(z)² · sin(2θ)^{-η}` is continuous on the open quadrant (there `z ≠ 0` and
`sin(2θ) > 0`). -/
theorem continuousOn_w_sq_thEta_quad :
    ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hEq : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hEq]
    refine ContinuousOn.div (ContinuousOn.pow ?_ 2) (ContinuousOn.pow ?_ 2) ?_
    · exact continuousOn_const.add continuousOn_fst
    · exact continuousOn_fst
    · intro p hp; exact pow_ne_zero 2 (ne_of_gt hp.1)
  have ht : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      Real.continuous_sin.comp_continuousOn (continuousOn_const.mul continuousOn_snd)
    exact hsin.rpow_const (fun p hp => Or.inl (ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos]))))
  exact (ContinuousOn.pow hw 2).mul ht

theorem cutAesmFacts {χ : ℕ → ℝ → ℝ} {K : ℝ} (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => χ k p.1)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    ∧ MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => deriv (χ k) p.1)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    ∧ MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact aestronglyMeasurable_of_continuousOn_openQuad (continuousOn_cut_quad hχ k)
  · exact aestronglyMeasurable_of_continuousOn_openQuad (continuousOn_deriv_cut_quad hχ k)
  · exact aestronglyMeasurable_of_continuousOn_openQuad continuousOn_w_sq_thEta_quad

end Work.FTS.EllSol.PkgK5.TraceEngine
