import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Honest.SliceSetup
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.SlicePsiNear
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AngBW.S3

open Work.FTS.EllipticEst.Honest

set_option autoImplicit false


open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Plumbing: gluing two half-open pieces -/

/-- **Gluing**: integrability on the two open halves gives integrability on the whole open
interval. -/
theorem integrableOn_Ioo_union_Ioo {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : MeasureTheory.IntegrableOn f (Set.Ioo a b))
    (h2 : MeasureTheory.IntegrableOn f (Set.Ioo b c)) :
    MeasureTheory.IntegrableOn f (Set.Ioo a c) := by
  have h1' : MeasureTheory.IntegrableOn f (Set.Ioc a b) :=
    h1.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (a := a) (b := b)).symm
  have h2' : MeasureTheory.IntegrableOn f (Set.Ioc b c) :=
    h2.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (a := b) (b := c)).symm
  have hu : MeasureTheory.IntegrableOn f (Set.Ioc a b ∪ Set.Ioc b c) := h1'.union h2'
  rw [Set.Ioc_union_Ioc_eq_Ioc hab hbc] at hu
  exact hu.mono_set Set.Ioo_subset_Ioc_self

set_option linter.unusedVariables false in
theorem slice_psi_mem (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hu1 : u (Real.pi / 2) = 0)
    (hB : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hY : MeasureTheory.IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) ∧
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have h0 : (0 : ℝ) ≤ Real.pi / 4 := by linarith [Real.pi_pos]
  have h1 : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨hA1, hA1'⟩ := slice_psi_near_zero u hu hB hX
  obtain ⟨hA2', hA2⟩ := slice_psi_near_pi2 u hu hY
  exact ⟨integrableOn_Ioo_union_Ioo h0 h1 hA1 hA2,
    integrableOn_Ioo_union_Ioo h0 h1 hA1' hA2'⟩


end Work.FTS.EllipticEst.H2W.AngBW.S3
