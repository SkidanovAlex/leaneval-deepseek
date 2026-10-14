import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.MeridianDyn.DynEqF
import Submission.Work.FTS.MeridianDyn.ResidDyn
import Submission.Work.FTS_BSIdentP.Slim.TendstoSliceQuotient
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set
open scoped Topology

namespace Work.FTS.MeridianDyn

set_option autoImplicit false

/-! ## Parity -/

/-- The full profile extended oddly in `θ` is odd in its angular argument, off `θ = 0`. -/
theorem profFamOdd_neg {α : ℝ} {g : Fam} {Z Θ σ : ℝ} (hΘ : Θ ≠ 0) :
    profFamOdd α g Z (-Θ) σ = -profFamOdd α g Z Θ σ := by
  by_cases h : 0 ≤ Θ
  · have h' : ¬ (0 ≤ -Θ) := by
      intro hcon
      exact hΘ (le_antisymm (neg_nonneg.mp hcon) h)
    have hprof : profFamOdd α g Z Θ σ
        = Work.Construction.Fstar α Z Θ + g Z Θ σ := by
      rw [profFamOdd_apply, Work.ConstructionInstance.profile_of_nonneg h]
      rfl
    have hprof' : profFamOdd α g Z (-Θ) σ
        = -(Work.Construction.Fstar α Z Θ + g Z Θ σ) := by
      rw [profFamOdd_apply, Work.ConstructionInstance.profile, if_neg h']
      simp
    rw [hprof, hprof']
  · have h' : 0 ≤ -Θ := by linarith
    have hprof : profFamOdd α g Z (-Θ) σ
        = Work.Construction.Fstar α Z (-Θ) + g Z (-Θ) σ := by
      rw [profFamOdd_apply, Work.ConstructionInstance.profile_of_nonneg h']
      rfl
    have hprof' : profFamOdd α g Z Θ σ
        = -(Work.Construction.Fstar α Z (-Θ) + g Z (-Θ) σ) := by
      rw [profFamOdd_apply, Work.ConstructionInstance.profile, if_neg h]
      simp
    rw [hprof, hprof']
    ring

/-- The polar radius is even in the axial variable. -/
theorem rhoP_neg (r z : ℝ) : Work.Cyl.rhoP r (-z) = Work.Cyl.rhoP r z := by
  rw [Work.Cyl.rhoP, Work.Cyl.rhoP]
  congr 1
  ring

/-- The polar angle is odd in the axial variable. -/
theorem thetaP_neg (r z : ℝ) : Work.Cyl.thetaP r (-z) = -Work.Cyl.thetaP r z := by
  rw [Work.Cyl.thetaP, Work.Cyl.thetaP, neg_div, Real.arctan_neg]

/-- The polar angle only vanishes on the equatorial plane. -/
theorem thetaP_ne_zero {r z : ℝ} (hr : r ≠ 0) (hz : z ≠ 0) : Work.Cyl.thetaP r z ≠ 0 := by
  intro h0
  have h1 : Real.tan (Work.Cyl.thetaP r z) = 0 := by rw [h0, Real.tan_zero]
  rw [Work.Cyl.thetaP, Real.tan_arctan] at h1
  rcases div_eq_zero_iff.mp h1 with h | h
  · exact hz h
  · exact hr h

/-! ## The main theorem -/



end Work.FTS.MeridianDyn
