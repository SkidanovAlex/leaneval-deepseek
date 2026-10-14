import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.integrable_cross_slot_rpow
import Submission.Work.FTS.StrongEps.EpsSlotLip
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.hbdd_of_joint_continuous =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.JepsJoint




end Work.FTS.StrongEps.EpsE4Thr.JepsJoint
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.SlotHkGen.integrable_cross_slot_rpow_mixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.EpsE4Thr.SlotHkGen


end Work.FTS.StrongEps.EpsE4Thr.SlotHkGen
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.SlotHkGen.integral_slot_sq_rpow_le_HkSq_mixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.SlotHkGen


end Work.FTS.StrongEps.EpsE4Thr.SlotHkGen
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSlotLipP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

/-! ## The integral form of the `P₀`-scheme -/

/-- **The `P₀`-analogue of `epsSol_eq_integral`.**  A solution of the projected scheme satisfies
`g z θ τ = g₀ z θ + ∫_0^τ epsRHSP … s z θ ds` at every point of the open quadrant.  The proof is
the fundamental theorem of calculus applied to the pointwise ODE of `IsEpsSolP` on `[0,τ]`; only
the continuity of the integrand is used. -/
theorem epsSol_eq_integralP {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) (Set.Icc 0 T)) :
    ∀ z θ τ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → τ ∈ Set.Icc 0 T →
      g z θ τ
        = g₀ z θ + ∫ s in (0 : ℝ)..τ, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ := by
  intro z θ τ hQ hτ
  obtain ⟨hz, hθ₁, hθ₂⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ₁, hθ₂⟩
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => g z θ s)
        (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g x z θ) (Set.Icc 0 T) x :=
    fun x hx => hsol.2 z θ x hz hθ hx
  have hsub : Set.Icc (0 : ℝ) τ ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl hτ.2
  have hftc : ∫ s in (0 : ℝ)..τ, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ
      = g z θ τ - g z θ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.1
      ((HasDerivWithinAt.continuousOn hderiv).mono hsub)
      (fun x hx => (hderiv x ⟨hx.1.le, le_trans hx.2.le hτ.2⟩).hasDerivAt
        (Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 hτ.2)))
      (ContinuousOn.intervalIntegrable_of_Icc hτ.1 ((hcont z θ hQ).mono hsub))
  rw [← hsol.1 z θ]
  linarith

/-! ## Lipschitz continuity of the slots along the `P₀`-scheme -/


end Work.FTS.StrongEps
end
