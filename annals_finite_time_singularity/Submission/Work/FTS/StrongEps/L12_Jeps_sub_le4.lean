import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.L12_Jeps_sub_le4_proof
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.ProjSlotDerivFull =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false


end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12_Jeps_sub_le4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **`|L₁₂(J_ε f)(0) − L₁₂(f)(0)| ≤ C ε ‖f‖_{ℋ⁴}`**. -/
theorem L12_Jeps_sub_le4 (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (f : Fn),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 →
        |Work.Construction.L12 (Jeps ρ ε f) 0 - Work.Construction.L12 f 0|
          ≤ C * ε * Work.Spaces.HkNorm α 4 f :=
  L12_Jeps_sub_le4_proof ρ hρ

end Work.FTS.StrongEps
end
end
