import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux

theorem thMollTransfer : ∀ (u : ℝ → ℝ → ℝ) {ε z : ℝ}, 0 < ε → ε ≤ 1 / 2 → 0 < z → u z 0 = 0 → u z (Real.pi / 2) = 0 → MeasureTheory.IntegrableOn (fun θ : ℝ => u z θ) Work.Spaces.Iθ → (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt (fun θ' : ℝ => u z θ') (Work.Spaces.pth u z θ) θ) → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.pth u z θ) Work.Spaces.Iθ → (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt (fun θ' : ℝ => Work.Spaces.pth u z θ') (Work.Spaces.pth (Work.Spaces.pth u) z θ) θ) → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth u) z θ) Work.Spaces.Iθ → (∀ θ ∈ Work.Spaces.Iθ, Work.FTS.EllSol.PkgK5.K5c.thMoll u ε z θ = ∫ s in Work.Spaces.Iθ, (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s) - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)) * u z s) ∧ (∀ θ ∈ Work.Spaces.Iθ, deriv (fun θ' : ℝ => Work.FTS.EllSol.PkgK5.K5c.thMoll u ε z θ') θ = ∫ s in Work.Spaces.Iθ, (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s) - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)) * Work.Spaces.pth u z s) ∧ (∀ θ ∈ Work.Spaces.Iθ, deriv (deriv (fun θ' : ℝ => Work.FTS.EllSol.PkgK5.K5c.thMoll u ε z θ')) θ = ∫ s in Work.Spaces.Iθ, (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s) - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)) * Work.Spaces.pth (Work.Spaces.pth u) z s) := by sorry

end Work.FTS.EllSol.EllPkgAux
