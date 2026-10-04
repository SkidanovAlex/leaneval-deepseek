import Mathlib
import Submission.Work.Diff.STE.Lead.CompJetDefs
import Submission.Work.Diff.STE.Lead.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.CompJet

theorem fderiv_comp_jet {n m : ℕ}
    (Ψ : Work.Diff.STE.Lead.Modl n × (Work.Diff.STE.Lead.Idx n m → ℂ) → ℂ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    {F : Work.Diff.STE.Lead.Modl n → (Work.Diff.STE.Lead.Idx n m → ℂ)}
    {F' : Work.Diff.STE.Lead.Modl n →L[ℝ] (Work.Diff.STE.Lead.Idx n m → ℂ)}
    {y v : Work.Diff.STE.Lead.Modl n} (hF : HasFDerivAt F F' y) :
    fderiv ℝ (fun y' => Ψ (y', F y')) y v = fderiv ℝ Ψ (y, F y) (v, F' v) := by
  -- `Ψ` is smooth, hence differentiable at the point `(y, F y)`.
  have hdΨ : DifferentiableAt ℝ Ψ (y, F y) :=
    (hΨ.contDiffAt).differentiableAt (by simp)
  -- The map `y' ↦ (y', F y')` has derivative `(1, F')` at `y`.
  have h1 : HasFDerivAt (fun y' : Work.Diff.STE.Lead.Modl n => (y', F y'))
      ((1 : Work.Diff.STE.Lead.Modl n →L[ℝ] Work.Diff.STE.Lead.Modl n).prod F') y :=
    (hasFDerivAt_id y).prodMk hF
  -- Chain rule.
  have h2 : HasFDerivAt (fun y' : Work.Diff.STE.Lead.Modl n => Ψ (y', F y'))
      ((fderiv ℝ Ψ (y, F y)) ∘SL
        ((1 : Work.Diff.STE.Lead.Modl n →L[ℝ] Work.Diff.STE.Lead.Modl n).prod F')) y :=
    hdΨ.hasFDerivAt.comp y h1
  rw [h2.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]

end Work.Diff.STE.Lead.CompJet
