import Mathlib
import Submission.Work.WilE3.Realify.Defs
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

namespace Work.WilE3.Realify

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

/-- The parametrisation `w ↦ zOf w` of `ℝ^{2k}` by `ℂ^k` (`z = u + i v`) is `ℝ`-differentiable. -/
theorem differentiableAt_zOf {k : ℕ} (w : Fin (k + k) → ℝ) :
    DifferentiableAt ℝ (zOf (k := k)) w := by
  rw [differentiableAt_pi]
  intro i
  unfold zOf
  fun_prop

/-- The complexified system composed with the parametrisation `w ↦ zOf w` is `ℝ`-differentiable:
`eaEvalC c P` is `ℂ`-analytic (`Work.WilE3.API.eaEvalC_fderiv_analytic`), hence `ℝ`-differentiable,
and `zOf` is `ℝ`-linear. -/
theorem differentiableAt_evalUV_complex {k r : ℕ} (c : EAChain k r) (P : EAPoly k r)
    (w : Fin (k + k) → ℝ) :
    DifferentiableAt ℝ (fun w' : Fin (k + k) → ℝ => Work.WilE3.eaEvalC c P (zOf w')) w := by
  have hZ : DifferentiableAt ℝ (zOf (k := k)) w := differentiableAt_zOf w
  have hE : DifferentiableAt ℂ (Work.WilE3.eaEvalC c P) (zOf w) :=
    (Work.WilE3.API.eaEvalC_fderiv_analytic c P (zOf w)).1.differentiableAt
  have hEr : DifferentiableAt ℝ (Work.WilE3.eaEvalC c P) (zOf w) := hE.restrictScalars ℝ
  exact hEr.comp w hZ

theorem differentiableAt_evalUV {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (P : WilkiesDesign.E.EAPoly k r) (w : Fin (k + k) → ℝ) :
    DifferentiableAt ℝ (fun w' : Fin (k + k) → ℝ => (Work.WilE3.Realify.evalUV c P w').re) w ∧
    DifferentiableAt ℝ (fun w' : Fin (k + k) → ℝ => (Work.WilE3.Realify.evalUV c P w').im) w := by
  have hcomp : DifferentiableAt ℝ
      (fun w' : Fin (k + k) → ℝ => Work.WilE3.eaEvalC c P (zOf w')) w :=
    differentiableAt_evalUV_complex c P w
  constructor
  · convert (Complex.reCLM.differentiableAt.comp w hcomp) using 1
    ext w'
    simp [evalUV]
  · convert (Complex.imCLM.differentiableAt.comp w hcomp) using 1
    ext w'
    simp [evalUV]

end

end Work.WilE3.Realify
