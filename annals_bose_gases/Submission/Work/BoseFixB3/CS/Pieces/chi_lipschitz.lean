import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.ChiWitness
import Submission.ConvChiBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `χ` is globally Lipschitz

`Submission.BoseGases.chi` is the `C^∞` bump of `Submission/CubicChi.lean`, compactly
supported.  A compactly supported `C^1` function on a normed space is globally
Lipschitz: its Fréchet derivative is continuous and compactly supported (hence
bounded), and the mean value inequality on the (convex) whole space bounds
`‖f a - f b‖` by that constant times `‖a - b‖`.

We prove that general fact first (`lipschitz_of_hasCompactSupport_fderiv`), then
specialise it to `χ`.
-/

noncomputable section

namespace Work.BoseFixB3.CS.Pieces

/-- A differentiable real-valued function on a normed space whose Fréchet derivative
is continuous and has compact support is globally Lipschitz. -/
lemma lipschitz_of_hasCompactSupport_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hdiff : Differentiable ℝ f)
    (hsupp : HasCompactSupport (fderiv ℝ f)) (hcont : Continuous (fderiv ℝ f)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a b : E, |f a - f b| ≤ L * ‖a - b‖ := by
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hcont
  refine ⟨max C 0, le_max_right C 0, fun a b => ?_⟩
  have hmain : ‖f a - f b‖ ≤ (max C 0 : ℝ) * ‖a - b‖ :=
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := f)
      (fun x _ => hdiff x) (fun x _ => (hC x).trans (le_max_left C 0))
      trivial trivial
  rwa [Real.norm_eq_abs] at hmain

theorem chi_lipschitz :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a b : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.chi a - Submission.BoseGases.chi b| ≤ L * ‖a - b‖ :=
  lipschitz_of_hasCompactSupport_fderiv
    (Submission.BoseGases.chi_contDiff.differentiable (by simp))
    (HasCompactSupport.fderiv (𝕜 := ℝ) Submission.BoseGases.chi_hasCompactSupport)
    (Submission.BoseGases.chi_contDiff.continuous_fderiv (by simp))

end Work.BoseFixB3.CS.Pieces
