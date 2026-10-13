import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W.PsiSlices

theorem contDiffOn_uncurry_dilate (Ψ : ℝ → ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (fun z θ => Ψ (lam * z) θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  -- The dilation `(z, θ) ↦ (lam * z, θ)` maps the half-strip into itself (`lam > 0`) and is
  -- smooth, so `Function.uncurry (fun z θ => Ψ (lam * z) θ) = (Function.uncurry Ψ) ∘ φ`
  -- inherits every order of smoothness from `Ψ`.
  intro n
  have hφ : ContDiffOn ℝ n (fun p : ℝ × ℝ => (lam * p.1, p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => (lam * p.1, p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨mul_pos hlam hz, hθ⟩
  exact (hsm n).comp hφ hmap

end Work.H2W.PsiSlices
