import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.BoseBoxFock.L1Tails.chiBasicFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.continuous_fderiv_chiC_mul`

The parametric continuity of the Fréchet derivative of `w' ↦ chiC ℓ w' * G w' y` with respect
to the parameter `y`.

This is a purely analytic statement: for a jointly `C^∞` kernel
`G : ℝ³ → ℝ³ → ℂ` and the `C^∞` window `chiC ℓ`, the function

    p ↦ fderiv ℝ (fun w' => chiC ℓ w' * G w' p.2) p.1 v

is continuous for every fixed direction `v = single j 1`.  The proof bundles the two variables
of `p` into the single smooth function `H q = chiC ℓ q.1 * G q.1 q.2` on `ℝ³ × ℝ³`, identifies
the partial derivative in the first variable with the full derivative of `H` evaluated on the
vector `(v, 0)` using `fderiv_comp` and `hasFDerivAt_prodMk_left`, and then applies
`ContDiff.continuous_fderiv_apply`.
-/

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem continuous_fderiv_chiC_mul {ℓ : ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) (j : Fin 3) :
    Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      fderiv ℝ (fun w' => Work.BoseBoxFock.L1Tails.chiC ℓ w' * G w' p.2) p.1
        (EuclideanSpace.single j (1 : ℝ))) := by
  set v : E3 := EuclideanSpace.single j (1 : ℝ)
  set H : E3 × E3 → ℂ := fun q => Work.BoseBoxFock.L1Tails.chiC ℓ q.1 * G q.1 q.2 with hHdef
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := by
    rw [hHdef]
    exact ((contDiff_chiC ℓ).comp contDiff_fst).mul hG
  have hcont : Continuous (fun q : E3 × E3 => fderiv ℝ H q (v, 0)) :=
    (hH.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  refine hcont.congr fun p => ?_
  have hdH : DifferentiableAt ℝ H (p.1, p.2) := hH.differentiable (by simp) (p.1, p.2)
  have hdι : DifferentiableAt ℝ (fun w' : E3 => (w', p.2)) p.1 := by fun_prop
  have h1 : fderiv ℝ (fun w' : E3 => H (w', p.2)) p.1
      = (fderiv ℝ H (p.1, p.2)).comp (ContinuousLinearMap.inl ℝ E3 E3) := by
    have h3 := fderiv_comp (𝕜 := ℝ) (x := p.1) (f := fun w' : E3 => (w', p.2)) hdH hdι
    rw [show (fderiv ℝ (fun w' : E3 => (w', p.2)) p.1) = ContinuousLinearMap.inl ℝ E3 E3 from
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2).fderiv] at h3
    exact h3
  have hthis : (fun w' : E3 => H (w', p.2))
      = (fun w' => Work.BoseBoxFock.L1Tails.chiC ℓ w' * G w' p.2) := by
    funext w'; rfl
  rw [← hthis, h1]
  simp [ContinuousLinearMap.inl_apply]

end Work.BoseBoxFock.L1Tails
