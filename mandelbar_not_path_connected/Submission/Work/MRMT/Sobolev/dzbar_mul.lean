import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Sobolev

/-- Pointwise Leibniz rule for the Wirtinger derivative `∂̄ = ½(∂_x + i ∂_y)`
(equivalently the complex conjugate of the holomorphic Wirtinger derivative).

Writing `D h z` for the real Fréchet derivative `fderiv ℝ h z`, the product rule
for real differentiation gives

`D (f * g) z = f z • D g z + g z • D f z`,

and evaluating both sides at `1` and at `Complex.I`, then using `∂̄ h z =
(D h z 1 + I * D h z I)/2`, yields the claim. -/
theorem dzbar_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    Work.MRMT.dzbar (fun w => f w * g w) z = f z * Work.MRMT.dzbar g z + g z * Work.MRMT.dzbar f z := by
  have h : fderiv ℝ (fun w => f w * g w) z = f z • fderiv ℝ g z + g z • fderiv ℝ f z :=
    fderiv_mul hf hg
  simp only [Work.MRMT.dzbar, h, add_apply, smul_apply, smul_eq_mul]
  ring

end Work.MRMT.Sobolev
