import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

/-- The Hessian of the radial function `x ↦ F (‖x‖ ^ 2)` on a real inner product space.

For a `C²` function `F : ℝ → ℝ` the second Fréchet derivative of `x ↦ F (‖x‖ ^ 2)` at `z`,
evaluated on the pair `(u, v)`, is

`2 * F'(‖z‖ ^ 2) * ⟪u, v⟫ + 4 * F''(‖z‖ ^ 2) * ⟪z, u⟫ * ⟪z, v⟫`.

This is the classical formula `∇²(F∘‖·‖²) = 2F'(‖z‖²) I + 4F''(‖z‖²) z zᵀ`, written in the
`fderiv`-of-`fderiv` form used by the pressure reconstruction. -/
theorem normSq_hessian_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (z u v : E) :
    (fderiv ℝ (fun w : E => fderiv ℝ (fun x : E => F (‖x‖ ^ 2)) w v) z) u
      = 2 * deriv F (‖z‖ ^ 2) * inner ℝ u v
        + 4 * deriv (deriv F) (‖z‖ ^ 2) * (inner ℝ z u * inner ℝ z v) := by
  -- the one-dimensional derivative of `deriv F` at `‖z‖ ^ 2`
  have hderiv : HasDerivAt (deriv F) (deriv (deriv F) (‖z‖ ^ 2)) (‖z‖ ^ 2) := by
    rw [hasDerivAt_iff_hasFDerivAt, toSpanSingleton_deriv]
    exact (hF.differentiable_deriv_two (‖z‖ ^ 2)).hasFDerivAt
  -- `x ↦ ‖x‖ ^ 2` has derivative `2 • innerSL ℝ x` at `x` (with the scalar pinned to `ℝ`)
  have hsq : HasFDerivAt (fun x : E => ‖x‖ ^ 2) ((2:ℝ) • innerSL ℝ z) z := by
    have h := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
    rwa [← Nat.cast_smul_eq_nsmul ℝ 2 (innerSL ℝ z)] at h
  -- the derivative of `w ↦ deriv F (‖w‖ ^ 2)`
  have hr : HasFDerivAt (fun w : E => deriv F (‖w‖ ^ 2))
      ((deriv (deriv F) (‖z‖ ^ 2)) • ((2:ℝ) • innerSL ℝ z)) z := by
    simpa only [Function.comp_def] using hderiv.comp_hasFDerivAt z hsq
  -- the gradient of `x ↦ F (‖x‖ ^ 2)`
  have hfd : ∀ w : E, fderiv ℝ (fun x : E => F (‖x‖ ^ 2)) w
      = (deriv F (‖w‖ ^ 2)) • ((2:ℝ) • innerSL ℝ w) := by
    intro w
    have hsqw : HasFDerivAt (fun x : E => ‖x‖ ^ 2) ((2:ℝ) • innerSL ℝ w) w := by
      have h := (hasStrictFDerivAt_norm_sq w).hasFDerivAt
      rwa [← Nat.cast_smul_eq_nsmul ℝ 2 (innerSL ℝ w)] at h
    have h1 : HasDerivAt F (deriv F (‖w‖ ^ 2)) (‖w‖ ^ 2) := by
      rw [hasDerivAt_iff_hasFDerivAt, toSpanSingleton_deriv]
      exact ((hF.differentiable (by norm_num)) (‖w‖ ^ 2)).hasFDerivAt
    have h2 := h1.comp_hasFDerivAt w hsqw
    rw [show fderiv ℝ (fun x : E => F (‖x‖ ^ 2)) w
          = fderiv ℝ (F ∘ fun x : E => ‖x‖ ^ 2) w from rfl]
    rw [h2.fderiv]
  -- rewrite the inner derivative as `w ↦ deriv F (‖w‖ ^ 2) * (2 * ⟪w, v⟫)`
  rw [show (fun w : E => fderiv ℝ (fun x : E => F (‖x‖ ^ 2)) w v)
        = (fun w : E => deriv F (‖w‖ ^ 2) * (2 * inner ℝ w v)) from by
      funext w
      rw [hfd w]
      simp [innerSL_apply_apply, smul_eq_mul]]
  rw [show (fun w : E => deriv F (‖w‖ ^ 2) * (2 * inner ℝ w v))
        = (fun w : E => deriv F (‖w‖ ^ 2)) * (fun w : E => 2 * inner ℝ w v) from rfl]
  -- the derivative of `w ↦ 2 * ⟪w, v⟫`
  have hb : HasFDerivAt (fun w : E => 2 * inner ℝ w v) ((2:ℝ) • innerSL ℝ v) z := by
    have hd0 : HasFDerivAt (fun w : E => inner ℝ w v) (innerSL ℝ v) z := by
      have h : (fun w : E => inner ℝ w v) = ⇑(innerSL ℝ v) := by
        funext w; rw [innerSL_apply_apply, real_inner_comm]
      rw [h]; exact (innerSL ℝ v).hasFDerivAt
    simpa using hd0.const_mul (2:ℝ)
  -- product rule and evaluation
  have hprod := hr.mul hb
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, real_inner_comm u v]
  ring

theorem normSq_hessian (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (z u v : EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 3) => F (‖x‖ ^ 2)) w v) z) u
      = 2 * deriv F (‖z‖ ^ 2) * inner ℝ u v
        + 4 * deriv (deriv F) (‖z‖ ^ 2) * (inner ℝ z u * inner ℝ z v) :=
  normSq_hessian_aux F hF z u v

end Work.FTS.PressureOn.Auxiliary
