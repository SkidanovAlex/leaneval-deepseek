import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

theorem g_pointwise_ident (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      g θ = - deriv (deriv u) θ + Real.tan θ * deriv u θ
        + (Real.tan θ ^ 2 - 5) * u θ := by
  intro θ hθ
  -- `cos θ ≠ 0` on `(0, π/2)`, so `tan` is differentiable at `θ`.
  have hcos : Real.cos θ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩).ne'
  -- `u` is differentiable at `θ` because `θ` is an interior point of the (open) domain.
  have hdu : DifferentiableAt ℝ u θ :=
    (hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
  have hmtan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  -- `tan' = 1/cos² = tan² + 1`.
  have htrig : 1 / Real.cos θ ^ 2 = Real.tan θ ^ 2 + 1 := by
    rw [div_eq_iff (pow_ne_zero 2 hcos)]
    have h := Real.one_add_tan_sq_mul_cos_sq_eq_one hcos
    ring_nf
    linarith [h]
  -- Product rule for `∂_θ(tan θ · u θ)`.
  have hmul : deriv (fun t => Real.tan t * u t) θ
      = Real.tan θ * deriv u θ + (Real.tan θ ^ 2 + 1) * u θ := by
    change deriv (Real.tan * u) θ = _
    rw [deriv_mul hmtan hdu, Real.deriv_tan]
    rw [htrig]
    ring
  -- Unfold `Lzero1`, identifying `deriv (fun t => deriv u t) θ` with `deriv (deriv u) θ`.
  have h1 : Work.FTS.EllipticEst.Lzero1 u θ
      = -deriv (deriv u) θ + deriv (fun t => Real.tan t * u t) θ - 6 * u θ := rfl
  have hg' : g θ = -deriv (deriv u) θ + deriv (fun t => Real.tan t * u t) θ - 6 * u θ := by
    have h := (hg θ hθ).symm
    rwa [h1] at h
  rw [hg', hmul]
  ring

end Work.FTS.EllipticEst.remov
