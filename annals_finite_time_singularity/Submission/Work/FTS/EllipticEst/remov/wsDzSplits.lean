/-
Copyright: work module for the Elgindi finite-time singularity project.

# The two lowest `D_z`-splittings

This module records the two elementary consequences of the product rule that expand the
iterated radial operators `D_z^2`, `D_z^3` (`D_z = z ∂_z`) applied to a datum `Ψ` which is
`C^∞` on the open quadrant:

* `D_z^2 Ψ = D_z Ψ + z² ∂_z^2 Ψ`  (the `z ∂_z (z ∂_z Ψ) = z ∂_z Ψ + (z ∂_z)^2 Ψ` split);
* `D_z^3 Ψ = D_z^2 Ψ + D_z (z² ∂_z^2 Ψ)`.

Both are used by `remov.weakSliceRegular` to rewrite the higher radial slots of the
`ℋ^k`-norm of `Ψ` in terms of the plain iterated derivative `∂_z^j Ψ`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.wsAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Filter Set

namespace Work.FTS.EllipticEst.remov

theorem wsDzSplits {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {s θ : ℝ} (hs : 0 < s) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.DzIter 2 Ψ s θ
        = Work.Spaces.Dz Ψ s θ + s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) ∧
      (Work.Spaces.DzIter 3 Ψ s θ
        = Work.Spaces.DzIter 2 Ψ s θ
          + Work.Spaces.DzIter 1
              (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') s θ) := by
  -- the product rule for the two elementary blocks `z ↦ z ∂_z Ψ` and `z ↦ z² ∂_z²Ψ`
  have hdF : ∀ z : ℝ, 0 < z →
      deriv (fun z' : ℝ => z' * Work.Spaces.pz Ψ z' θ) z
        = Work.Spaces.pz Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ := by
    intro z hz
    have h := (hasDerivAt_id z).mul (hΨ.hasDerivAt_slice_pzIter 1 hθ hz)
    have hfun : (fun z' : ℝ => z' * Work.Spaces.pz Ψ z' θ)
        = (id * fun z' : ℝ => Work.Spaces.pzIter 1 Ψ z' θ) := by
      funext z'
      simp [Pi.mul_apply]
    rw [hfun, h.deriv]
    simp only [one_mul, id_eq]
    rfl
  have hdG : ∀ z : ℝ, 0 < z →
      deriv (fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ) z
        = 2 * z * Work.Spaces.pzIter 2 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ := by
    intro z hz
    have h := ((hasDerivAt_id z).pow 2).mul (hΨ.hasDerivAt_slice_pzIter 2 hθ hz)
    have hfun : (fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ)
        = (id ^ 2 * fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ) := by
      funext z'
      simp [Pi.mul_apply, Pi.pow_apply]
    rw [hfun, h.deriv]
    rw [show (2 : ℕ) + 1 = 3 from rfl]
    simp only [id_eq, Pi.pow_apply, mul_one]
    ring
  have key1 : ∀ z : ℝ, 0 < z → Work.Spaces.DzIter 2 Ψ z θ
      = Work.Spaces.Dz Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ := by
    intro z hz
    have hD : Work.Spaces.DzIter 2 Ψ z θ
        = z * deriv (fun z' : ℝ => z' * Work.Spaces.pz Ψ z' θ) z := rfl
    rw [hD, hdF z hz, Work.Spaces.Dz]
    ring
  refine ⟨key1 s hs, ?_⟩
  -- `D_z^2 Ψ` coincides with the sum of the two blocks on a neighbourhood of `s`
  have hbody : (fun z' : ℝ => Work.Spaces.DzIter 2 Ψ z' θ) =ᶠ[𝓝 s]
      (fun z' : ℝ => z' * Work.Spaces.pz Ψ z' θ
        + z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with z' hz'
    rw [key1 z' hz', Work.Spaces.Dz]
  have hDF : DifferentiableAt ℝ (fun z' : ℝ => z' * Work.Spaces.pz Ψ z' θ) s := by
    have h := (hasDerivAt_id s).mul (hΨ.hasDerivAt_slice_pzIter 1 hθ hs)
    exact h.differentiableAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z' => by simp [Pi.mul_apply])
  have hDG : DifferentiableAt ℝ
      (fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ) s := by
    have h := ((hasDerivAt_id s).pow 2).mul (hΨ.hasDerivAt_slice_pzIter 2 hθ hs)
    exact h.differentiableAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z' => by simp [Pi.mul_apply, Pi.pow_apply])
  have hderiv2 : deriv (fun z' : ℝ => Work.Spaces.DzIter 2 Ψ z' θ) s
      = (Work.Spaces.pz Ψ s θ + s * Work.Spaces.pzIter 2 Ψ s θ)
        + (2 * s * Work.Spaces.pzIter 2 Ψ s θ + s ^ 2 * Work.Spaces.pzIter 3 Ψ s θ) := by
    rw [Filter.EventuallyEq.deriv_eq hbody]
    have heq : deriv (fun z' : ℝ => z' * Work.Spaces.pz Ψ z' θ
          + z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ) s
        = deriv ((fun z' : ℝ => z' * Work.Spaces.pz Ψ z' θ)
          + fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ) s :=
      Filter.EventuallyEq.deriv_eq
        (Filter.Eventually.of_forall fun z' => by simp [Pi.add_apply])
    rw [heq, deriv_add hDF hDG, hdF s hs, hdG s hs]
  have hD3 : Work.Spaces.DzIter 3 Ψ s θ
      = s * deriv (fun z' : ℝ => Work.Spaces.DzIter 2 Ψ z' θ) s := rfl
  have hDg : Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') s θ
      = s * deriv (fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ) s := rfl
  rw [hD3, hderiv2, hDg, hdG s hs, key1 s hs, Work.Spaces.Dz]
  ring

end Work.FTS.EllipticEst.remov
