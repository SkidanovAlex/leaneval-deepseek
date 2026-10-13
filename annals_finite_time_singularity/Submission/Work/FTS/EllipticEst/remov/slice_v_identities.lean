/-
Copyright: work module for the Elgindi finite-time singularity project.

# Slice identities for `u` in terms of `v = u / cos θ`

On the open angular interval `I = (0, π/2)` put `v = u / cos θ`.  Because `cos` does not
vanish on `I`, we have `u = cos θ · v` and `tan θ · u = sin θ · v` near every point of `I`,
so the derivatives of `u` (and of `tan θ · u`) are obtained from the Leibniz rule applied to
`cos · v` resp. `sin · v`:

* `u'      = cos θ · v' - sin θ · v`,
* `u''     = cos θ · v'' - 2 sin θ · v' - cos θ · v`,
* `u'''    = cos θ · v''' - 3 sin θ · v'' - 3 cos θ · v' + sin θ · v`,
* `(tan θ · u)'' = sin θ · v'' + 2 cos θ · v' - sin θ · v`,

and the angular operator `Lzero1 = -∂_θθ + ∂_θ(tan θ ·) - 6` becomes

* `Lzero1 u = -cos θ · v'' + 3 sin θ · v' - 4 cos θ · v`.

The four displayed identities are exactly the statement of `slice_v_identities`.

The proof is the one of `cosBarIdents`, at order `3` instead of `4`: `u =ᶠ cos · v` at every
point of `I`, so the iterated derivatives are computed with `iteratedDeriv_mul` (via the
helper expansions `itd_cos_*`, `itd_sin_*` of `cosBarIdents`), and the identities reduce to
elementary trigonometry.
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.cosBarIdents

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

theorem slice_v_identities (u : ℝ → ℝ) (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u θ
        = - Real.cos θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
          + 3 * Real.sin θ * deriv (fun t => u t / Real.cos t) θ
          - 4 * Real.cos θ * (u θ / Real.cos θ) ∧
      deriv (deriv (deriv u)) θ
        = Real.cos θ * deriv (fun t => deriv (fun s => deriv (fun r => u r / Real.cos r) s) t) θ
          - 3 * Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
          - 3 * Real.cos θ * deriv (fun t => u t / Real.cos t) θ
          + Real.sin θ * (u θ / Real.cos θ) ∧
      deriv (fun t => deriv (fun s => Real.tan s * u s) t) θ
        = Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
          + 2 * Real.cos θ * deriv (fun t => u t / Real.cos t) θ
          - Real.sin θ * (u θ / Real.cos θ) ∧
      deriv u θ = Real.cos θ * deriv (fun t => u t / Real.cos t) θ
          - Real.sin θ * (u θ / Real.cos θ) := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  set ψ : ℝ → ℝ := fun t => u t / Real.cos t with hψdef
  have hcos_ne : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos t ≠ 0 := by
    intro t ht
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩)
  have hcosθ : Real.cos θ ≠ 0 := hcos_ne θ hθ
  have hψC : ContDiffOn ℝ 3 ψ (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn hcos_ne
  have hψAt : ContDiffAt ℝ 3 ψ θ := hψC.contDiffAt hIoo
  have hψ1 : ContDiffAt ℝ 1 ψ θ := hψAt.of_le (by norm_num)
  have hψ2 : ContDiffAt ℝ 2 ψ θ := hψAt.of_le (by norm_num)
  -- `u = cos θ · ψ` and `tan θ · u = sin θ · ψ` near `θ`
  have hu_eq : u =ᶠ[𝓝 θ] fun s => Real.cos s * ψ s := by
    filter_upwards [hIoo] with s hs
    have hc : Real.cos s ≠ 0 := hcos_ne s hs
    show u s = Real.cos s * ψ s
    rw [hψdef, ← mul_div_assoc, mul_div_cancel_left₀ (u s) hc]
  have htan_eq : (fun s => Real.tan s * u s) =ᶠ[𝓝 θ] fun s => Real.sin s * ψ s := by
    filter_upwards [hIoo] with s hs
    have hc : Real.cos s ≠ 0 := hcos_ne s hs
    show Real.tan s * u s = Real.sin s * ψ s
    rw [Real.tan_eq_sin_div_cos, hψdef, div_mul_eq_mul_div, mul_div_assoc]
  -- Leibniz expansions of the derivatives of `u` and of `tan θ · u`
  have hu1 : iteratedDeriv 1 u θ = -Real.sin θ * ψ θ + Real.cos θ * iteratedDeriv 1 ψ θ := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq 1 hu_eq]
    exact itd_cos_one ψ θ hψ1
  have hu2 : iteratedDeriv 2 u θ = -Real.cos θ * ψ θ - 2 * Real.sin θ * iteratedDeriv 1 ψ θ
      + Real.cos θ * iteratedDeriv 2 ψ θ := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq 2 hu_eq]
    exact itd_cos_two ψ θ hψ2
  have hu3 : iteratedDeriv 3 u θ = Real.sin θ * ψ θ - 3 * Real.cos θ * iteratedDeriv 1 ψ θ
      - 3 * Real.sin θ * iteratedDeriv 2 ψ θ + Real.cos θ * iteratedDeriv 3 ψ θ := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq 3 hu_eq]
    exact itd_cos_three ψ θ hψAt
  have htu1 : iteratedDeriv 1 (fun s => Real.tan s * u s) θ
      = Real.cos θ * ψ θ + Real.sin θ * iteratedDeriv 1 ψ θ := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq 1 htan_eq]
    exact itd_sin_one ψ θ hψ1
  have htu2 : iteratedDeriv 2 (fun s => Real.tan s * u s) θ
      = -Real.sin θ * ψ θ + 2 * Real.cos θ * iteratedDeriv 1 ψ θ
        + Real.sin θ * iteratedDeriv 2 ψ θ := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq 2 htan_eq]
    exact itd_sin_two ψ θ hψ2
  -- conversions from `deriv` to `iteratedDeriv` on the left-hand sides
  have hd2u : deriv (fun s => deriv u s) θ = iteratedDeriv 2 u θ := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hd1tu : deriv (fun s => Real.tan s * u s) θ
      = iteratedDeriv 1 (fun s => Real.tan s * u s) θ := by rw [iteratedDeriv_one]
  have hval : u θ = Real.cos θ * ψ θ := hu_eq.self_of_nhds
  -- `Lzero1 u` in terms of `ψ`
  have keyL : Work.FTS.EllipticEst.Lzero1 u θ
      = -Real.cos θ * iteratedDeriv 2 ψ θ + 3 * Real.sin θ * iteratedDeriv 1 ψ θ
        - 4 * Real.cos θ * ψ θ := by
    unfold Work.FTS.EllipticEst.Lzero1
    rw [hd2u, hd1tu, hu2, htu1, hval]
    ring
  -- conversions of the goal's sub-terms to `ψ`-form
  have hP1 : deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ = iteratedDeriv 2 ψ θ := by
    rw [itd_two_val, hψdef]
  have hP2 : deriv (fun t => deriv (fun s => deriv (fun r => u r / Real.cos r) s) t) θ
      = iteratedDeriv 3 ψ θ := by
    rw [itd_three_val, hψdef]
  have hP0 : deriv (fun t => u t / Real.cos t) θ = iteratedDeriv 1 ψ θ := by
    rw [itd_one_val, hψdef]
  have hPtu : deriv (fun t => deriv (fun s => Real.tan s * u s) t) θ
      = iteratedDeriv 2 (fun s => Real.tan s * u s) θ := by
    rw [itd_two_val]
  have hPu : deriv u θ = iteratedDeriv 1 u θ := by rw [iteratedDeriv_one]
  have hPu3 : deriv (deriv (deriv u)) θ = iteratedDeriv 3 u θ := by
    rw [itd_three_val]
  have hV : u θ / Real.cos θ = ψ θ := by rw [hψdef]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [keyL, hP1, hP0, hV]
  · rw [hPu3, hu3, hP2, hP1, hP0, hV]
    ring
  · rw [hPtu, htu2, hP1, hP0, hV]
    ring
  · rw [hPu, hu1, hP0, hV]
    ring

end Work.FTS.EllipticEst.remov
