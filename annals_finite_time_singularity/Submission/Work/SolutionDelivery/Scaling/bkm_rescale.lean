/-
# The BKM integral under the Euler scaling

The classical Euler scaling `u'(x,t) = λ u(λx, λ²t)` (`Work.SolutionDelivery.rescale`) scales the
vorticity *pointwise* by `λ²`,

  `∇×u'(·,t) = λ² · (∇×u)(λ·, λ²t)`,

and since `x ↦ λx` is a bijection of `ℝ³` (for `λ ≠ 0`) the `L∞`-in-space norm of the vorticity
scales by `λ²` as well.  In the BKM integral `∫₀ᵗ ⨆ₓ ‖ω(x,s)‖ ds` that factor `λ²` is exactly the
Jacobian of the substitution `s ↦ λ²s`, so the integral is merely reparametrised:

  `bkm u' t = bkm u (λ²t)`.

This is the last scaling fact needed by `Work.SolutionDelivery.EulerScalingToUnitData`
(the blow-up time of the rescaled solution is `1`).

The three ingredients, each proved below:

* `vorticity_smul_scale` — the pointwise identity `∇×(λ u(λ·)) = λ² (∇×u)(λ·)`, from
  `fderiv ℝ (λ • F (λ • ·)) x = λ² • fderiv ℝ F (λ • x)` (`fderiv_comp_smul` +
  `fderiv_const_smul_field`, both unconditional) and the bilinearity of the cross product;
* `iSup_norm_vorticity_rescale` — the same identity for the `⨆ₓ`;
* `integral_rescale` — the interval-integral substitution
  `∫₀ᵗ λ² A(λ²s) ds = ∫₀^{λ²t} A(τ) dτ` (`intervalIntegral.smul_integral_comp_mul_left`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.SolutionDelivery.Scaling.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity

namespace Work.SolutionDelivery.Scaling

/-! ## The pointwise scaling of the vorticity -/

/-- **The vorticity of a rescaled field.**  For every `λ` (the hypothesis `λ ≠ 0` is *not* needed
here)

  `∇×(λ u(λ·)) (x) = λ² · (∇×u)(λx)`.

The chain rule enters only through the two unconditional `fderiv` identities
`fderiv ℝ (λ • F (λ • ·)) x = λ² • fderiv ℝ F (λ • x)` (`fderiv_comp_smul` followed by
`fderiv_const_smul_field`), and the cross product is linear in its second argument. -/
theorem vorticity_smul_scale {lam : ℝ} {F : R3 → R3} (x : R3) :
    vorticity (fun y => lam • F (lam • y)) x = lam ^ 2 • vorticity F (lam • x) := by
  have hd : fderiv ℝ (fun y => lam • F (lam • y)) x = lam ^ 2 • fderiv ℝ F (lam • x) := by
    change fderiv ℝ (fun y => (lam • F) (lam • y)) x = lam ^ 2 • fderiv ℝ F (lam • x)
    rw [fderiv_comp_smul (𝕜 := ℝ) (f := lam • F) (x := x) lam]
    rw [fderiv_const_smul_field (𝕜 := ℝ) (F := R3) lam]
    simp [Pi.smul_apply, smul_smul, pow_two]
  simp only [vorticity]
  rw [hd]
  simp only [smul_apply, WithLp.ofLp_smul, LinearMap.map_smul]
  rw [← Finset.smul_sum, WithLp.toLp_smul]

/-! ## Reindexing an `⨆` along `x ↦ λx` -/

/-- The multiplication `x ↦ λx` is a bijection of `ℝ³` for `λ ≠ 0`, hence reindexes an `⨆`. -/
theorem iSup_comp_smul_eq {lam : ℝ} (hlam : lam ≠ 0) (g : R3 → ℝ) :
    (⨆ x, g (lam • x)) = ⨆ x, g x := by
  have hsurj : Function.Surjective (fun x : R3 => lam • x) :=
    fun y => ⟨lam⁻¹ • y, by simp [smul_smul, mul_inv_cancel₀ hlam]⟩
  have hrange : Set.range (fun x : R3 => g (lam • x)) = Set.range g := by
    have hcomp : (fun x : R3 => g (lam • x)) = g ∘ (fun x : R3 => lam • x) := rfl
    rw [hcomp, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]
  change sSup (Set.range (fun x : R3 => g (lam • x))) = sSup (Set.range g)
  rw [hrange]

/-- Pulling a nonnegative constant out of an `⨆` that is reindexed along `x ↦ λx`. -/
theorem iSup_const_mul_comp_smul {lam c : ℝ} (hlam : lam ≠ 0) (hc : 0 ≤ c)
    (g : R3 → ℝ) : (⨆ x, c * g (lam • x)) = c * ⨆ x, g x := by
  rw [iSup_comp_smul_eq hlam (fun z => c * g z)]
  exact (Real.mul_iSup_of_nonneg hc g).symm

/-! ## The `L∞`-in-space norm of the vorticity -/

/-- **The `L∞`-in-space norm of the vorticity under the scaling.**  For `λ ≠ 0` and every time `s`,

  `⨆ₓ ‖(∇×u')(x,s)‖ = λ² · ⨆ₓ ‖(∇×u)(x,λ²s)‖`,  `u' = rescale λ u`. -/
theorem iSup_norm_vorticity_rescale {lam : ℝ} (hlam : lam ≠ 0) (u : R3 → ℝ → R3) (s : ℝ) :
    (⨆ x, ‖vorticity ((rescale lam u) · s) x‖)
      = lam ^ 2 * (⨆ x, ‖vorticity (u · (lam ^ 2 * s)) x‖) := by
  have hfun : (fun x => ‖vorticity ((rescale lam u) · s) x‖)
      = fun x => lam ^ 2 * ‖vorticity (u · (lam ^ 2 * s)) (lam • x)‖ := by
    funext x
    have hab : vorticity ((rescale lam u) · s) x
        = lam ^ 2 • vorticity (u · (lam ^ 2 * s)) (lam • x) :=
      vorticity_smul_scale (lam := lam) (F := fun y => u y (lam ^ 2 * s)) x
    rw [hab, norm_smul, Real.norm_of_nonneg (sq_nonneg lam)]
  rw [hfun]
  exact iSup_const_mul_comp_smul hlam (sq_nonneg lam)
    (fun z => ‖vorticity (u · (lam ^ 2 * s)) z‖)

/-! ## The interval-integral substitution -/

/-- **The substitution `s ↦ λ²s` in the BKM integrand**: the factor `λ²` produced by the vorticity
scaling is exactly the Jacobian of the change of variables, so the interval integral is only
reparametrised,

  `∫₀ᵗ λ² A(λ²s) ds = ∫₀^{λ²t} A(τ) dτ`. -/
theorem integral_rescale (A : ℝ → ℝ) {lam : ℝ} (hlam : lam ≠ 0) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, lam ^ 2 * A (lam ^ 2 * s)) = ∫ τ in (0 : ℝ)..(lam ^ 2 * t), A τ := by
  have hc : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam
  have h1 := intervalIntegral.smul_integral_comp_mul_left (f := fun τ => lam ^ 2 * A τ)
    (a := (0 : ℝ)) (b := t) (c := lam ^ 2)
  have h2 : (∫ x in (0 : ℝ)..lam ^ 2 * t, lam ^ 2 * A x)
      = lam ^ 2 * ∫ x in (0 : ℝ)..lam ^ 2 * t, A x :=
    intervalIntegral.integral_const_mul (lam ^ 2) A
  rw [mul_zero, h2, smul_eq_mul] at h1
  exact mul_left_cancel₀ hc h1

/-! ## The BKM integral under the scaling -/

theorem bkm_rescale {lam : ℝ} (hlam : lam ≠ 0)
    (u : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3) (t : ℝ) :
    Work.LWP.bkm (Work.SolutionDelivery.rescale lam u) t
      = Work.LWP.bkm u (lam ^ 2 * t) := by
  unfold Work.LWP.bkm
  simp_rw [iSup_norm_vorticity_rescale hlam u]
  exact integral_rescale (fun τ => ⨆ x, ‖vorticity (u · τ) x‖) hlam t

end Work.SolutionDelivery.Scaling
