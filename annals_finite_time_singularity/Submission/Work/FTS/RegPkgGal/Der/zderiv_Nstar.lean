import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.zderiv_Nstar`

The `z`-derivative bound for the modulation term `N_*` of the fake-time equation,

  `N_*(μ,λ,g) = -μ·g - (μ + λ + μλ)·D_z g`   (`Work.Construction.Nstar`),

evaluated on the clock functions `μ(τ)`, `λ(τ)` and on the perturbation family
`(z,θ,τ) ↦ g z θ τ`.

If the `z`-slices `z ↦ g z θ τ` and `z ↦ D_z g(·,θ,τ) z` are differentiable on `z > 0` with
derivatives bounded by `N` (uniformly in `τ ∈ [0,S]`, `θ ∈ Iθ`), and if `|μ|, |λ| ≤ Nmu` on
`[0,S]`, then `z ↦ N_*(μ τ, λ τ, g(·,·,τ)) z θ` is differentiable on `z > 0` with derivative
bounded by `Nmu·N + (2·Nmu + Nmu²)·N` (uniformly).

Note that `N_*` does not involve the *second* `z`-derivative of `g`: the factor
`D_z g = z·∂_zg` is differentiated as a whole, which is exactly what the hypothesis
`hdDg` provides.  The proof is the product/sum rule applied to the two summands, with the
coefficient `μ + λ + μλ` bounded by `|μ| + |λ| + |μ||λ| ≤ 2·Nmu + Nmu²`.

This is the `N_*`-input of `Work.FTS.RegPkgGal.Der.rhs_zderiv_of_parts`: it turns the two
`z`-jet hypotheses on `g` and `D_z g` and the boundedness of the clock functions into the
a-priori regularity of the `N_*` term of the right-hand side of the fake-time equation.
-/

namespace Work.FTS.RegPkgGal.Der

theorem zderiv_Nstar {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {mu lam : ℝ → ℝ} {N Nmu : ℝ}
    (hα : 0 < α) (hS : 0 < S)
    (hdg : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => g z' θ τ) d z ∧ |d| ≤ N)
    (hdDg : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Spaces.Dz (fun z θ => g z θ τ) z' θ) d z ∧ |d| ≤ N)
    (hmu : 0 ≤ Nmu ∧ ∀ τ ∈ Set.Icc 0 S, |mu τ| ≤ Nmu)
    (hlam : ∀ τ ∈ Set.Icc 0 S, |lam τ| ≤ Nmu) :
    ∃ Nc : ℝ, 0 ≤ Nc ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.Nstar (mu τ) (lam τ)
        (fun z θ => g z θ τ) z' θ) d z ∧ |d| ≤ Nc := by
  have hα0 : 0 ≤ α := hα.le
  -- `N ≥ 0` follows from the (non-vacuous) hypothesis `hdg`, evaluated at `τ = 0`, `θ = 0`,
  -- `z = 1`.
  have h0S : (0 : ℝ) ∈ Set.Icc 0 S := ⟨le_refl 0, hS.le⟩
  have h0θ : (0 : ℝ) ∈ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact ⟨le_refl 0, by linarith [Real.pi_pos]⟩
  have h1z : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hN0 : 0 ≤ N := by
    obtain ⟨d, _, hd⟩ := hdg 0 h0S 0 h0θ 1 h1z
    exact le_trans (abs_nonneg d) hd
  refine ⟨Nmu * N + (2 * Nmu + Nmu ^ 2) * N, ?_, ?_⟩
  · nlinarith [hmu.1, hN0, sq_nonneg Nmu]
  · intro τ hτ θ hθ z hz
    obtain ⟨dg, hdgd, hdgb⟩ := hdg τ hτ θ hθ z hz
    obtain ⟨dDg, hdDgd, hdDgb⟩ := hdDg τ hτ θ hθ z hz
    -- The bound on the coefficient `μ + λ + μλ`.
    have hc : |mu τ + lam τ + mu τ * lam τ| ≤ 2 * Nmu + Nmu ^ 2 := by
      have hu := hmu.2 τ hτ
      have hl := hlam τ hτ
      have h1 : |mu τ + lam τ| ≤ |mu τ| + |lam τ| := abs_add_le _ _
      have h2 : |mu τ * lam τ| ≤ Nmu * Nmu := by
        rw [abs_mul]
        exact mul_le_mul hu hl (abs_nonneg _) hmu.1
      have h3 : |mu τ + lam τ + mu τ * lam τ| ≤ |mu τ + lam τ| + |mu τ * lam τ| :=
        abs_add_le _ _
      nlinarith [sq_nonneg Nmu]
    have hC0 : 0 ≤ 2 * Nmu + Nmu ^ 2 := by nlinarith [hmu.1, sq_nonneg Nmu]
    refine ⟨(-(mu τ)) * dg + (-(mu τ + lam τ + mu τ * lam τ)) * dDg, ?_, ?_⟩
    · -- The derivative itself: sum rule on the two summands, each with a constant factor.
      have heq : (fun z' => Work.Construction.Nstar (mu τ) (lam τ) (fun z θ => g z θ τ) z' θ)
          = (fun z' => (-(mu τ)) * g z' θ τ)
            + (fun z' => (-(mu τ + lam τ + mu τ * lam τ))
                * Work.Spaces.Dz (fun z θ => g z θ τ) z' θ) := by
        funext z'
        simp only [Pi.add_apply, Work.Construction.Nstar, Work.Spaces.Dz, Work.Spaces.pz]
        ring
      rw [heq]
      exact (hdgd.const_mul (-(mu τ))).add
        (hdDgd.const_mul (-(mu τ + lam τ + mu τ * lam τ)))
    · -- The bound on the derivative.
      have hb1 : |(-(mu τ)) * dg| ≤ Nmu * N := by
        rw [abs_mul, abs_neg]
        exact mul_le_mul (hmu.2 τ hτ) hdgb (abs_nonneg _) hmu.1
      have hb2 : |(-(mu τ + lam τ + mu τ * lam τ)) * dDg| ≤ (2 * Nmu + Nmu ^ 2) * N := by
        rw [abs_mul, abs_neg]
        exact mul_le_mul hc hdDgb (abs_nonneg _) hC0
      calc |(-(mu τ)) * dg + (-(mu τ + lam τ + mu τ * lam τ)) * dDg|
          ≤ |(-(mu τ)) * dg| + |(-(mu τ + lam τ + mu τ * lam τ)) * dDg| := abs_add_le _ _
        _ ≤ Nmu * N + (2 * Nmu + Nmu ^ 2) * N := add_le_add hb1 hb2

end Work.FTS.RegPkgGal.Der
