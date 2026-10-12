import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import ChallengeDeps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# 1-D radial Laplacian identity

For a twice continuously differentiable `V : ℝ → ℝ` and `r ≠ 0`,

    (d²/dt² + (2/t) d/dt) (V(t)/t)  at  t = r    equals   V''(r)/r .

In Lean:

    deriv (deriv (fun t => V t * t⁻¹)) r + 2 * deriv (fun t => V t * t⁻¹) r / r
        = deriv (deriv V) r * r⁻¹

This is the one-dimensional core of `Δ(V(‖x‖)/‖x‖) = V''(‖x‖)/‖x‖` in ℝ³.
Prove it by direct calculus: write `f(t) = V(t)·t⁻¹`, compute
`f'(t) = V'(t)/t − V(t)/t²`, then
`f''(t) = V''(t)/t − 2V'(t)/t² + 2V(t)/t³`, and combine.
You may add any helper lemmas above.  Useful mathlib API:
`deriv_mul`, `deriv_inv`, `deriv_sub`, `deriv_add`, `Filter.EventuallyEq.deriv_eq`,
`DifferentiableAt.mul`, `DifferentiableAt.inv`, `differentiableAt_inv`,
`ContDiff.contDiffAt`, `ContDiffAt.differentiableAt`.
-/

noncomputable section

set_option autoImplicit false

namespace Submission.OneDimId

open Filter
open scoped ContDiff Topology

/-- The derivative of `t ↦ V t · t⁻¹` at a nonzero point `t`. -/
lemma deriv_one_over_id (V : ℝ → ℝ) (hV : ContDiff ℝ 2 V) {t : ℝ} (ht : t ≠ 0) :
    deriv (fun s : ℝ => V s * s⁻¹) t = deriv V t * t⁻¹ - V t * (t⁻¹) ^ 2 := by
  have hVt : DifferentiableAt ℝ V t :=
    (hV.differentiable (by norm_num : (2 : ℕ∞ω) ≠ 0)).differentiableAt
  have hiv : DifferentiableAt ℝ (fun s : ℝ => s⁻¹) t := differentiableAt_inv ht
  calc
    deriv (fun s : ℝ => V s * s⁻¹) t
        = deriv (V * (fun s : ℝ => s⁻¹)) t := by rfl
    _ = deriv V t * t⁻¹ + V t * deriv (fun s : ℝ => s⁻¹) t := by
          simpa using (deriv_mul hVt hiv)
    _ = deriv V t * t⁻¹ + V t * (-(t ^ 2)⁻¹) := by rw [deriv_inv]
    _ = deriv V t * t⁻¹ - V t * (t⁻¹) ^ 2 := by
          have hsq : (t ^ 2)⁻¹ = (t⁻¹) ^ 2 := by field_simp [ht]
          rw [hsq]
          ring

/-- The derivative of `t ↦ V'(t) · t⁻¹` at a nonzero point `r`. -/
lemma deriv_A (V : ℝ → ℝ) (hV : ContDiff ℝ 2 V) {r : ℝ} (hr : r ≠ 0) :
    deriv (fun t : ℝ => deriv V t * t⁻¹) r
      = deriv (deriv V) r * r⁻¹ + deriv V r * (-(r ^ 2)⁻¹) := by
  have h1 : DifferentiableAt ℝ (deriv V) r := (hV.differentiable_deriv_two).differentiableAt
  have h2 : DifferentiableAt ℝ (fun s : ℝ => s⁻¹) r := differentiableAt_inv hr
  calc
    deriv (fun t : ℝ => deriv V t * t⁻¹) r
        = deriv ((deriv V) * (fun s : ℝ => s⁻¹)) r := by rfl
    _ = deriv (deriv V) r * r⁻¹ + deriv V r * deriv (fun s : ℝ => s⁻¹) r := by
          simpa using (deriv_mul h1 h2)
    _ = deriv (deriv V) r * r⁻¹ + deriv V r * (-(r ^ 2)⁻¹) := by rw [deriv_inv]

/-- The derivative of `t ↦ V t · (t⁻¹)²` at a nonzero point `r`. -/
lemma deriv_B (V : ℝ → ℝ) (hV : ContDiff ℝ 2 V) {r : ℝ} (hr : r ≠ 0) :
    deriv (fun t : ℝ => V t * (t⁻¹) ^ 2) r
      = deriv V r * (r⁻¹) ^ 2 + V r * (2 * r⁻¹ * (-(r ^ 2)⁻¹)) := by
  have hVr : DifferentiableAt ℝ V r :=
    (hV.differentiable (by norm_num : (2 : ℕ∞ω) ≠ 0)).differentiableAt
  have hsq : DifferentiableAt ℝ (fun t : ℝ => (t⁻¹) ^ 2) r := by fun_prop
  have hdsq : deriv (fun t : ℝ => (t⁻¹) ^ 2) r = 2 * r⁻¹ * (-(r ^ 2)⁻¹) := by
    have hiv : DifferentiableAt ℝ (fun s : ℝ => s⁻¹) r := differentiableAt_inv hr
    calc
      deriv (fun t : ℝ => (t⁻¹) ^ 2) r
          = deriv ((fun s : ℝ => s⁻¹) ^ 2) r := by rfl
      _ = (2 : ℝ) * (fun s : ℝ => s⁻¹) r ^ (2 - 1) * deriv (fun s : ℝ => s⁻¹) r := by
            exact deriv_pow hiv 2
      _ = 2 * r⁻¹ ^ 1 * (-(r ^ 2)⁻¹) := by simp
      _ = 2 * r⁻¹ * (-(r ^ 2)⁻¹) := by ring
  calc
    deriv (fun t : ℝ => V t * (t⁻¹) ^ 2) r
        = deriv (V * (fun t : ℝ => (t⁻¹) ^ 2)) r := by rfl
    _ = deriv V r * (r⁻¹) ^ 2 + V r * deriv (fun t : ℝ => (t⁻¹) ^ 2) r := by
          simpa using (deriv_mul hVr hsq)
    _ = deriv V r * (r⁻¹) ^ 2 + V r * (2 * r⁻¹ * (-(r ^ 2)⁻¹)) := by rw [hdsq]

end Submission.OneDimId

namespace Submission.BoseGases

open Filter MeasureTheory
open scoped ContDiff Topology Real

lemma one_dim_div_identity (V : ℝ → ℝ) (hV : ContDiff ℝ 2 V) {r : ℝ} (hr : r ≠ 0) :
    deriv (deriv (fun t : ℝ => V t * t⁻¹)) r + 2 * deriv (fun t : ℝ => V t * t⁻¹) r / r
      = deriv (deriv V) r * r⁻¹ := by
  have hs : {t : ℝ | t ≠ 0} ∈ 𝓝 r := (isOpen_ne (x := 0)).mem_nhds hr
  have hphi_eq : deriv (fun t : ℝ => V t * t⁻¹) =ᶠ[𝓝 r]
        (fun t : ℝ => deriv V t * t⁻¹ - V t * (t⁻¹) ^ 2) := by
    filter_upwards [hs] with t ht
    exact Submission.OneDimId.deriv_one_over_id V hV ht
  have hderiv2 : deriv (deriv (fun t : ℝ => V t * t⁻¹)) r
      = deriv (fun t : ℝ => deriv V t * t⁻¹ - V t * (t⁻¹) ^ 2) r :=
    hphi_eq.deriv_eq
  have hderivphi : deriv (fun t : ℝ => deriv V t * t⁻¹ - V t * (t⁻¹) ^ 2) r
      = (deriv (deriv V) r * r⁻¹ + deriv V r * (-(r ^ 2)⁻¹))
        - (deriv V r * (r⁻¹) ^ 2 + V r * (2 * r⁻¹ * (-(r ^ 2)⁻¹))) := by
    calc
      deriv (fun t : ℝ => deriv V t * t⁻¹ - V t * (t⁻¹) ^ 2) r
          = deriv ((fun t : ℝ => deriv V t * t⁻¹) - (fun t : ℝ => V t * (t⁻¹) ^ 2)) r := by
            rfl
      _ = deriv (fun t : ℝ => deriv V t * t⁻¹) r
          - deriv (fun t : ℝ => V t * (t⁻¹) ^ 2) r := by
            have hVr : DifferentiableAt ℝ V r :=
              (hV.differentiable (by norm_num : (2 : ℕ∞ω) ≠ 0)).differentiableAt
            have hderVr : DifferentiableAt ℝ (deriv V) r :=
              (hV.differentiable_deriv_two).differentiableAt
            have hA : DifferentiableAt ℝ (fun t : ℝ => deriv V t * t⁻¹) r := by
              fun_prop
            have hB : DifferentiableAt ℝ (fun t : ℝ => V t * (t⁻¹) ^ 2) r := by
              fun_prop
            exact deriv_sub hA hB
      _ = (deriv (deriv V) r * r⁻¹ + deriv V r * (-(r ^ 2)⁻¹))
          - (deriv V r * (r⁻¹) ^ 2 + V r * (2 * r⁻¹ * (-(r ^ 2)⁻¹))) := by
            rw [Submission.OneDimId.deriv_A V hV hr]
            rw [Submission.OneDimId.deriv_B V hV hr]
  calc
    deriv (deriv (fun t : ℝ => V t * t⁻¹)) r + 2 * deriv (fun t : ℝ => V t * t⁻¹) r / r
        = (deriv (deriv V) r * r⁻¹ + deriv V r * (-(r ^ 2)⁻¹))
          - (deriv V r * (r⁻¹) ^ 2 + V r * (2 * r⁻¹ * (-(r ^ 2)⁻¹)))
          + 2 * (deriv V r * r⁻¹ - V r * (r⁻¹) ^ 2) / r := by
          rw [hderiv2, hderivphi]
          rw [Submission.OneDimId.deriv_one_over_id V hV hr]
    _ = deriv (deriv V) r * r⁻¹ := by
          field_simp [hr]
          ring

end Submission.BoseGases
