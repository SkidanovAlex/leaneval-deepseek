import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.R1G3.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G3

set_option linter.unusedVariables false

/-! ## Two chain rules for the radial rescaling `z ↦ z / c`

`bslOp α` is built from the radial operator `D_z = z ∂_z` (appearing as the terms `z²∂_zz` and
`z∂_z`, both of which are homogeneous of degree `0` in `z`), so it is invariant under the
rescaling `z ↦ z/c`.  The two lemmas below are the chain rules that make this precise at the
level of `deriv`; the first is unconditional because Mathlib's `deriv` is totalised
(`deriv_comp_mul_left` is the corresponding statement for `x ↦ g (c * x)`). -/

/-- Chain rule for the rescaling `t ↦ g (t / c)`: `(g(·/c))'(x) = c⁻¹ g'(x/c)`.
No differentiability hypothesis is needed (totalised `deriv`). -/
lemma deriv_comp_div_scale (g : ℝ → ℝ) (c x : ℝ) :
    deriv (fun t => g (t / c)) x = c⁻¹ * deriv g (x / c) := by
  have h : (fun t => g (t / c)) = (fun t => g (c⁻¹ * t)) := by
    funext t; rw [div_eq_mul_inv, mul_comm]
  rw [h, deriv_comp_mul_left, smul_eq_mul]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

/-- Second order chain rule for the rescaling `t ↦ g (t / c)`:
`((g(·/c))')'(z) = c⁻¹² g''(z/c)`, under differentiability of `g'` at `z/c` (which holds
automatically when `g` is `C²` there). -/
lemma deriv_comp_div_scale_deriv (g : ℝ → ℝ) (c z : ℝ)
    (hg : DifferentiableAt ℝ (deriv g) (z / c)) :
    deriv (fun z' => deriv (fun z'' => g (z'' / c)) z') z
      = c⁻¹ ^ 2 * deriv (deriv g) (z / c) := by
  have hfe : (fun z' => deriv (fun z'' => g (z'' / c)) z')
      = fun z' => c⁻¹ * deriv g (z' / c) := by
    funext z'; exact deriv_comp_div_scale g c z'
  have h2 : (fun z' => c⁻¹ * deriv g (z' / c))
      = fun z' => (fun u => c⁻¹ * deriv g u) (z' / c) := rfl
  rw [hfe, h2, deriv_comp_div_scale (fun u => c⁻¹ * deriv g u) c z,
      deriv_const_mul (c⁻¹) hg]
  ring

/-- **Scaling invariance of the elliptic operator `bslOp` in the radial variable.**  `bslOp α` is
built from `D_z = z ∂_z` (the `z²∂_zz` and `z∂_z` terms) and from angular operations, hence it
commutes with the rescaling `z ↦ z/c` of the self-similar radial variable: passing from the
*physical* polar variable `R = ρ^α` to the *self-similar* variable `z = R/λ` does not change the
operator.  This is what makes the elliptic law of the ansatz `bslOp α Φ = -F` well posed in the
self-similar variables. -/
theorem bslOp_scale (α c : ℝ) (hc : c ≠ 0) (Φ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hΦ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2) (z / c, θ)) :
    Work.Elliptic.bslOp α (fun z θ => Φ (z / c) θ) z θ
      = Work.Elliptic.bslOp α Φ (z / c) θ := by
  -- the `z`-slice `u ↦ Φ u θ` is `C²` at `z/c`, hence `(∂_zΦ)` is differentiable there
  have hslice : ContDiffAt ℝ 2 (fun u => Φ u θ) (z / c) :=
    Work.Elliptic.contDiffAt_uncurry_slice_fst Φ (z / c) θ hΦ
  have hg : DifferentiableAt ℝ (deriv (fun u => Φ u θ)) (z / c) :=
    (hslice.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- the radial chain rules
  have hpz : Work.Spaces.pz (fun z θ => Φ (z / c) θ) z θ
      = c⁻¹ * Work.Spaces.pz Φ (z / c) θ := by
    simp only [Work.Spaces.pz]
    exact deriv_comp_div_scale (fun u => Φ u θ) c z
  have hpz2 : Work.Spaces.pzIter 2 (fun z θ => Φ (z / c) θ) z θ
      = c⁻¹ ^ 2 * Work.Spaces.pzIter 2 Φ (z / c) θ := by
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
    exact deriv_comp_div_scale_deriv (fun u => Φ u θ) c z hg
  -- the angular part is untouched by the rescaling
  have hL : Work.Elliptic.Lzero (fun z θ => Φ (z / c) θ) z θ
      = Work.Elliptic.Lzero Φ (z / c) θ := rfl
  rw [Work.Elliptic.bslOp_apply, Work.Elliptic.bslOp_apply, hpz2, hpz, hL]
  ring

end Work.R1G3
