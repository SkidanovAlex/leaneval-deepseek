import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.R1G3.Defs
-- ===== merged: Submission.Work.R1G3.bslOp_const_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.R1G3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Unconditional commutation of `deriv` (and `iteratedDeriv`) with scalar multiplication -/

/-- `deriv` commutes with multiplication by a constant, **with no differentiability
hypothesis**: the totalised derivative of a non-differentiable function is `0`, and `c * f` is
differentiable at `x` exactly when `f` is (for `c ≠ 0`). -/
lemma deriv_const_mul_uncond (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  by_cases hc : c = 0
  · subst hc; simp
  · by_cases hf : DifferentiableAt ℝ f x
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro h
        have h3 : DifferentiableAt ℝ (fun y => c⁻¹ * (c * f y)) x := h.const_mul c⁻¹
        have he : (fun y => c⁻¹ * (c * f y)) = f := by
          funext y; field_simp
        rw [he] at h3
        exact hf h3
      rw [deriv_zero_of_not_differentiableAt h2,
        deriv_zero_of_not_differentiableAt hf, mul_zero]

/-- `iteratedDeriv n` commutes with multiplication by a constant, again with no differentiability
hypothesis (apply the first order statement `n` times, using that it holds as an identity of
*functions*). -/
lemma iteratedDeriv_const_mul_uncond (n : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    iteratedDeriv n (fun x => c * f x) = fun x => c * iteratedDeriv n f x := by
  induction n with
  | zero => funext x; simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [iteratedDeriv_succ]
    exact deriv_const_mul_uncond c (iteratedDeriv k f) x

/-! ## The partial derivatives of `Work.Spaces` commute with scalar multiplication -/

/-- `∂_z` commutes with scalar multiplication, unconditionally. -/
lemma pz_const_mul (c : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => c * Ψ z θ) z θ = c * Work.Spaces.pz Ψ z θ := by
  simp only [Work.Spaces.pz]
  exact deriv_const_mul_uncond c (fun z' => Ψ z' θ) z

/-- `∂_θ` commutes with scalar multiplication, unconditionally. -/
lemma pth_const_mul (c : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z θ => c * Ψ z θ) z θ = c * Work.Spaces.pth Ψ z θ := by
  simp only [Work.Spaces.pth]
  exact deriv_const_mul_uncond c (fun θ' => Ψ z θ') θ

/-- `∂_zz` commutes with scalar multiplication, unconditionally. -/
lemma pzIter_two_const_mul (c : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter 2 (fun z θ => c * Ψ z θ) z θ = c * Work.Spaces.pzIter 2 Ψ z θ := by
  rw [Work.Elliptic.pzIter_eq_iteratedDeriv 2 (fun z θ => c * Ψ z θ) z θ,
    Work.Elliptic.pzIter_eq_iteratedDeriv 2 Ψ z θ]
  exact congrFun (iteratedDeriv_const_mul_uncond 2 c (fun z' => Ψ z' θ)) z

/-- `∂_θθ` commutes with scalar multiplication, unconditionally. -/
lemma pthIter_two_const_mul (c : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 (fun z θ => c * Ψ z θ) z θ = c * Work.Spaces.pthIter 2 Ψ z θ := by
  rw [Work.Elliptic.pthIter_eq_iteratedDeriv 2 (fun z θ => c * Ψ z θ) z θ,
    Work.Elliptic.pthIter_eq_iteratedDeriv 2 Ψ z θ]
  exact congrFun (iteratedDeriv_const_mul_uncond 2 c (fun θ' => Ψ z θ')) θ

/-- `∂_θ(tan θ · ·)` commutes with scalar multiplication, unconditionally: the functions
`θ ↦ tan θ * (c * Ψ z θ)` and `θ ↦ c * (tan θ * Ψ z θ)` are equal pointwise, and the second one
has derivative `c` times that of `θ ↦ tan θ * Ψ z θ` by `deriv_const_mul_uncond`, *even at
`θ = π/2` where `tan` is not differentiable*. -/
lemma pth_tan_mul_const_mul (c : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z θ => Real.tan θ * (c * Ψ z θ)) z θ
      = c * Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ := by
  simp only [Work.Spaces.pth]
  have key : (fun θ' : ℝ => Real.tan θ' * (c * Ψ z θ'))
      = (fun θ' : ℝ => c * (Real.tan θ' * Ψ z θ')) := by
    funext θ'; ring
  rw [key]
  exact deriv_const_mul_uncond c (fun θ' => Real.tan θ' * Ψ z θ') θ

/-! ## `L₀` and `bslOp` -/

/-- `L₀` commutes with scalar multiplication, with no hypothesis at all. -/
lemma Lzero_const_mul (c : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (fun z θ => c * Ψ z θ) z θ = c * Work.Elliptic.Lzero Ψ z θ := by
  have h2 := pthIter_two_const_mul c Ψ z θ
  have ht := pth_tan_mul_const_mul c Ψ z θ
  simp only [Work.Elliptic.Lzero, h2, ht]
  ring

/-- `bslOp α` is homogeneous: it is a constant-coefficient (in the radial variable, after the
`D_z`-rewriting) linear operator, so it commutes with multiplication by a scalar. -/
theorem bslOp_const_mul (α c : ℝ) (Φ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hΦ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2) (z, θ)) :
    Work.Elliptic.bslOp α (fun z θ => c * Φ z θ) z θ
      = c * Work.Elliptic.bslOp α Φ z θ := by
  have h2 := pzIter_two_const_mul c Φ z θ
  have h1 := pz_const_mul c Φ z θ
  have hL := Lzero_const_mul c Φ z θ
  simp only [Work.Elliptic.bslOp_apply, h2, h1, hL]
  ring

end Work.R1G3
end
end
-- ===== merged: Submission.Work.R1G3.bslOp_scale =====
section

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
end
