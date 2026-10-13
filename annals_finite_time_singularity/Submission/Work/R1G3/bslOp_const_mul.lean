/-
# Scalar homogeneity of the elliptic operator `bslOp`

`bslOp α Ψ = -α²z²∂_zzΨ - α(5+α)z∂_zΨ + L₀Ψ` with
`L₀Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` (see `Submission/Work/Elliptic/Defs.lean`) is a
constant-coefficient linear differential operator, so it commutes with multiplication of the
unknown by a scalar:

  `bslOp α (fun z θ => c * Ψ z θ) z θ = c * bslOp α Ψ z θ`

at every `(z,θ)`.

**No `cos θ ≠ 0` hypothesis is needed.**  In `bslOp_add` the corresponding additivity statement
carries the hypothesis `Real.cos θ ≠ 0`, because `deriv (f + g) = deriv f + deriv g` genuinely
needs differentiability of `f` and `g`, which the angular factor `tan θ` fails to have at
`θ = π/2` (`tan` is *not* continuous there under Lean's totalised convention `tan θ = sin θ/cos θ`,
`1/0 = 0`).  For scalar multiplication the situation is different: the identity

  `deriv (fun y => c * f y) x = c * deriv f x`

holds for **arbitrary** `f : ℝ → ℝ`, `c : ℝ`, `x : ℝ`.  Indeed, if `c = 0` both sides vanish; if
`c ≠ 0` then `c * f` is differentiable at `x` iff `f` is, and `deriv` of a non-differentiable
function is `0` by convention.  Composing this with itself gives the same identity for
`iteratedDeriv n`, again with no smoothness hypothesis.  This is the whole content of the proof
below: the `hΦ : ContDiffAt ℝ 2 …` hypothesis of the statement is *not* needed (it is retained
because the statement is used in a `C²` context), and the argument is pure `ring` after the
pointwise linearity of `∂_z`, `∂_zz`, `∂_θθ` and `∂_θ(tan θ · ·)` has been recorded.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.R1G3.Defs
import Submission.Work.Elliptic.bslOp_add

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
