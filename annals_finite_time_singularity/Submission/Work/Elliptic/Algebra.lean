/-
Copyright: work module for the Elgindi finite-time singularity project.

# Pointwise algebra of the elliptic operator `L` (paper §'Elliptic Regularity Estimates')

The elementary identities on which the elliptic section rests:

* `Work.Elliptic.Lzero_sin_two` : `L₀(sin 2θ) = 0` — `sin 2θ` lies in the kernel of the
  `α = 0` operator (paper line 279);
* `Work.Elliptic.bslOp_sin_two_mul` : `L(G(z) sin 2θ) = -(α²z²G'' + α(5+α)zG') sin 2θ` — the
  identity behind §'The singular term': the `sin 2θ`-part of `L` is purely radial, which is why
  adding a multiple of `sin 2θ` can be used to remove the solvability obstruction;
* `Work.Elliptic.Lzero_sin_two_mul` : the same computation with a `z`-dependent factor.

Everything here is pointwise and holds at every `θ` with `cos θ ≠ 0`; the only singularity of
`Real.tan` in `[0,π/2]` is the endpoint `θ = π/2`, which is a null set for every integral of the
estimates, so all the estimates hold almost everywhere on `[0,π/2]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Derivatives of the elementary angular functions -/

lemma deriv_sin_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  rw [h2.deriv]; ring

lemma deriv_cos_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.cos (2 * θ')) θ = -2 * Real.sin (2 * θ) := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-Real.sin (2 * θ) * 2) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ h1
  rw [h2.deriv]; ring

/-- `(2 cos 2θ)' = -4 sin 2θ`. -/
lemma deriv_two_cos_two (θ : ℝ) :
    deriv (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ = -4 * Real.sin (2 * θ) := by
  rw [deriv_const_mul_field, deriv_cos_two]
  ring

/-- The double `θ`-derivative of `sin 2θ`. -/
lemma pthIter_sin_two (z θ : ℝ) :
    Work.Spaces.pthIter 2 (fun (_ : ℝ) (θ : ℝ) => Real.sin (2 * θ)) z θ
      = -4 * Real.sin (2 * θ) := by
  have h1 : (fun θ' : ℝ => deriv (fun θ'' : ℝ => Real.sin (2 * θ'')) θ')
      = fun θ' => 2 * Real.cos (2 * θ') := by
    funext θ'; exact deriv_sin_two θ'
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth,
    Function.comp_apply]
  rw [h1, deriv_two_cos_two]

/-- `∂_θ(tan θ · sin 2θ) = 2 sin 2θ` (for `cos θ ≠ 0`). -/
lemma deriv_tan_mul_sin_two (θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    deriv (fun θ' : ℝ => Real.tan θ' * Real.sin (2 * θ')) θ = 2 * Real.sin (2 * θ) := by
  have hne : ∀ᶠ θ' in 𝓝 θ, Real.cos θ' ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hθ
  have heq : (fun θ' : ℝ => Real.tan θ' * Real.sin (2 * θ'))
      =ᶠ[𝓝 θ] fun θ' => 2 * Real.sin θ' ^ 2 := by
    filter_upwards [hne] with θ' h'
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp
  rw [heq.deriv_eq]
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * Real.sin θ' ^ 2) (4 * Real.sin θ * Real.cos θ) θ := by
    have h : HasDerivAt (fun x : ℝ => Real.sin x ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
      have h0 := (Real.hasDerivAt_sin θ).pow 2
      convert h0 using 1 <;> ring
    convert h.const_mul 2 using 1 <;> ring
  calc deriv (fun θ' : ℝ => 2 * Real.sin θ' ^ 2) θ
      = 4 * Real.sin θ * Real.cos θ := h2.deriv
    _ = 2 * Real.sin (2 * θ) := by rw [Real.sin_two_mul]; ring

/-! ## The kernel identity -/

/-- `L₀(sin 2θ) = 0`. -/
lemma Lzero_sin_two (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    Lzero (fun (_ : ℝ) (θ : ℝ) => Real.sin (2 * θ)) z θ = 0 := by
  rw [Lzero, pthIter_sin_two]
  have h : Work.Spaces.pth (fun z θ => Real.tan θ * Real.sin (2 * θ)) z θ
      = deriv (fun θ' : ℝ => Real.tan θ' * Real.sin (2 * θ')) θ := by
    simp only [Work.Spaces.pth, Function.comp_apply]
  rw [h, deriv_tan_mul_sin_two θ hθ]
  ring

/-- `L₀(g(z)·sin 2θ) = 0` for any `g`: the `sin 2θ` direction of the kernel survives
multiplication by a `z`-dependent factor. -/
lemma Lzero_sin_two_mul (g : ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    Lzero (fun z θ => g z * Real.sin (2 * θ)) z θ = 0 := by
  have h1 : Work.Spaces.pthIter 2 (fun z θ => g z * Real.sin (2 * θ)) z θ
      = g z * Work.Spaces.pthIter 2 (fun (_ : ℝ) (θ : ℝ) => Real.sin (2 * θ)) z θ := by
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth,
      Function.comp_apply, deriv_const_mul_field]
  have h3 : Work.Spaces.pth (fun z θ => Real.tan θ * (g z * Real.sin (2 * θ))) z θ
      = g z * Work.Spaces.pth (fun z θ => Real.tan θ * Real.sin (2 * θ)) z θ := by
    simp only [Work.Spaces.pth, Function.comp_apply]
    rw [show (fun θ' : ℝ => Real.tan θ' * (g z * Real.sin (2 * θ')))
        = fun θ' : ℝ => g z * (Real.tan θ' * Real.sin (2 * θ')) from by
      funext θ'; ring]
    rw [deriv_const_mul_field]
  rw [Lzero, h1, h3]
  have hL := Lzero_sin_two z θ hθ
  rw [Lzero] at hL
  linear_combination g z * hL

/-! ## The action of `L` on `G(z) sin 2θ` -/

/-- `L(G(z)·sin 2θ) = -(α²z²G'' + α(5+α)zG')·sin 2θ`: the radial and angular parts decouple on the
`sin 2θ` direction, which is what makes the singular term computable in closed form. -/
lemma bslOp_sin_two_mul (α : ℝ) (g : ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    bslOp α (fun z θ => g z * Real.sin (2 * θ)) z θ
      = -(α ^ 2 * z ^ 2 * deriv (fun z' : ℝ => deriv g z') z + α * (5 + α) * z * deriv g z)
          * Real.sin (2 * θ) := by
  have hpz1 : Work.Spaces.pz (fun z θ => g z * Real.sin (2 * θ)) z θ
      = deriv g z * Real.sin (2 * θ) := by
    simp only [Work.Spaces.pz, Function.comp_apply, deriv_mul_const_field]
  have hpz2 : Work.Spaces.pzIter 2 (fun z θ => g z * Real.sin (2 * θ)) z θ
      = deriv (fun z' : ℝ => deriv g z') z * Real.sin (2 * θ) := by
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz,
      Function.comp_apply, deriv_mul_const_field]
  have hL : Lzero (fun z θ => g z * Real.sin (2 * θ)) z θ = 0 :=
    Lzero_sin_two_mul g z θ hθ
  rw [bslOp_apply, hpz2, hpz1, hL]
  ring

end Work.Elliptic
