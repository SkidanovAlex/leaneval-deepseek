/-
The change of variables `z = exp (α s)` for the elliptic operator `bslOp` of
`Work.Elliptic` (`Submission/Work/Elliptic/Defs.lean`): for a function of the form
`φ (z,θ) = ψ ((1/α) log z, θ)` the operator becomes the constant-coefficient (in the
radial direction) operator

  `Kop ψ = -∂_ss ψ - ∂_θθ ψ - 5 ∂_s ψ + tan θ ∂_θ ψ + (tan²θ - 5) ψ`

at `(exp (α s), θ)`; this is `Work.EllipticEst.InteriorRegularity.Kop` of `Strip.lean`
in coordinates (`bslOp_comp_exp` is the `deriv`-level statement of that fact).

Proof: the radial part `-α²z²∂_zz - α(5+α)z∂_z` is computed from the chain rule for the
logarithm-composition (`deriv_comp_const_mul_log`, `deriv_deriv_comp_const_mul_log`
below), which turns `∂_z` into `(1/(αz)) ∂_s` and `∂_zz` into `(1/(αz))² ∂_ss - (1/(αz²)) ∂_s`,
so that at `z = exp (α s)` (where `(1/α) log z = s`)

  `-α²z² ∂_zz φ = -∂_ss ψ + α ∂_s ψ`,  `-α(5+α) z ∂_z φ = -(5+α) ∂_s ψ`.

The angular part is `Lzero`: `-∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`, and the product rule plus
`deriv tan θ = 1/cos²θ = 1 + tan²θ` (which is where `hcos` is used) gives
`tan θ ∂_θψ + (1 + tan²θ) ψ - 6ψ = tan θ ∂_θψ + (tan²θ - 5) ψ`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.EllipticEst.InteriorRegularity.Strip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter

namespace Work.EllipticEst.InteriorRegularity

/-- **First-order chain rule for a logarithm-composition.**  For `z ≠ 0` and `φ`
differentiable at `(1/α) log z`,
`d/dz [φ ((1/α) log z)] = φ'((1/α) log z) · 1/(α z)`. -/
lemma deriv_comp_const_mul_log (φ : ℝ → ℝ) {α z : ℝ} (hz : z ≠ 0)
    (hφ : DifferentiableAt ℝ φ ((1 / α) * Real.log z)) :
    deriv (fun w => φ ((1 / α) * Real.log w)) z
      = deriv φ ((1 / α) * Real.log z) * (1 / (α * z)) := by
  have hinner : DifferentiableAt ℝ (fun w : ℝ => (1 / α) * Real.log w) z :=
    (Real.differentiableAt_log hz).const_mul (1 / α)
  change deriv (φ ∘ fun w : ℝ => (1 / α) * Real.log w) z = _
  rw [deriv_comp (x := z) (h := fun w : ℝ => (1 / α) * Real.log w) (h₂ := φ) hφ hinner]
  have hd : deriv (fun w : ℝ => (1 / α) * Real.log w) z = 1 / (α * z) := by
    rw [deriv_const_mul (1/α) (Real.differentiableAt_log hz), Real.deriv_log, one_div,
      div_eq_mul_inv, mul_inv]
    ring
  rw [hd]

/-- **Second-order chain rule for a logarithm-composition.**  For `α ≠ 0`, `z ≠ 0`, `φ`
twice differentiable along the composition (hypotheses `hφ`, `hφd`),
`d²/dz² [φ ((1/α) log z)] = φ''((1/α) log z) /(α z)² - φ'((1/α) log z) /(α z²)`. -/
lemma deriv_deriv_comp_const_mul_log (φ : ℝ → ℝ) {α z : ℝ} (hα : α ≠ 0) (hz : z ≠ 0)
    (hφ : DifferentiableAt ℝ (deriv φ) ((1 / α) * Real.log z))
    (hφd : ∀ w, DifferentiableAt ℝ φ ((1 / α) * Real.log w)) :
    deriv (fun w => deriv (fun w' => φ ((1 / α) * Real.log w')) w) z
      = deriv (deriv φ) ((1 / α) * Real.log z) * (1 / (α * z)) * (1 / (α * z))
        - deriv φ ((1 / α) * Real.log z) * (1 / (α * z ^ 2)) := by
  have hinner : DifferentiableAt ℝ (fun w : ℝ => (1 / α) * Real.log w) z :=
    (Real.differentiableAt_log hz).const_mul (1 / α)
  have hev : (fun w => deriv (fun w' => φ ((1 / α) * Real.log w')) w)
      =ᶠ[nhds z] fun w => deriv φ ((1 / α) * Real.log w) * ((1 / α) * w⁻¹) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    rw [deriv_comp_const_mul_log φ hw (hφd w)]
    congr 1
    rw [one_div, div_eq_mul_inv, mul_inv]
    ring
  rw [hev.deriv_eq]
  have hA : DifferentiableAt ℝ (fun w : ℝ => deriv φ ((1 / α) * Real.log w)) z := by
    change DifferentiableAt ℝ ((deriv φ) ∘ fun w : ℝ => (1 / α) * Real.log w) z
    exact hφ.comp z hinner
  have hB : DifferentiableAt ℝ (fun w : ℝ => (1 / α) * w⁻¹) z :=
    (differentiableAt_id.inv hz).const_mul (1 / α)
  change deriv ((fun w : ℝ => deriv φ ((1 / α) * Real.log w)) * fun w : ℝ => (1 / α) * w⁻¹) z = _
  rw [deriv_mul hA hB]
  have hA' : deriv (fun w : ℝ => deriv φ ((1 / α) * Real.log w)) z
      = deriv (deriv φ) ((1 / α) * Real.log z) * (1 / (α * z)) := by
    change deriv ((deriv φ) ∘ fun w : ℝ => (1 / α) * Real.log w) z = _
    rw [deriv_comp (x := z) (h := fun w : ℝ => (1 / α) * Real.log w) (h₂ := deriv φ) hφ hinner]
    congr 1
    rw [deriv_const_mul (1/α) (Real.differentiableAt_log hz), Real.deriv_log, one_div,
      div_eq_mul_inv, mul_inv]
    ring
  have hB' : deriv (fun w : ℝ => (1 / α) * w⁻¹) z = -(1 / (α * z ^ 2)) := by
    rw [deriv_const_mul (1/α) (differentiableAt_id.inv hz), deriv_inv]
    field_simp
  rw [hA', hB']
  field_simp
  ring

theorem bslOp_comp_exp {α : ℝ} (hα : 0 < α) {ψ : ℝ → ℝ → ℝ}
    (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ)) {s θ : ℝ}
    (hcos : Real.cos θ ≠ 0) :
    Work.Elliptic.bslOp α (fun z θ' => ψ ((1 / α) * Real.log z) θ') (Real.exp (α * s)) θ
      = - deriv (fun s' => deriv (fun s'' => ψ s'' θ) s') s
        - deriv (fun θ' => deriv (fun θ'' => ψ s θ'') θ') θ
        - 5 * deriv (fun s' => ψ s' θ) s + Real.tan θ * deriv (fun θ' => ψ s θ') θ
        + ((Real.tan θ) ^ 2 - 5) * ψ s θ := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hexp : Real.exp (α * s) ≠ 0 := Real.exp_ne_zero _
  have hlog : (1 / α) * Real.log (Real.exp (α * s)) = s := by
    rw [Real.log_exp, ← mul_assoc, one_div, inv_mul_cancel₀ hαne, one_mul]
  -- smoothness of the `s`-slices, which is all the chain rule needs
  have hsmooth : ContDiff ℝ 2 (fun s' : ℝ => ψ s' θ) := by
    have h : ContDiff ℝ 2 (fun s' : ℝ => (s', θ)) := ContDiff.prodMk contDiff_id contDiff_const
    exact (hψ 2).comp h
  have hφdiff : DifferentiableAt ℝ (fun s' : ℝ => ψ s' θ)
      ((1 / α) * Real.log (Real.exp (α*s))) :=
    (hsmooth.differentiable (by norm_num)) _
  have hφ'diff : DifferentiableAt ℝ (deriv (fun s' : ℝ => ψ s' θ))
      ((1 / α) * Real.log (Real.exp (α*s))) := hsmooth.differentiable_deriv_two _
  have hφddiff : ∀ w, DifferentiableAt ℝ (fun s' : ℝ => ψ s' θ) ((1 / α) * Real.log w) :=
    fun w => (hsmooth.differentiable (by norm_num)) ((1 / α) * Real.log w)
  -- the values of `pz` and `pzIter 2`
  have h1 : Work.Spaces.pz (fun z θ' => ψ ((1 / α) * Real.log z) θ') (Real.exp (α*s)) θ
      = deriv (fun s' => ψ s' θ) s * (1 / (α * Real.exp (α*s))) := by
    change deriv (fun w : ℝ => ψ ((1 / α) * Real.log w) θ) (Real.exp (α*s)) = _
    rw [deriv_comp_const_mul_log (fun s' : ℝ => ψ s' θ) hexp hφdiff, hlog]
  have h2 : Work.Spaces.pzIter 2 (fun z θ' => ψ ((1 / α) * Real.log z) θ') (Real.exp (α*s)) θ
      = deriv (fun s' => deriv (fun s'' => ψ s'' θ) s') s * (1 / (α * Real.exp (α*s))) ^ 2
        - deriv (fun s' => ψ s' θ) s * (1 / (α * (Real.exp (α*s)) ^ 2)) := by
    change deriv (fun w : ℝ => deriv (fun w' : ℝ => ψ ((1 / α) * Real.log w') θ) w)
      (Real.exp (α*s)) = _
    rw [deriv_deriv_comp_const_mul_log (fun s' : ℝ => ψ s' θ) hαne hexp hφ'diff hφddiff, hlog]
    have hd2 : deriv (deriv (fun s' : ℝ => ψ s' θ)) s
        = deriv (fun s' => deriv (fun s'' => ψ s'' θ) s') s := rfl
    rw [hd2, pow_two]
    ring
  -- the angular values: `Lzero`'s two derivative slots and the value slot
  have h4 : Work.Spaces.pthIter 2 (fun z θ' => ψ ((1 / α) * Real.log z) θ') (Real.exp (α*s)) θ
      = deriv (fun θ' => deriv (fun θ'' => ψ s θ'') θ') θ := by
    change deriv (fun θ' : ℝ =>
      deriv (fun θ'' : ℝ => ψ ((1 / α) * Real.log (Real.exp (α*s))) θ'') θ') θ = _
    rw [hlog]
  have h5 : Work.Spaces.pth (fun z θ' => Real.tan θ' * ψ ((1 / α) * Real.log z) θ')
      (Real.exp (α*s)) θ
      = Real.tan θ * deriv (fun θ' => ψ s θ') θ + (1 + (Real.tan θ) ^ 2) * ψ s θ := by
    change deriv (fun θ' : ℝ =>
      Real.tan θ' * ψ ((1 / α) * Real.log (Real.exp (α*s))) θ') θ = _
    rw [hlog]
    have htansmooth : DifferentiableAt ℝ Real.tan θ := (Real.differentiableAt_tan).mpr hcos
    have htsmooth : DifferentiableAt ℝ (fun θ' : ℝ => ψ s θ') θ := by
      have h : ContDiff ℝ 2 (fun θ' : ℝ => ψ s θ') := by
        have h2 : ContDiff ℝ 2 (fun θ' : ℝ => (s, θ')) :=
          ContDiff.prodMk contDiff_const contDiff_id
        exact (hψ 2).comp h2
      exact (h.differentiable (by norm_num)) θ
    change deriv (Real.tan * fun θ' : ℝ => ψ s θ') θ = _
    rw [deriv_mul htansmooth htsmooth, Real.deriv_tan]
    have hsec : (1 : ℝ) / Real.cos θ ^ 2 = 1 + Real.tan θ ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
      linear_combination -Real.sin_sq_add_cos_sq θ
    rw [hsec]
    ring
  rw [Work.Elliptic.bslOp, Work.Elliptic.Lzero]
  rw [h1, h2, h4, h5, hlog]
  field_simp
  ring

end Work.EllipticEst.InteriorRegularity
