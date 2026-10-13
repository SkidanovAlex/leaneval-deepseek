/-
Work module for `annals_finite_time_singularity`: elementary facts about the transported operator
`kopDr` (its locality), the operator `bslOp` (its locality and action on `0`), and the `exp`/`rpow`
algebra of the change of variables `z = exp (ασ)`.

This module is imported both by `exists_pullback` and by the transport module.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.EllipticEst.InteriorRegularity.Q0.RRKop
import Submission.Work.EllipticEst.InteriorRegularity.Q0.bslOp_congr_of_isOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## `exp`/`rpow` algebra -/

theorem exp_mul_rpow {α σ : ℝ} (hα : α ≠ 0) :
    (Real.exp (α * σ)) ^ ((5 - α) / α) = Real.exp ((5 - α) * σ) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  field_simp

theorem exp_alpha_eq_self {α : ℝ} (hα : 0 < α) {z : ℝ} (hz : 0 < z) :
    Real.exp (α * ((1 / α) * Real.log z)) = z := by
  have h1 : α * ((1 / α) * Real.log z) = Real.log z := by field_simp
  rw [h1, Real.exp_log hz]

theorem continuous_wtRR (α : ℝ) : Continuous (fun q : ℝ × ℝ => wtRR α q.1 q.2) := by
  have h : (fun q : ℝ × ℝ => wtRR α q.1 q.2)
      = fun q : ℝ × ℝ => α * Real.exp (5 * q.1) * Real.cos q.2 := rfl
  rw [h]
  fun_prop

/-! ## Locality of `kopDr` -/

theorem deriv_eq_zero_of_eventuallyEq_zero {f : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] 0) :
    deriv f x = 0 := by
  rw [h.deriv_eq]
  exact deriv_const x 0

/-- `kopDr ψ` vanishes outside the (topological) support of `ψ`. -/
theorem kopDr_eq_zero_of_notMem_tsupport {ψ : ℝ → ℝ → ℝ} {σ θ : ℝ}
    (h : (σ, θ) ∉ tsupport (Function.uncurry ψ)) : kopDr ψ σ θ = 0 := by
  have hev : Function.uncurry ψ =ᶠ[𝓝 (σ, θ)] 0 := notMem_tsupport_iff_eventuallyEq.mp h
  have hslσ : (fun σ' : ℝ => ψ σ' θ) =ᶠ[𝓝 σ] 0 := by
    have h1 := hev.comp_tendsto (g := fun σ' : ℝ => (σ', θ))
      (show Tendsto (fun σ' : ℝ => (σ', θ)) (𝓝 σ) (𝓝 (σ, θ)) from by
        rw [nhds_prod_eq]; exact tendsto_id.prodMk tendsto_const_nhds)
    have heq : (Function.uncurry ψ ∘ fun σ' : ℝ => (σ', θ)) = fun σ' => ψ σ' θ := by
      funext σ'; rfl
    have hz : ((0 : ℝ × ℝ → ℝ) ∘ fun σ' : ℝ => (σ', θ)) = 0 := by
      funext σ'; rfl
    rwa [heq, hz] at h1
  have hslθ : (fun θ' : ℝ => ψ σ θ') =ᶠ[𝓝 θ] 0 := by
    have h1 := hev.comp_tendsto (g := fun θ' : ℝ => (σ, θ'))
      (show Tendsto (fun θ' : ℝ => (σ, θ')) (𝓝 θ) (𝓝 (σ, θ)) from by
        rw [nhds_prod_eq]; exact tendsto_const_nhds.prodMk tendsto_id)
    have heq : (Function.uncurry ψ ∘ fun θ' : ℝ => (σ, θ')) = fun θ' => ψ σ θ' := by
      funext θ'; rfl
    have hz : ((0 : ℝ × ℝ → ℝ) ∘ fun θ' : ℝ => (σ, θ')) = 0 := by
      funext θ'; rfl
    rwa [heq, hz] at h1
  have hzero : deriv (0 : ℝ → ℝ) = 0 := funext fun x => deriv_const x 0
  have hval : ψ σ θ = 0 := by
    have := hev.eq_of_nhds
    simpa [Function.uncurry] using this
  have hdσ : deriv (fun σ' : ℝ => ψ σ' θ) σ = 0 := deriv_eq_zero_of_eventuallyEq_zero hslσ
  have hdθ : deriv (fun θ' : ℝ => ψ σ θ') θ = 0 := deriv_eq_zero_of_eventuallyEq_zero hslθ
  have hslσ'd : deriv (fun σ'' : ℝ => ψ σ'' θ) =ᶠ[𝓝 σ] 0 := by
    have h1 := hslσ.deriv
    rwa [hzero] at h1
  have hslθ'd : deriv (fun θ'' : ℝ => ψ σ θ'') =ᶠ[𝓝 θ] 0 := by
    have h1 := hslθ.deriv
    rwa [hzero] at h1
  have h2σ : deriv (fun σ' : ℝ => deriv (fun σ'' : ℝ => ψ σ'' θ) σ') σ = 0 :=
    deriv_eq_zero_of_eventuallyEq_zero hslσ'd
  have h2θ : deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => ψ σ θ'') θ') θ = 0 :=
    deriv_eq_zero_of_eventuallyEq_zero hslθ'd
  simp only [kopDr, hval, hdσ, hdθ, h2σ, h2θ]
  ring

theorem support_kopDr_subset {ψ : ℝ → ℝ → ℝ} :
    Function.support (fun q : ℝ × ℝ => kopDr ψ q.1 q.2) ⊆ tsupport (Function.uncurry ψ) := by
  intro q hq
  by_contra hcon
  exact hq (kopDr_eq_zero_of_notMem_tsupport hcon)

/-! ## The operator `bslOp` on `0`, and its locality -/

theorem pzIter_zero_eq (n : ℕ) :
    Work.Spaces.pzIter n (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.pzIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.pz, deriv_const]

theorem pthIter_zero_eq (n : ℕ) :
    Work.Spaces.pthIter n (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.pthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.pth, deriv_const]

theorem bslOp_zero (α z θ : ℝ) :
    Work.Elliptic.bslOp α (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
  have h1 : Work.Spaces.pzIter 2 (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
    rw [pzIter_zero_eq 2]
  have h2 : Work.Spaces.pz (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
    simp [Work.Spaces.pz]
  have h3 : Work.Spaces.pthIter 2 (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
    rw [pthIter_zero_eq 2]
  have h4 : Work.Spaces.pth
      (fun z θ : ℝ => Real.tan θ * (fun _ _ : ℝ => (0 : ℝ)) z θ) z θ = 0 := by
    have : (fun z θ : ℝ => Real.tan θ * (fun _ _ : ℝ => (0 : ℝ)) z θ)
        = fun _ _ : ℝ => (0 : ℝ) := by
      funext z θ; simp
    rw [this]; simp [Work.Spaces.pth]
  rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, h1, h2, h3, h4]
  ring

/-- `bslOp α φ` vanishes outside the (topological) support of `φ`. -/
theorem bslOp_eq_zero_of_notMem_tsupport {α : ℝ} {φ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : (z, θ) ∉ tsupport (Function.uncurry φ)) : Work.Elliptic.bslOp α φ z θ = 0 := by
  have hV : IsOpen (tsupport (Function.uncurry φ))ᶜ := (isClosed_tsupport _).isOpen_compl
  have hEq : Set.EqOn (Function.uncurry φ)
      (Function.uncurry (fun _ _ : ℝ => (0 : ℝ))) (tsupport (Function.uncurry φ))ᶜ := by
    intro p hp
    simp only [Function.uncurry]
    by_contra hne
    exact hp (subset_tsupport _ (Function.mem_support.mpr hne))
  have hcongr := bslOp_congr_of_isOpen (α := α) hV hEq h
  exact hcongr.trans (bslOp_zero α z θ)

end Work.EllipticEst.InteriorRegularity.Q0
