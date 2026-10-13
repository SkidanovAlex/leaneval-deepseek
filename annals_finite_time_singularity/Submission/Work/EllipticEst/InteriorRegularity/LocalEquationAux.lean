import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.InteriorRegularity.Strip
import Submission.Work.EllipticEst.InteriorRegularity.curryC_bridge
import Submission.Work.EllipticEst.InteriorRegularity.Q0.lineDerivOp_smulLeftCLM

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.EllipticEst.InteriorRegularity

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

namespace Loc

/-! ## Leibniz rules and basic calculus facts for `d0`, `d1` -/

theorem d0_mul {f g : E2 → ℂ} {x : E2} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    d0 (fun y => f y * g y) x = f x * d0 g x + d0 f x * g x :=
  Q0.lineDeriv_mul_eq (m := e0) hf hg

theorem d1_mul {f g : E2 → ℂ} {x : E2} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    d1 (fun y => f y * g y) x = f x * d1 g x + d1 f x * g x :=
  Q0.lineDeriv_mul_eq (m := e1) hf hg

theorem d0_add {f g : E2 → ℂ} {x : E2} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : d0 (f + g) x = d0 f x + d0 g x := by
  simp only [d0, Pi.add_apply]
  rw [(hf.add hg).lineDeriv_eq_fderiv, hf.lineDeriv_eq_fderiv, hg.lineDeriv_eq_fderiv,
    fderiv_add hf hg]
  rfl

theorem d1_add {f g : E2 → ℂ} {x : E2} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : d1 (f + g) x = d1 f x + d1 g x := by
  simp only [d1, Pi.add_apply]
  rw [(hf.add hg).lineDeriv_eq_fderiv, hf.lineDeriv_eq_fderiv, hg.lineDeriv_eq_fderiv,
    fderiv_add hf hg]
  rfl

theorem d0_congr {f g : E2 → ℂ} {x : E2} (h : f =ᶠ[𝓝 x] g) : d0 f x = d0 g x := by
  simp only [d0]
  rw [h.lineDeriv_eq]

theorem d1_congr {f g : E2 → ℂ} {x : E2} (h : f =ᶠ[𝓝 x] g) : d1 f x = d1 g x := by
  simp only [d1]
  rw [h.lineDeriv_eq]

theorem d0_eq_zero_of_eventuallyEq_zero {f : E2 → ℂ} {x : E2} (h : f =ᶠ[𝓝 x] 0) :
    d0 f x = 0 := by
  rw [d0_congr h]
  simp [d0, lineDeriv]

theorem d1_eq_zero_of_eventuallyEq_zero {f : E2 → ℂ} {x : E2} (h : f =ᶠ[𝓝 x] 0) :
    d1 f x = 0 := by
  rw [d1_congr h]
  simp [d1, lineDeriv]

/-- The second order Leibniz rule for `d0`. -/
theorem d0_d0_mul {f g : E2 → ℂ} (hf : ∀ y, DifferentiableAt ℝ f y)
    (hg : ∀ y, DifferentiableAt ℝ g y) (hf' : ∀ y, DifferentiableAt ℝ (d0 f) y)
    (hg' : ∀ y, DifferentiableAt ℝ (d0 g) y) (x : E2) :
    d0 (d0 (fun y => f y * g y)) x
      = d0 (d0 f) x * g x + 2 * (d0 f x * d0 g x) + f x * d0 (d0 g) x := by
  have h1 : d0 (fun y => f y * g y) = fun y => f y * d0 g y + d0 f y * g y := by
    funext y
    rw [d0_mul (hf y) (hg y)]
  rw [h1]
  have h2 : d0 (fun y => f y * d0 g y + d0 f y * g y) x
      = d0 (fun y => f y * d0 g y) x + d0 (fun y => d0 f y * g y) x := by
    rw [show (fun y => f y * d0 g y + d0 f y * g y)
        = (fun y => f y * d0 g y) + (fun y => d0 f y * g y) from rfl]
    exact d0_add ((hf x).mul (hg' x)) ((hf' x).mul (hg x))
  rw [h2,
    show d0 (fun y => f y * d0 g y) x = f x * d0 (d0 g) x + d0 f x * d0 g x from
      d0_mul (hf x) (hg' x),
    show d0 (fun y => d0 f y * g y) x = d0 f x * d0 g x + d0 (d0 f) x * g x from
      d0_mul (hf' x) (hg x)]
  ring

/-- The second order Leibniz rule for `d1`. -/
theorem d1_d1_mul {f g : E2 → ℂ} (hf : ∀ y, DifferentiableAt ℝ f y)
    (hg : ∀ y, DifferentiableAt ℝ g y) (hf' : ∀ y, DifferentiableAt ℝ (d1 f) y)
    (hg' : ∀ y, DifferentiableAt ℝ (d1 g) y) (x : E2) :
    d1 (d1 (fun y => f y * g y)) x
      = d1 (d1 f) x * g x + 2 * (d1 f x * d1 g x) + f x * d1 (d1 g) x := by
  have h1 : d1 (fun y => f y * g y) = fun y => f y * d1 g y + d1 f y * g y := by
    funext y
    rw [d1_mul (hf y) (hg y)]
  rw [h1]
  have h2 : d1 (fun y => f y * d1 g y + d1 f y * g y) x
      = d1 (fun y => f y * d1 g y) x + d1 (fun y => d1 f y * g y) x := by
    rw [show (fun y => f y * d1 g y + d1 f y * g y)
        = (fun y => f y * d1 g y) + (fun y => d1 f y * g y) from rfl]
    exact d1_add ((hf x).mul (hg' x)) ((hf' x).mul (hg x))
  rw [h2,
    show d1 (fun y => f y * d1 g y) x = f x * d1 (d1 g) x + d1 f x * d1 g x from
      d1_mul (hf x) (hg' x),
    show d1 (fun y => d1 f y * g y) x = d1 f x * d1 g x + d1 (d1 f) x * g x from
      d1_mul (hf' x) (hg x)]
  ring

/-- The derivative of `θ ↦ tan θ` along `e₁`. -/
theorem d1_tan (x : E2) (hx : Real.cos (x 1) ≠ 0) :
    d1 (fun y : E2 => (Real.tan (y 1) : ℂ)) x = ((Real.cos (x 1))⁻¹ ^ 2 : ℂ) := by
  have hshift : (fun t : ℝ => ((fun y : E2 => (Real.tan (y 1) : ℂ)) (x + t • e1)))
      = fun t : ℝ => (Real.tan ((x 1) + t) : ℂ) := by
    funext t
    rw [add_smul_e1_coords]
    rfl
  rw [d1, lineDeriv, hshift]
  rw [deriv_comp_const_add (f := fun t : ℝ => (Real.tan t : ℂ)) (a := x 1) (x := (0 : ℝ))]
  simp only [add_zero]
  have hd : HasDerivAt (fun t : ℝ => (Real.tan t : ℂ))
      (((1 / Real.cos (x 1) ^ 2 : ℝ)) : ℂ) (x 1) :=
    (Real.hasDerivAt_tan hx).ofReal_comp
  rw [hd.deriv]
  have hscal : ((1 / Real.cos (x 1) ^ 2 : ℝ)) = (Real.cos (x 1))⁻¹ ^ 2 := by
    rw [one_div, inv_pow]
  rw [hscal]
  norm_cast

/-- `d0` of a constant multiple. -/
theorem d0_const_mul (c : ℂ) {f : E2 → ℂ} {x : E2} (hf : DifferentiableAt ℝ f x) :
    d0 (fun y => c * f y) x = c * d0 f x := by
  rw [d0, d0, lineDeriv, lineDeriv]
  have h3 : HasDerivAt (fun t : ℝ => x + t • e0) e0 (0 : ℝ) := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e0).const_add x
  have h2 : DifferentiableAt ℝ (fun t : ℝ => f (x + t • e0)) (0 : ℝ) :=
    (show DifferentiableAt ℝ f (x + (0 : ℝ) • e0) from by simpa using hf).comp (0 : ℝ)
      h3.differentiableAt
  rw [deriv_const_mul c h2]

/-- `d1` of a constant multiple. -/
theorem d1_const_mul (c : ℂ) {f : E2 → ℂ} {x : E2} (hf : DifferentiableAt ℝ f x) :
    d1 (fun y => c * f y) x = c * d1 f x := by
  rw [d1, d1, lineDeriv, lineDeriv]
  have h3 : HasDerivAt (fun t : ℝ => x + t • e1) e1 (0 : ℝ) := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e1).const_add x
  have h2 : DifferentiableAt ℝ (fun t : ℝ => f (x + t • e1)) (0 : ℝ) :=
    (show DifferentiableAt ℝ f (x + (0 : ℝ) • e1) from by simpa using hf).comp (0 : ℝ)
      h3.differentiableAt
  rw [deriv_const_mul c h2]

/-- `d0` of a constant function. -/
theorem d0_const (c : ℂ) (x : E2) : d0 (fun _ : E2 => c) x = 0 := by
  simp [d0, lineDeriv]

/-- `d1` of a constant function. -/
theorem d1_const (c : ℂ) (x : E2) : d1 (fun _ : E2 => c) x = 0 := by
  simp [d1, lineDeriv]

/-- `d0` of a `C^∞` function is `C^∞`. -/
theorem contDiff_d0 {f : E2 → ℂ} (hf : ∀ n : ℕ, ContDiff ℝ n f) (n : ℕ) :
    ContDiff ℝ n (d0 f) := by
  have hfd : d0 f = fun x => fderiv ℝ f x e0 := by
    funext x
    rw [d0, DifferentiableAt.lineDeriv_eq_fderiv]
    exact (hf 1).differentiable (by norm_num) x
  rw [hfd]
  have hmain : ContDiff ℝ n (fun p : E2 × E2 => fderiv ℝ f p.1 p.2) :=
    (hf (n + 1)).contDiff_fderiv_apply (by simp)
  have hg : ContDiff ℝ n (fun x : E2 => (x, e0)) :=
    ContDiff.prodMk (contDiff_id : ContDiff ℝ n (id : E2 → E2))
      (contDiff_const : ContDiff ℝ n (fun _ : E2 => e0))
  exact hmain.comp hg

/-- `d1` of a `C^∞` function is `C^∞`. -/
theorem contDiff_d1 {f : E2 → ℂ} (hf : ∀ n : ℕ, ContDiff ℝ n f) (n : ℕ) :
    ContDiff ℝ n (d1 f) := by
  have hfd : d1 f = fun x => fderiv ℝ f x e1 := by
    funext x
    rw [d1, DifferentiableAt.lineDeriv_eq_fderiv]
    exact (hf 1).differentiable (by norm_num) x
  rw [hfd]
  have hmain : ContDiff ℝ n (fun p : E2 × E2 => fderiv ℝ f p.1 p.2) :=
    (hf (n + 1)).contDiff_fderiv_apply (by simp)
  have hg : ContDiff ℝ n (fun x : E2 => (x, e1)) :=
    ContDiff.prodMk (contDiff_id : ContDiff ℝ n (id : E2 → E2))
      (contDiff_const : ContDiff ℝ n (fun _ : E2 => e1))
  exact hmain.comp hg

/-- `1 + tan² = 1/cos²`, in `ℂ`, for `cos θ ≠ 0`. -/
theorem one_add_tan_sq (θ : ℝ) (h : Real.cos θ ≠ 0) :
    (1 : ℂ) + ((Real.tan θ : ℂ)) ^ 2 = (((Real.cos θ : ℂ))⁻¹) ^ 2 := by
  have hr : (1 + Real.tan θ ^ 2 : ℝ) = ((Real.cos θ)⁻¹) ^ 2 := by
    rw [show (1 + Real.tan θ ^ 2 : ℝ) = (Real.cos θ ^ 2)⁻¹ by
        rw [← inv_inv (1 + Real.tan θ ^ 2), Real.inv_one_add_tan_sq h],
      ← inv_pow]
  have e1 : (1 : ℂ) + ((Real.tan θ : ℂ)) ^ 2 = ((1 + Real.tan θ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one]
  have e2 : (((Real.cos θ : ℂ))⁻¹) ^ 2 = (((Real.cos θ)⁻¹) ^ 2 : ℝ) := by
    rw [Complex.ofReal_pow, Complex.ofReal_inv]
  rw [e1, e2, hr]

/-- `d1` of `tan (· 1)`, in the form `1 + tan²`. -/
theorem d1_tan' (x : E2) (hx : Real.cos (x 1) ≠ 0) :
    d1 (fun y : E2 => (Real.tan (y 1) : ℂ)) x = 1 + ((Real.tan (x 1) : ℂ)) ^ 2 := by
  rw [d1_tan x hx, Complex.ofReal_inv]
  exact (one_add_tan_sq (x 1) hx).symm

/-- Linearity of the Bochner integral for an eight-term combination. -/
theorem integral_lin8 {f1 f2 f3 f4 f5 f6 f7 f8 : E2 → ℂ}
    (h1 : Integrable f1) (h2 : Integrable f2) (h3 : Integrable f3) (h4 : Integrable f4)
    (h5 : Integrable f5) (h6 : Integrable f6) (h7 : Integrable f7) (h8 : Integrable f8) :
    ∫ x, (f1 x + f2 x - f3 x + f4 x - f5 x + f6 x + f7 x + f8 x)
      = (∫ x, f1 x) + (∫ x, f2 x) - (∫ x, f3 x) + (∫ x, f4 x)
        - (∫ x, f5 x) + (∫ x, f6 x) + (∫ x, f7 x) + (∫ x, f8 x) := by
  have e2 : Integrable (fun x => f1 x + f2 x) := h1.add h2
  have e3 : Integrable (fun x => f1 x + f2 x - f3 x) := e2.sub h3
  have e4 : Integrable (fun x => f1 x + f2 x - f3 x + f4 x) := e3.add h4
  have e5 : Integrable (fun x => f1 x + f2 x - f3 x + f4 x - f5 x) := e4.sub h5
  have e6 : Integrable (fun x => f1 x + f2 x - f3 x + f4 x - f5 x + f6 x) := e5.add h6
  have e7 : Integrable (fun x => f1 x + f2 x - f3 x + f4 x - f5 x + f6 x + f7 x) := e6.add h7
  rw [integral_add e7 h8, integral_add e6 h7, integral_add e5 h6, integral_sub e4 h5,
      integral_add e3 h4, integral_sub e2 h3, integral_add h1 h2]

/-! ## The pointwise identity

The integrand of the weak formulation applied to `ψ = χ·φ`, plus the eight terms of the target
identity, vanish pointwise.  This is a product-rule computation: on the open set `U` the
multipliers `σ`, `tt`, `χ'` are `1`, `tan θ`, `1`; outside `U` (hence outside `tsupport χ`) the
cut-off `χ` and all its derivatives vanish. -/
theorem pointwise_identity {χ χ' σ tt φc : E2 → ℂ} {U : Set E2}
    (hU : IsOpen U) (htsU : tsupport χ ⊆ U) (hUsub : U ⊆ stripE)
    (hχs : ∀ n : ℕ, ContDiff ℝ n χ) (hχ's : ∀ n : ℕ, ContDiff ℝ n χ')
    (hσs : ∀ n : ℕ, ContDiff ℝ n σ) (htts : ∀ n : ℕ, ContDiff ℝ n tt)
    (hφs : ∀ n : ℕ, ContDiff ℝ n φc)
    (hσ1 : ∀ x ∈ U, σ x = 1) (htt1 : ∀ x ∈ U, tt x = (Real.tan (x 1) : ℂ))
    (hχ'1 : ∀ x ∈ U, χ' x = 1) (x : E2) :
    χ x * (d0 (d0 φc) x + d1 (d1 φc) x)
      + χ x * d0 (fun y => (5 * σ y) * φc y) x
      - χ x * d1 (fun y => (σ y * tt y) * φc y) x
      + χ x * (6 * σ x) * φc x
      - χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)
      + χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x
      + χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x
      + Kop (fun y => χ y * φc y) x = 0 := by
  have hχd : ∀ y : E2, DifferentiableAt ℝ χ y := fun y => (hχs 1).differentiable (by norm_num) y
  have hσd : ∀ y : E2, DifferentiableAt ℝ σ y := fun y => (hσs 1).differentiable (by norm_num) y
  have httd : ∀ y : E2, DifferentiableAt ℝ tt y := fun y => (htts 1).differentiable (by norm_num) y
  have hφd : ∀ y : E2, DifferentiableAt ℝ φc y := fun y => (hφs 1).differentiable (by norm_num) y
  have hd0χd : ∀ y : E2, DifferentiableAt ℝ (d0 χ) y :=
    fun y => (contDiff_d0 hχs 1).differentiable (by norm_num) y
  have hd1χd : ∀ y : E2, DifferentiableAt ℝ (d1 χ) y :=
    fun y => (contDiff_d1 hχs 1).differentiable (by norm_num) y
  have hd0φd : ∀ y : E2, DifferentiableAt ℝ (d0 φc) y :=
    fun y => (contDiff_d0 hφs 1).differentiable (by norm_num) y
  have hd1φd : ∀ y : E2, DifferentiableAt ℝ (d1 φc) y :=
    fun y => (contDiff_d1 hφs 1).differentiable (by norm_num) y
  have e2 : d0 (fun y => (5 * σ y) * φc y) x = (5 * σ x) * d0 φc x + (5 * d0 σ x) * φc x := by
    rw [d0_mul (f := fun y => 5 * σ y) (g := φc) (x := x)
        ((differentiableAt_const (c := (5 : ℂ))).mul (hσd x)) (hφd x),
      d0_const_mul (5 : ℂ) (hσd x)]
  have e3 : d1 (fun y => (σ y * tt y) * φc y) x
      = (σ x * tt x) * d1 φc x + (σ x * d1 tt x + d1 σ x * tt x) * φc x := by
    rw [d1_mul (f := fun y => σ y * tt y) (g := φc) (x := x) ((hσd x).mul (httd x)) (hφd x),
      d1_mul (f := σ) (g := tt) (x := x) (hσd x) (httd x)]
  have e4 : d0 (fun y => (2 * d0 χ y) * φc y) x
      = (2 * d0 χ x) * d0 φc x + (2 * d0 (d0 χ) x) * φc x := by
    rw [d0_mul (f := fun y => 2 * d0 χ y) (g := φc) (x := x)
        ((differentiableAt_const (c := (2 : ℂ))).mul (hd0χd x)) (hφd x),
      d0_const_mul (2 : ℂ) (hd0χd x)]
  have e5 : d1 (fun y => (2 * d1 χ y) * φc y) x
      = (2 * d1 χ x) * d1 φc x + (2 * d1 (d1 χ) x) * φc x := by
    rw [d1_mul (f := fun y => 2 * d1 χ y) (g := φc) (x := x)
        ((differentiableAt_const (c := (2 : ℂ))).mul (hd1χd x)) (hφd x),
      d1_const_mul (2 : ℂ) (hd1χd x)]
  have eK : Kop (fun y => χ y * φc y) x
      = - (d0 (d0 (fun y => χ y * φc y)) x) - (d1 (d1 (fun y => χ y * φc y)) x)
        - 5 * d0 (fun y => χ y * φc y) x
        + (Real.tan (x 1) : ℂ) * d1 (fun y => χ y * φc y) x
        + (((Real.tan (x 1)) ^ 2 - 5 : ℝ) : ℂ) * (χ x * φc x) := by
    rw [show Kop (fun y => χ y * φc y) = fun z : E2 =>
        - d0 (d0 (fun y => χ y * φc y)) z - d1 (d1 (fun y => χ y * φc y)) z
        - 5 * d0 (fun y => χ y * φc y) z
        + (Real.tan (z 1) : ℂ) * d1 (fun y => χ y * φc y) z
        + (((Real.tan (z 1)) ^ 2 - 5 : ℝ) : ℂ) * (χ z * φc z) from rfl]
  rw [e2, e3, e4, e5, eK]
  rw [d0_d0_mul (f := χ) (g := φc) hχd hφd hd0χd hd0φd x,
      d1_d1_mul (f := χ) (g := φc) hχd hφd hd1χd hd1φd x,
      d0_mul (f := χ) (g := φc) (x := x) (hχd x) (hφd x),
      d1_mul (f := χ) (g := φc) (x := x) (hχd x) (hφd x)]
  simp only [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_ofNat]
  by_cases hx : x ∈ U
  · have hσx : σ x = 1 := hσ1 x hx
    have httx : tt x = (Real.tan (x 1) : ℂ) := htt1 x hx
    have hχ'x : χ' x = 1 := hχ'1 x hx
    have hevσ : σ =ᶠ[𝓝 x] (fun _ : E2 => (1 : ℂ)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hσ1 y hy
    have hd0σ : d0 σ x = 0 := by rw [d0_congr hevσ, d0_const]
    have hd1σ : d1 σ x = 0 := by rw [d1_congr hevσ, d1_const]
    have hevtt : tt =ᶠ[𝓝 x] (fun y : E2 => (Real.tan (y 1) : ℂ)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact htt1 y hy
    have hcos : Real.cos (x 1) ≠ 0 := by
      have hx1 : x 1 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hUsub hx
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx1.1, Real.pi_pos], hx1.2⟩)
    have hd1tt : d1 tt x = 1 + ((Real.tan (x 1) : ℂ)) ^ 2 := by
      rw [d1_congr hevtt, d1_tan' x hcos]
    rw [hσx, httx, hχ'x, hd0σ, hd1σ, hd1tt]
    ring
  · have hxt : x ∉ tsupport χ := fun h => hx (htsU h)
    have hW : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
    have hxW : x ∈ (tsupport χ)ᶜ := hxt
    have hχ0W : ∀ y ∈ (tsupport χ)ᶜ, χ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
    have hevχ : χ =ᶠ[𝓝 x] (0 : E2 → ℂ) := Filter.eventuallyEq_of_mem (hW.mem_nhds hxW) hχ0W
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hxt
    have hd0χ : d0 χ x = 0 := d0_eq_zero_of_eventuallyEq_zero hevχ
    have hd1χ : d1 χ x = 0 := d1_eq_zero_of_eventuallyEq_zero hevχ
    have hevd0χ : d0 χ =ᶠ[𝓝 x] (0 : E2 → ℂ) :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hxW)
        (fun y hy => d0_eq_zero_of_eventuallyEq_zero
          (Filter.eventuallyEq_of_mem (hW.mem_nhds hy) hχ0W))
    have hevd1χ : d1 χ =ᶠ[𝓝 x] (0 : E2 → ℂ) :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hxW)
        (fun y hy => d1_eq_zero_of_eventuallyEq_zero
          (Filter.eventuallyEq_of_mem (hW.mem_nhds hy) hχ0W))
    have hd0d0χ : d0 (d0 χ) x = 0 := d0_eq_zero_of_eventuallyEq_zero hevd0χ
    have hd1d1χ : d1 (d1 χ) x = 0 := d1_eq_zero_of_eventuallyEq_zero hevd1χ
    rw [hχx, hd0χ, hd1χ, hd0d0χ, hd1d1χ]
    ring

/-- `d0` of a compactly supported function has compact support. -/
theorem hasCompactSupport_d0 {f : E2 → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (d0 f) := by
  refine IsCompact.of_isClosed_subset hf (isClosed_tsupport (d0 f))
    (closure_minimal ?_ (isClosed_tsupport f))
  intro x hx
  by_contra hxt
  exact hx (d0_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.mp hxt))

/-- `d1` of a compactly supported function has compact support. -/
theorem hasCompactSupport_d1 {f : E2 → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (d1 f) := by
  refine IsCompact.of_isClosed_subset hf (isClosed_tsupport (d1 f))
    (closure_minimal ?_ (isClosed_tsupport f))
  intro x hx
  by_contra hxt
  exact hx (d1_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.mp hxt))

end Loc

end Work.EllipticEst.InteriorRegularity
