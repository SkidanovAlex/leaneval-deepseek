import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Distribution.DerivNotation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.LocalEquationAux =====
section

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
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.laplacian_smulLeftCLM =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

open MeasureTheory TemperedDistribution Filter Set
open scoped SchwartzMap LineDeriv Laplacian

set_option maxHeartbeats 1000000

/-! ### Elementary pointwise calculus on `E2` -/



/-! ### The Schwartz-map level -/

/-- The coercion of the line derivative of a Schwartz map is the pointwise line derivative. -/
theorem lineDerivOp_coe (m : E2) (ψ : 𝓢(E2, ℂ)) :
    (⇑(LineDeriv.lineDerivOp m ψ) : E2 → ℂ) = fun y => lineDeriv ℝ (⇑ψ) y m := by
  funext y
  rw [SchwartzMap.lineDerivOp_apply]


/-- The Laplacian of a Schwartz map, evaluated in the basis `(e0, e1)`. -/
theorem schwartzMap_laplacian_apply (ψ : 𝓢(E2, ℂ)) (x : E2) :
    Laplacian.laplacian ψ x
      = lineDeriv ℝ (fun y => lineDeriv ℝ (⇑ψ) y e0) x e0
        + lineDeriv ℝ (fun y => lineDeriv ℝ (⇑ψ) y e1) x e1 := by
  rw [SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 2) ℝ), Fin.sum_univ_two,
    add_apply, SchwartzMap.lineDerivOp_apply, lineDerivOp_coe, SchwartzMap.lineDerivOp_apply,
    lineDerivOp_coe]
  simp only [e0, e1]



/-! ### The distributional Leibniz rule -/


end Work.EllipticEst.InteriorRegularity.Q0
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.VT.DerivAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap LineDeriv ContDiff

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem finrank_E2 : Module.finrank ℝ E2 = 2 := by
  rw [finrank_euclideanSpace_fin]

/-- The zeroth-order commutator coefficient `Δχ - 5 ∂₀χ + tt ∂₁χ`. -/
def rho0 (χ tt : E2 → ℂ) : E2 → ℂ :=
  fun x => d0 (d0 χ) x + d1 (d1 χ) x - 5 * d0 χ x + tt x * d1 χ x

theorem contDiff_d0 {f : E2 → ℂ} (hf : ∀ k : ℕ, ContDiff ℝ k f) (n : ℕ) :
    ContDiff ℝ n (fun x => d0 f x) := by
  have h1 : ContDiff ℝ (n : ℕ∞ω) (fun p : E2 × E2 => (fderiv ℝ f p.1) p.2) :=
    ContDiff.contDiff_fderiv_apply (𝕜 := ℝ) (f := f)
      (n := ((n + 1 : ℕ) : ℕ∞ω)) (m := (n : ℕ∞ω)) (hf (n + 1)) (by push_cast; norm_num)
  have h2 : ContDiff ℝ (n : ℕ∞ω) (fun x : E2 => (fderiv ℝ f x) e0) :=
    h1.comp (ContDiff.prodMk contDiff_id contDiff_const)
  have h3 : (fun x : E2 => d0 f x) = fun x : E2 => (fderiv ℝ f x) e0 := by
    funext x
    exact (hf 1).differentiable (by norm_num) x |>.lineDeriv_eq_fderiv
  rwa [h3]

theorem contDiff_d1 {f : E2 → ℂ} (hf : ∀ k : ℕ, ContDiff ℝ k f) (n : ℕ) :
    ContDiff ℝ n (fun x => d1 f x) := by
  have h1 : ContDiff ℝ (n : ℕ∞ω) (fun p : E2 × E2 => (fderiv ℝ f p.1) p.2) :=
    ContDiff.contDiff_fderiv_apply (𝕜 := ℝ) (f := f)
      (n := ((n + 1 : ℕ) : ℕ∞ω)) (m := (n : ℕ∞ω)) (hf (n + 1)) (by push_cast; norm_num)
  have h2 : ContDiff ℝ (n : ℕ∞ω) (fun x : E2 => (fderiv ℝ f x) e1) :=
    h1.comp (ContDiff.prodMk contDiff_id contDiff_const)
  have h3 : (fun x : E2 => d1 f x) = fun x : E2 => (fderiv ℝ f x) e1 := by
    funext x
    exact (hf 1).differentiable (by norm_num) x |>.lineDeriv_eq_fderiv
  rwa [h3]

theorem tsupport_d0_subset {f : E2 → ℂ} (hs : ∀ n : ℕ, ContDiff ℝ n f) :
    tsupport (fun x : E2 => d0 f x) ⊆ tsupport f := by
  have hfun : (fun x : E2 => d0 f x) = fun x : E2 => fderiv ℝ f x e0 := by
    funext x
    exact (hs 1).differentiable (by norm_num) x |>.lineDeriv_eq_fderiv
  rw [hfun]
  exact tsupport_fderiv_apply_subset (𝕜 := ℝ) e0

theorem tsupport_d1_subset {f : E2 → ℂ} (hs : ∀ n : ℕ, ContDiff ℝ n f) :
    tsupport (fun x : E2 => d1 f x) ⊆ tsupport f := by
  have hfun : (fun x : E2 => d1 f x) = fun x : E2 => fderiv ℝ f x e1 := by
    funext x
    exact (hs 1).differentiable (by norm_num) x |>.lineDeriv_eq_fderiv
  rw [hfun]
  exact tsupport_fderiv_apply_subset (𝕜 := ℝ) e1

theorem d0_eq_zero_of_notMem_tsupport {f : E2 → ℂ} (hs : ∀ n : ℕ, ContDiff ℝ n f) {x : E2}
    (hx : x ∉ tsupport f) : d0 f x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_d0_subset hs h)

theorem d1_eq_zero_of_notMem_tsupport {f : E2 → ℂ} (hs : ∀ n : ℕ, ContDiff ℝ n f) {x : E2}
    (hx : x ∉ tsupport f) : d1 f x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_d1_subset hs h)

theorem hasCompactSupport_of_tsupport_subset {f g : E2 → ℂ} (hf : HasCompactSupport f)
    (h : tsupport g ⊆ tsupport f) : HasCompactSupport g :=
  IsCompact.of_isClosed_subset hf (isClosed_tsupport g) h

theorem hasCompactSupport_d0 {f : E2 → ℂ} (hf : HasCompactSupport f)
    (hs : ∀ n : ℕ, ContDiff ℝ n f) : HasCompactSupport (fun x => d0 f x) :=
  hasCompactSupport_of_tsupport_subset hf (tsupport_d0_subset hs)

theorem hasCompactSupport_d1 {f : E2 → ℂ} (hf : HasCompactSupport f)
    (hs : ∀ n : ℕ, ContDiff ℝ n f) : HasCompactSupport (fun x => d1 f x) :=
  hasCompactSupport_of_tsupport_subset hf (tsupport_d1_subset hs)

theorem contDiff_rho0 {χ tt : E2 → ℂ} (hχs : ∀ n : ℕ, ContDiff ℝ n χ)
    (htts : ∀ n : ℕ, ContDiff ℝ n tt) (n : ℕ) : ContDiff ℝ n (rho0 χ tt) := by
  have h1 := contDiff_d0 (fun k => contDiff_d0 hχs k) n
  have h2 := contDiff_d1 (fun k => contDiff_d1 hχs k) n
  have h3 := contDiff_d0 hχs n
  have h4 := contDiff_d1 hχs n
  exact ((h1.add h2).sub (contDiff_const.mul h3)).add (htts n |>.mul h4)

theorem support_rho0_subset {χ tt : E2 → ℂ} (hχs : ∀ n : ℕ, ContDiff ℝ n χ) :
    Function.support (rho0 χ tt) ⊆ tsupport χ := by
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxn
  have hd0 : d0 χ x = 0 := d0_eq_zero_of_notMem_tsupport hχs hxn
  have hd1 : d1 χ x = 0 := d1_eq_zero_of_notMem_tsupport hχs hxn
  have htd : tsupport (fun y => d1 χ y) ⊆ tsupport χ := tsupport_d1_subset hχs
  have hd1' : d1 (d1 χ) x = 0 :=
    d1_eq_zero_of_notMem_tsupport (fun k => contDiff_d1 hχs k) (fun h => hxn (htd h))
  have hd0' : d0 (d0 χ) x = 0 :=
    d0_eq_zero_of_notMem_tsupport (fun k => contDiff_d0 hχs k)
      (fun h => hxn ((tsupport_d0_subset hχs) h))
  have hval : rho0 χ tt x = 0 := by
    simp only [rho0, hd0, hd1, hd1', hd0', mul_zero, sub_zero, add_zero]
  exact hx hval

theorem hasCompactSupport_rho0 {χ tt : E2 → ℂ} (hχc : HasCompactSupport χ)
    (hχs : ∀ n : ℕ, ContDiff ℝ n χ) : HasCompactSupport (rho0 χ tt) :=
  hasCompactSupport_of_tsupport_subset hχc (by
    rw [tsupport]
    exact (closure_mono (support_rho0_subset hχs)).trans
      (le_of_eq (isClosed_tsupport χ).closure_eq))


theorem abs_coord_le_norm (x : E2) (i : Fin 2) : |x i| ≤ ‖x‖ :=
  PiLp.norm_apply_le (p := 2) x i

/-- A point of the ball of radius `δ/2` around `x₀` has its second coordinate strictly inside
`(0, π/2)`, when `δ` measures the distance of `x₀` to the boundary of the strip. -/
theorem mem_Ioo_of_mem_ball {x₀ x : E2} {δ : ℝ} (hδ : 0 < δ) (hxδ : δ ≤ x₀ 1)
    (hyδ : δ ≤ Real.pi / 2 - x₀ 1) (hx : x ∈ Metric.ball x₀ (δ / 2)) :
    x 1 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hcoord : |x 1 - x₀ 1| ≤ ‖x - x₀‖ := by
    have h := abs_coord_le_norm (x - x₀) 1
    simpa using h
  constructor
  · have h := neg_le_abs (x 1 - x₀ 1)
    linarith
  · have h := le_abs_self (x 1 - x₀ 1)
    linarith

/-- `x ↦ tan (x 1)` is `C^∞` on a ball around `x₀` staying strictly inside the strip
`0 < x 1 < π/2`. -/
theorem contDiffOn_tan_coord {x₀ : E2} {δ : ℝ} (hδ : 0 < δ) (hxδ : δ ≤ x₀ 1)
    (hyδ : δ ≤ Real.pi / 2 - x₀ 1) (n : ℕ) :
    ContDiffOn ℝ n (fun x : E2 => (Real.tan (x 1) : ℂ)) (Metric.ball x₀ (δ / 2)) := by
  have htan : ContDiffOn ℝ n (fun y : ℝ => (Real.tan y : ℂ)) (Set.Ioo 0 (Real.pi / 2)) := by
    intro y hy
    have hcos : Real.cos y ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hy.1, Real.pi_pos], hy.2⟩)
    exact (ContDiffAt.comp y (Complex.ofRealCLM.contDiff.contDiffAt)
      ((Real.contDiffAt_tan).mpr hcos)).contDiffWithinAt
  refine htan.comp ?_ ?_
  · fun_prop
  · intro x hx
    exact mem_Ioo_of_mem_ball hδ hxδ hyδ hx

theorem hasCompactSupport_const_mul {f : E2 → ℂ} (hf : HasCompactSupport f) (c : ℂ) :
    HasCompactSupport (fun x => c * f x) :=
  hasCompactSupport_of_tsupport_subset hf (by
    rw [tsupport, tsupport]
    refine closure_mono ?_
    intro x hx
    rw [Function.mem_support] at hx
    rw [Function.mem_support]
    intro hfx
    exact hx (by rw [hfx, mul_zero]))

end Work.EllipticEst.InteriorRegularity.VT
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.VT.Smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 800000





/-- A compactly supported `C^∞` function is integrable. -/
theorem integrable_of_smooth_compact {f : E2 → ℂ} (hc : HasCompactSupport f)
    (hs : ∀ n : ℕ, ContDiff ℝ n f) : Integrable f := by
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_infty.mpr hs
  have hcoe : (⇑(hc.toSchwartzMap hfs) : E2 → ℂ) = f :=
    funext (HasCompactSupport.toSchwartzMap_toFun hc hfs)
  have h : Integrable (⇑(hc.toSchwartzMap hfs)) volume := (hc.toSchwartzMap hfs).integrable
  rwa [hcoe] at h

end Work.EllipticEst.InteriorRegularity.VT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.radIter_Bmom_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {F : ℝ → ℝ → ℝ}

/-! ## The moment tower

`B_{j+1}(s)/s` is the derivative of `B_j`; this is the *only* analytic input of the
identity, and it is available `sorry`-free as `FstarDzIter_chain_open`. -/

/-- **The moment tower** (difference form).  For `0 < s ≤ z` and `j + 1 ≤ k`,
`B_j(z) - B_j(s) = ∫_s^z B_{j+1}(r)/r dr`. -/
theorem radIter_bmom_chain (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) {s z : ℝ} (hs : 0 < s)
    (hsz : s ≤ z) :
    Bmom F j z - Bmom F j s = ∫ r in s..z, Bmom F (j + 1) r / r := by
  simpa only [Bmom_eq_Fstar_DzIter] using
    GbarSin.FstarDzIter_chain_open α k F hF hmem j hj hs hsz

/-- **The moment tower** (anchored form): for `0 < a < b` and `j + 1 ≤ k`,
`B_j(b) = B_j(a) + ∫_a^b B_{j+1}(s)/s ds`. -/
theorem radIter_bmom_relation (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) :
    Bmom F j b = Bmom F j a + ∫ s in a..b, Bmom F (j + 1) s / s := by
  have h := radIter_bmom_chain α k hF hmem j hj ha hab.le
  linarith

/-- **The moment tower anchored at `c`**: for every `y > 0`,
`B_j(y) = B_j(c) + ∫_c^y B_{j+1}(s)/s ds`. -/
theorem radIter_bmom_eq_const_add_integral (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∀ y : ℝ, 0 < y → Bmom F j y = Bmom F j c + ∫ s in c..y, Bmom F (j + 1) s / s := by
  intro y hy
  rcases lt_trichotomy y c with hlt | heq | hgt
  · have hrel := radIter_bmom_relation α k hF hmem j hj hy hlt
    rw [hrel, intervalIntegral.integral_symm]
    ring
  · subst heq
    simp
  · exact radIter_bmom_relation α k hF hmem j hj hc hgt

/-! ## Continuity of the moments -/

/-- The `j`-th moment is continuous on `(0,∞)`, for `j + 1 ≤ k`. -/
theorem radIter_bmom_continuousOn (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) :
    ContinuousOn (fun z => Bmom F j z) (Set.Ioi 0) := by
  intro z hz
  have hz0 : 0 < z := hz
  set a : ℝ := z / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have haz : a < z := by rw [ha_def]; linarith
  have hb : a < z + a := by linarith
  have hg : IntegrableOn (fun s => Bmom F (j + 1) s / s) (Set.uIcc a (z + a)) := by
    rw [Set.uIcc_of_le hb.le]
    exact integrableOn_Bmom_div α k hF hmem (j + 1) (by omega) a (z + a) ha0 hb
  have hΦ : ContinuousOn (fun x : ℝ => ∫ s in a..x, Bmom F (j + 1) s / s)
      (Set.uIcc a (z + a)) :=
    intervalIntegral.continuousOn_primitive_interval hg
  have hU : Set.uIcc a (z + a) ∈ 𝓝 z := by
    rw [Set.uIcc_of_le hb.le]
    exact Icc_mem_nhds haz (by linarith)
  have hcontΦ : ContinuousWithinAt (fun x : ℝ => ∫ s in a..x, Bmom F (j + 1) s / s)
      (Set.Ioi 0) z :=
    (hΦ.continuousAt hU).continuousWithinAt
  have hev : (fun x : ℝ => Bmom F j x) =ᶠ[𝓝[Set.Ioi 0] z]
      (fun x : ℝ => Bmom F j a + ∫ s in a..x, Bmom F (j + 1) s / s) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact radIter_bmom_eq_const_add_integral α k hF hmem j hj ha0 x hx
  have hz_e : Bmom F j z = Bmom F j a + ∫ s in a..z, Bmom F (j + 1) s / s :=
    radIter_bmom_eq_const_add_integral α k hF hmem j hj ha0 z hz0
  exact (continuousWithinAt_const.add hcontΦ).congr_of_eventuallyEq hev hz_e

/-! ## Differentiability of the moments -/

/-- **The `j`-th moment is differentiable everywhere on `(0,∞)`** with derivative
`B_{j+1}(z)/z`, as soon as `j + 2 ≤ k` (so that `B_{j+1}` — and hence `B_{j+1}(s)/s` — is
continuous, which makes the fundamental theorem of calculus available). -/
theorem radIter_bmom_hasDerivAt (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 2 ≤ k) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z => Bmom F j z) (Bmom F (j + 1) z / z) z := by
  have hz0 : 0 < z := hz
  set a : ℝ := z / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have haz : a < z := by rw [ha_def]; linarith
  have hcontOn : ContinuousOn (fun s : ℝ => Bmom F (j + 1) s / s) (Set.Ioi 0) :=
    (radIter_bmom_continuousOn α k hF hmem (j + 1) (by omega)).div continuousOn_id
      (fun s hs => (show (0 : ℝ) < s from hs).ne')
  have hcont : ContinuousAt (fun s : ℝ => Bmom F (j + 1) s / s) z :=
    hcontOn.continuousAt (isOpen_Ioi.mem_nhds hz0)
  have hInt : IntervalIntegrable (fun s : ℝ => Bmom F (j + 1) s / s) volume a z := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le haz.le]
    exact integrableOn_Bmom_div α k hF hmem (j + 1) (by omega) a z ha0 haz
  have hder := intervalIntegral.integral_hasDerivAt_right hInt
    (hcontOn.stronglyMeasurableAtFilter isOpen_Ioi z hz0) hcont
  have hev : (fun x : ℝ => Bmom F j x) =ᶠ[𝓝 z]
      (fun x : ℝ => Bmom F j a + ∫ s in a..x, Bmom F (j + 1) s / s) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz0] with x hx
    exact radIter_bmom_eq_const_add_integral α k hF hmem j (by omega) ha0 x hx
  exact hev.hasDerivAt_iff.mpr (hder.const_add (Bmom F j a))

/-- **A.e. differentiability of the top moment.**  For `k ≥ 1`, for almost every `z > 0` the
moment `B_{k-1}` is differentiable at `z` with derivative `B_k(z)/z`.  Only `k ≤ k` is
available for the tower, so this is the Lebesgue differentiation theorem
(`IntervalIntegrable.ae_hasDerivAt_integral`) applied on the countable family of intervals
`[1/(n+1), n+2]` covering `(0,∞)`. -/
theorem radIter_bmom_ae_hasDerivAt (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (hk : 1 ≤ k) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      HasDerivAt (fun z => Bmom F (k - 1) z) (Bmom F k z / z) z := by
  set P : ℝ → Prop := fun x => HasDerivAt (fun x => Bmom F (k - 1) x) (Bmom F k x / x) x
    with hP
  have key : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2))),
      P x := by
    intro n
    set a : ℝ := 1 / ((n : ℝ) + 1) with hadef
    set b : ℝ := (n : ℝ) + 2 with hbdef
    have hpos : 0 < a := by rw [hadef]; positivity
    have hlt : a < b := by
      have hbpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [hadef, hbdef, div_lt_iff₀ hbpos]
      nlinarith
    have hle : a ≤ b := hlt.le
    have hInt : IntervalIntegrable (fun s : ℝ => Bmom F k s / s) volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
      exact integrableOn_Bmom_div α k hF hmem k le_rfl a b hpos hlt
    have hldt := IntervalIntegrable.ae_hasDerivAt_integral hInt
    rw [Set.uIcc_of_le hle] at hldt
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hldt] with x hx
    intro hxmem
    have hxpos : 0 < x := lt_of_lt_of_le hpos hxmem.1
    have hder : HasDerivAt (fun y => ∫ t in a..y, Bmom F k t / t) (Bmom F k x / x) x :=
      hx hxmem a ⟨le_rfl, hle⟩
    have hev : (fun y => Bmom F (k - 1) y) =ᶠ[𝓝 x]
        (fun y => Bmom F (k - 1) a + ∫ t in a..y, Bmom F k t / t) := by
      filter_upwards [isOpen_Ioi.mem_nhds hxpos] with y hy
      have h := radIter_bmom_eq_const_add_integral α k hF hmem (k - 1) (by omega) hpos y hy
      rw [show (k - 1) + 1 = k from by omega] at h
      exact h
    exact hev.hasDerivAt_iff.mpr (hder.const_add _)
  have keynull : ∀ n : ℕ, volume {x | x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2)
      ∧ ¬ P x} = 0 := by
    intro n
    have h := key n
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff] at h
    have hset : {x | x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) ∧ ¬ P x}
        = {x | ¬ (x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) → P x)} := by
      ext x
      simp only [Set.mem_setOf_eq, not_imp]
    rw [hset]
    exact h
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null keynull)
  intro x hx
  have hx' : x ∈ Set.Ioi 0 ∧ ¬ P x := by
    simpa only [Set.mem_setOf_eq, not_imp] using hx
  obtain ⟨hx0, hxn⟩ := hx'
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ,
      1 / ((n : ℝ) + 1) ≤ x ∧ x ≤ (n : ℝ) + 2 := by
    obtain ⟨n, hn⟩ := exists_nat_ge (max x (1 / x))
    refine ⟨n, ?_, ?_⟩
    · have hx1 : 1 / x ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
      have : 1 ≤ x * (n : ℝ) := by
        rw [div_le_iff₀ hx0] at hx1
        linarith
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith
    · have hxn' : x ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
      linarith
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  show x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) ∧ ¬ P x
  exact ⟨⟨hn1, hn2⟩, hxn⟩

/-! ## The identity `(D_z^j F_*)(z) = B_j(z)` -/

/-- **The `D_z`-iterates of the angular moment are the moments** (everywhere on `(0,∞)`,
for all `j` with `j + 1 ≤ k`). -/
theorem radIter_bmom_eq_all (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) :
    ∀ j : ℕ, j + 1 ≤ k → ∀ z : ℝ, 0 < z →
      radIter (fun z => Bmom F 0 z) j z = Bmom F j z := by
  intro j
  induction j with
  | zero => intro _ z _; rfl
  | succ n ih =>
      intro hj z hz
      rw [radIter_succ]
      have hev : (radIter (fun z => Bmom F 0 z) n) =ᶠ[𝓝 z] (fun z => Bmom F n z) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih (by omega) z' hz'
      rw [hev.deriv_eq, (radIter_bmom_hasDerivAt α k hF hmem n (by omega) hz).deriv]
      rw [mul_div_assoc', mul_div_cancel_left₀ _ hz.ne']

/-- **The top `D_z`-iterate**, almost everywhere: for `k ≥ 1` and almost every `z > 0`,
`radIter (B_0) k z = B_k z`. -/
theorem radIter_bmom_ae_top (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (hk : 1 ≤ k) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      radIter (fun z => Bmom F 0 z) k z = Bmom F k z := by
  have h1 := radIter_bmom_ae_hasDerivAt α k hF hmem hk
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at h1
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [h1] with z hzimp
  intro hzmem
  have hz0 : 0 < z := hzmem
  have hk_eq : k = (k - 1) + 1 := by omega
  conv_lhs => rw [hk_eq]
  rw [radIter_succ]
  have hev : (radIter (fun z => Bmom F 0 z) (k - 1)) =ᶠ[𝓝 z]
      (fun z => Bmom F (k - 1) z) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz0] with z' hz'
    exact radIter_bmom_eq_all α k hF hmem (k - 1) (by omega) z' hz'
  rw [hev.deriv_eq, (hzimp hzmem).deriv]
  rw [mul_div_assoc', mul_div_cancel_left₀ _ hz0.ne']

/-! ## The target -/

/-- **The `D_z`-iterates of the angular moment are the radial moments, a.e.**  For a source
`F` which is `C^∞` on the open quadrant and honestly in `ℋ^k`, for almost every `z > 0` and
every `j ≤ k`,

  `radIter (Bmom F 0) j z = Bmom F j z`.

This is the separation identity used by `Cert.HkMem_Fstar_sin`: it identifies the radial
coefficients of `D_z^j (F_*(F)·sin 2θ)` — hence the `ℋ^k`-integrand of `F_*(F)·sin 2θ`
(`Cert.HkIntegrand_radial_sin`) — with the moments `F_*(D_z^j F)` of the source. -/
theorem radIter_Bmom_ae (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∀ j : ℕ, j ≤ k →
        Work.FTS.EllipticEst.radIter (fun z => Work.FTS.EllipticEst.Bmom F 0 z) j z
          = Work.FTS.EllipticEst.Bmom F j z := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk]
    filter_upwards with z
    intro j hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    rw [hj0]
    rfl
  · have htop := radIter_bmom_ae_top α k hF hmem hk
    filter_upwards [htop, self_mem_ae_restrict measurableSet_Ioi] with z htopz hz
    intro j hj
    rcases lt_or_eq_of_le hj with hlt | heq
    · exact radIter_bmom_eq_all α k hF hmem j (by omega) z hz
    · subst heq
      exact htopz

end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.lobAux.HkSqDzTransfer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.lobAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

open Work.FTS.EllipticEst

/-! ## Homogeneity of `HkSq` in the amplitude (with no `HkMem` hypothesis) -/


/-! ## Smoothness of the pieces on the open quadrant -/


/-! ## The elliptic law solved for `D_z Ψ` -/


/-! ## Locality and linearity of the iterated operators on the open quadrant

The `SmoothOpen`-closed iterated `D`-operators are linear on `Q0`; `SmoothOpenAdd` provides
the additive form, the subtractive form is redone here in the same style. -/

/-- Two functions agreeing on the open quadrant have the same iterated `D_θ`-derivatives
there.  (Locality of `D_θ`; no smoothness is needed.) -/
theorem DthIter_congr_open {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i F z θ = Work.Spaces.DthIter i G z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun θ' => Work.Spaces.DthIter n F z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n G z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (Real.pi / 2) from ⟨h1, h2⟩)]
          with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq]

/-- Two functions agreeing on the open quadrant have the same mixed derivatives there. -/
theorem mixed_congr_open {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) (j i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i F z θ = Work.Spaces.mixed j i G z θ :=
  SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i F) (G := Work.Spaces.DthIter i G)
    (DthIter_congr_open h i) j

/-- The iterated `D_z`-operator is additive for `-` on the open quadrant for `SmoothOpen`
data.  (The subtraction counterpart of `SmoothOpen.DzIter_add`.) -/
theorem DzIter_sub_open {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) (j : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter j (fun z θ => f z θ - g z θ) z θ
        = Work.Spaces.DzIter j f z θ - Work.Spaces.DzIter j g z θ := by
  induction j with
  | zero => intro z θ hz h1 h2; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => f z θ - g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n f z' θ - Work.Spaces.DzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n f z' θ) z :=
        ((hf.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n g z' θ) z :=
        ((hg.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd : deriv (fun z' => Work.Spaces.DzIter n f z' θ - Work.Spaces.DzIter n g z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n f z' θ) z
            - deriv (fun z' => Work.Spaces.DzIter n g z' θ) z := deriv_sub hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- The iterated `D_θ`-operator is additive for `-` on the open quadrant for `SmoothOpen`
data. -/
theorem DthIter_sub_open {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i (fun z θ => f z θ - g z θ) z θ
        = Work.Spaces.DthIter i f z θ - Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨h1, h2⟩
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => f z θ - g z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n f z θ' - Work.Spaces.DthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n f z θ') θ :=
        (((hf.DthIter n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n g z θ') θ :=
        (((hg.DthIter n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd : deriv (fun θ' => Work.Spaces.DthIter n f z θ' - Work.Spaces.DthIter n g z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n f z θ') θ
            - deriv (fun θ' => Work.Spaces.DthIter n g z θ') θ := deriv_sub hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

/-- The mixed operators `D_z^j D_θ^i` are additive for `-` on the open quadrant for
`SmoothOpen` data. -/
theorem mixed_sub_open {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) (j i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i (fun z θ => f z θ - g z θ) z θ
        = Work.Spaces.mixed j i f z θ - Work.Spaces.mixed j i g z θ := by
  intro z θ hz h1 h2
  have hcongr := SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i (fun z θ => f z θ - g z θ))
    (G := fun z θ => Work.Spaces.DthIter i f z θ - Work.Spaces.DthIter i g z θ)
    (fun z θ hz h1 h2 => DthIter_sub_open hf hg i z θ hz h1 h2) j z θ hz h1 h2
  have hadd := DzIter_sub_open (hf.DthIter i) (hg.DthIter i) j z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

/-! ## Congruence of the `ℋ^k`-integrand on the open quadrant -/


/-! ## Vanishing of the `ℋ^k`-integrand on the boundary of the quadrant -/

theorem DthIter_succ_eq_zero_of_sin (f : ℝ → ℝ → ℝ) {θ : ℝ} (hs : Real.sin (2 * θ) = 0)
    (m : ℕ) (z : ℝ) : Work.Spaces.DthIter (m + 1) f z θ = 0 := by
  simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth, hs, zero_mul]

theorem DzIter_eq_zero_of_slice (f : ℝ → ℝ → ℝ) {θ : ℝ} (h : ∀ z, f z θ = 0) :
    ∀ (j : ℕ) (z : ℝ), Work.Spaces.DzIter j f z θ = 0 := by
  intro j
  induction j with
  | zero => intro z; exact h z
  | succ n ih =>
      intro z
      have hslice : (fun z' => Work.Spaces.DzIter n f z' θ) = fun _ => (0 : ℝ) := funext ih
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [hslice]
      simp

theorem mixed_eq_zero_of_sin (f : ℝ → ℝ → ℝ) {θ : ℝ} (hs : Real.sin (2 * θ) = 0)
    {j i : ℕ} (hi : 1 ≤ i) (z : ℝ) : Work.Spaces.mixed j i f z θ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  simp only [Work.Spaces.mixed]
  exact DzIter_eq_zero_of_slice (Work.Spaces.DthIter (m + 1) f) (θ := θ)
    (fun z' => DthIter_succ_eq_zero_of_sin f hs m z') j z

/-- The `ℋ^k`-integrand vanishes on the angular boundary `sin(2θ) = 0`: the first sum is
killed by the `1/sin(2θ)^{η/2}` factor and the second by the `D_θ`-factors of all its
summands (all of them carry `i ≥ 1`). -/
theorem HkIntegrand_eq_zero_of_sin (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsin, div_zero, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · rw [mixed_eq_zero_of_sin f hs hc.1 z, zero_mul, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-- The `ℋ^k`-integrand vanishes on the radial boundary `z = 0` (where `w 0 = 0`). -/
theorem HkIntegrand_eq_zero_of_z_eq_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp [Work.Spaces.w, Work.Spaces.Wt, Work.Spaces.wTheta]

/-! ## The pointwise three-term Cauchy–Schwarz bound for the `ℋ^k`-integrand -/





/-! ## The pointwise transfer on the open quadrant -/



/-! ## From a pointwise integrand bound to the `HkSq` bound -/


/-- The constant multiple of the three-term integral. -/
theorem integral_mul_add3 (c : ℝ) (f g h : ℝ → ℝ) (μ : Measure ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (hh : Integrable h μ) :
    ∫ x, c * (f x + g x + h x) ∂μ = c * ((∫ x, f x ∂μ) + (∫ x, g x ∂μ) + ∫ x, h x ∂μ) := by
  have e1 : (∫ x, c * (f x + g x + h x) ∂μ) = ∫ x, c * ((f x + g x) + h x) ∂μ := rfl
  have e2 : (∫ x, c * ((f x + g x) + h x) ∂μ) = ∫ x, c * ((f + g) x + h x) ∂μ := rfl
  have e3 : (∫ x, (f + g) x ∂μ) = ∫ x, (f x + g x) ∂μ := rfl
  rw [e1, e2, integral_const_mul, integral_add (hf.add hg) hh, e3, integral_add hf hg]

/-- **Integration of a pointwise bound of `ℋ^k`-integrands.**  If the integrand of `U` is
pointwise dominated by `3(R₁ + R₂ + α⁴R₃)` on the closed quadrant and the three dominating
integrands are honest (`HkMem`), then the same bound holds for the iterated integrals.  This
is the two-step monotonicity argument of `Work.FTS.LocData.HkSq_add_le`; the integrability of
the dominating function — the role of the three `HkMem` hypotheses — is what makes it work in
the presence of the junk value `0` attached to a non-integrable integrand. -/
theorem HkSq_le_of_integrand_le (α : ℝ) (k : ℕ) {U R1 R2 R3 : ℝ → ℝ → ℝ}
    (h1 : Work.Spaces.HkMem α k R1) (h2 : Work.Spaces.HkMem α k R2)
    (h3 : Work.Spaces.HkMem α k R3)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k U z θ
        ≤ 3 * (Work.Spaces.HkIntegrand α k R1 z θ + Work.Spaces.HkIntegrand α k R2 z θ
            + α ^ 4 * Work.Spaces.HkIntegrand α k R3 z θ)) :
    Work.Spaces.HkSq α k U
      ≤ 3 * (Work.Spaces.HkSq α k R1 + Work.Spaces.HkSq α k R2
          + α ^ 4 * Work.Spaces.HkSq α k R3) := by
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k U z θ)
        ≤ 3 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R1 z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R2 z θ)
            + α ^ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R3 z θ)) := by
    intro z hz
    have hf : Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α k R1 z θ)
        (volume.restrict Work.Spaces.Iθ) := h1.1 z hz
    have hg : Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α k R2 z θ)
        (volume.restrict Work.Spaces.Iθ) := h2.1 z hz
    have hh : Integrable (fun θ : ℝ => α ^ 4 * Work.Spaces.HkIntegrand α k R3 z θ)
        (volume.restrict Work.Spaces.Iθ) := (h3.1 z hz).const_mul (α ^ 4)
    have hint : Integrable (fun θ : ℝ => 3 * (Work.Spaces.HkIntegrand α k R1 z θ
        + Work.Spaces.HkIntegrand α k R2 z θ
        + α ^ 4 * Work.Spaces.HkIntegrand α k R3 z θ))
        (volume.restrict Work.Spaces.Iθ) := ((hf.add hg).add hh).const_mul 3
    have hle := integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k U z θ) hint
      (ae_restrict_of_forall_mem hmesθ fun θ hθ => hpt z hz θ hθ)
    refine hle.trans_eq ?_
    rw [integral_mul_add3 (μ := volume.restrict Work.Spaces.Iθ) 3
      (fun θ : ℝ => Work.Spaces.HkIntegrand α k R1 z θ)
      (fun θ : ℝ => Work.Spaces.HkIntegrand α k R2 z θ)
      (fun θ : ℝ => α ^ 4 * Work.Spaces.HkIntegrand α k R3 z θ) hf hg hh,
      integral_const_mul]
  have hX1 : Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R1 z θ)
      (volume.restrict Work.Spaces.Iz) := h1.2
  have hX2 : Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R2 z θ)
      (volume.restrict Work.Spaces.Iz) := h2.2
  have hX3 : Integrable
      (fun z : ℝ => α ^ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R3 z θ))
      (volume.restrict Work.Spaces.Iz) := h3.2.const_mul (α ^ 4)
  have houter : (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k U z θ)
      ≤ ∫ z in Work.Spaces.Iz, 3 *
          ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R1 z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R2 z θ)
            + α ^ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R3 z θ)) := by
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k U z θ)
      (((hX1.add hX2).add hX3).const_mul 3) ?_
    exact ae_restrict_of_forall_mem hmesz fun z hz => hinner z hz
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine houter.trans_eq ?_
  rw [integral_mul_add3 (μ := volume.restrict Work.Spaces.Iz) 3
    (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R1 z θ)
    (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R2 z θ)
    (fun z : ℝ => α ^ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R3 z θ))
    hX1 hX2 hX3,
    integral_const_mul]

/-! ## The transfer theorem -/


end Work.FTS.EllipticEst.lobAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary definitions and pointwise bookkeeping for `EllEstUnif_step`

The induction step of Elgindi's Proposition `prop:Hk` is split here into

* the **exact recursion** of the two halves of `HkIntegrand` in the index `k`
  (`Zsum_succ`, `Msum_succ`): at level `k` the integrand is its level-`(k-1)` value, plus the
  *top diagonal* `i + j = k` of the mixed slots, plus the top radial slot;
* the **coarse pointwise comparison** `HkIntegrand_step_le` against the *shifted* integrand
  `HkIntegrand α (k-1) (D_z f)` — every slot of the top diagonal except the angular one
  `(mixed 0 k f · Wt)²` is a slot of the shifted integrand, and each single slot is dominated by
  the whole integrand (`Work.Spaces.sq_le_HkIntegrand_z`, `..._mixed`);
* the **reverse comparison** `HkIntegrand_shift_le`, expressing that shifting by `D_z` only
  removes slots.

Consequently the level-`k` norm is at most the level-`(k-1)` norm of `f`, the level-`(k-1)` norm
of `D_z f` and the single *top angular slot* `Tk α k f` — and it is precisely that last slot which
is the content of the paper's §"General ℋ^k case".
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

namespace Step

/-- The open quadrant, the domain on which the smoothness of the weak class is assumed. -/
def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

/-! ## The two halves of `HkIntegrand` and their recursion in `k` -/

/-- The weight `w(z)/sin(2θ)^{η/2}` of the pure `D_z`-slots of `HkIntegrand`. -/
def Zu (z θ : ℝ) : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)

/-- The pure radial part `∑_{i ≤ k} (D_z^i f · Zu)²` of `HkIntegrand α k f`. -/
def Zsum (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ * Zu z θ) ^ 2

/-- The mixed part `∑_{1 ≤ i, i+j ≤ k} (D_z^j D_θ^i f · Wt)²` of `HkIntegrand α k f`. -/
def Msum (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
    (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)

/-- **The top angular slot at level `k`**: the single term of `HkIntegrand α k f` that involves
`k` angular derivatives and no radial derivative.  This is the quantity the paper's
§"General `ℋ^k` case" has to estimate. -/
def Tk (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The top angular slot is nonnegative. -/
theorem Tk_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ Tk α k f :=
  integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _

/-- `HkIntegrand` is the sum of its radial and its mixed half. -/
theorem HkIntegrand_eq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ = Zsum k f z θ + Msum α k f z θ := rfl

/-- **The pure radial part recurses in `k`** by adding the top slot `i = k`. -/
theorem Zsum_succ {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Zsum k f z θ = Zsum (k - 1) f z θ
      + (Work.Spaces.DzIter k f z θ * Zu z θ) ^ 2 := by
  have hk1 : k - 1 + 1 = k := by omega
  unfold Zsum
  rw [Finset.sum_range_succ]
  have hcongr : (∑ i ∈ Finset.range k,
        (Work.Spaces.DzIter i f z θ * Zu z θ) ^ 2)
      = ∑ i ∈ Finset.range (k - 1 + 1),
        (Work.Spaces.DzIter i f z θ * Zu z θ) ^ 2 :=
    Finset.sum_congr (by rw [hk1]) (fun _ _ => rfl)
  rw [hcongr]

/-- **The mixed part as a sum of rows**: the inner `j`-sum may be truncated at `k - i`
(the skipped slots carry the value `0`). -/
theorem Msum_eq_rows (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Msum α k f z θ = ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1 - i),
        (if 1 ≤ i then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
  unfold Msum
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hsub : Finset.range (k + 1 - i) ⊆ Finset.range (k + 1) := by
    intro x hx
    exact Finset.mem_range.mpr (by have h := Finset.mem_range.mp hx; omega)
  have hzero : ∀ x ∈ Finset.range (k + 1), x ∉ Finset.range (k + 1 - i) →
      (if 1 ≤ i ∧ i + x ≤ k then
        (Work.Spaces.mixed x i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) = 0 := by
    intro x _ hx'
    have hxk : ¬ (x < k + 1 - i) := fun h => hx' (Finset.mem_range.mpr h)
    rw [if_neg]
    intro hcon
    exact hxk (by omega)
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjlt : j < k + 1 - i := Finset.mem_range.mp hj
  have hijk : i + j ≤ k := by omega
  by_cases hi' : 1 ≤ i
  · rw [if_pos ⟨hi', hijk⟩, if_pos hi']
  · rw [if_neg (fun h => hi' h.1), if_neg hi']

/-- **The mixed part recurses in `k`**: the `k - 1` mixed part, plus the top slot
`(i, j) = (k, 0)`, plus the diagonal `i + j = k` with `j ≥ 1`. -/
theorem Msum_succ {k : ℕ} (hk : 1 ≤ k) (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Msum α k f z θ = Msum α (k - 1) f z θ
      + (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2
      + ∑ i ∈ Finset.range k,
          (if 1 ≤ i then (Work.Spaces.mixed (k - i) i f z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0) := by
  rw [Msum_eq_rows, Finset.sum_range_succ]
  have hkrow : (∑ j ∈ Finset.range (k + 1 - k),
        (if 1 ≤ k then (Work.Spaces.mixed j k f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      = (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    have h1 : k + 1 - k = 1 := by omega
    rw [h1, Finset.sum_range_one, if_pos hk]
  have hrows : ∀ i ∈ Finset.range k,
      (∑ j ∈ Finset.range (k + 1 - i),
        (if 1 ≤ i then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      = (∑ j ∈ Finset.range (k - 1 + 1 - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        + (if 1 ≤ i then (Work.Spaces.mixed (k - i) i f z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0) := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have h1 : k + 1 - i = (k - i) + 1 := by omega
    have h2 : k - 1 + 1 - i = k - i := by
      rw [show k - 1 + 1 = k from by omega]
    rw [h1, h2, Finset.sum_range_succ]
  rw [Finset.sum_congr rfl hrows, Finset.sum_add_distrib, hkrow]
  have hfirst : (∑ i ∈ Finset.range k,
        (∑ j ∈ Finset.range (k - 1 + 1 - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)))
      = Msum α (k - 1) f z θ := by
    rw [Msum_eq_rows]
    exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
      (fun i _ => rfl)
  rw [hfirst]
  ring

/-! ## Iterated `D_z`, congruence on an open set, and the diagonal slots -/

/-- `D_z^n (D_z g) = D_z^{n+1} g`. -/
theorem DzIter_Dz (n : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter n (Work.Spaces.Dz g) = Work.Spaces.DzIter (n + 1) g := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [Work.Spaces.DzIter_succ (n := m) (f := Work.Spaces.Dz g), ih]
      rfl

/-- `D_z^k f = D_z^{k-1}(D_z f)`. -/
theorem DzIter_eq_DzIter_Dz {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter k f = Work.Spaces.DzIter (k - 1) (Work.Spaces.Dz f) := by
  have h := DzIter_Dz (k - 1) f
  have h1 : k - 1 + 1 = k := by omega
  rw [h1] at h
  exact h.symm

/-- Functions that agree on an open set have the same iterated `D_z` there. -/
theorem DzIter_congr_of_isOpen {g g' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j g))
      (Function.uncurry (Work.Spaces.DzIter j g')) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
      intro y hy
      show y.1 * Work.Spaces.pz (Work.Spaces.DzIter j g) y.1 y.2
        = y.1 * Work.Spaces.pz (Work.Spaces.DzIter j g') y.1 y.2
      rw [Work.Spaces.pz_congr_of_isOpen hV ih hy]


/-! ## The coarse pointwise comparisons -/






end Step

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The two ingredients of the argument

The proof of the target is a two-line consequence of the two lemmas below.

* `integrableOn_pz_mul_sinCos2` extracts the `i = 1` slot of `HkMem` for `∂_z g` and absorbs the
  angular profile `sinθcos²θ` into the weighted `L²`-integrand of `ℋ^k`.  It is the same
  "absorbtion" mechanism as `Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted` (the pointwise
  bound `|a·sinθcos²θ| ≤ (a·W)² + 1`, `W = w/sin(2θ)^{η/2}`) combined with
  `Work.Spaces.sq_le_HkIntegrand_z` for the `i = 1` summand and the identity
  `D_z g = z · ∂_z g`, which removes the factor `z²` (the only place where `z > 0` enters).

* `aesm_slice_mul_sinCos2`, `aesm_slice_pz_F`, `aesm_slice_pz_zsq_pzIter2` supply the a.e. strong
  measurability that `Integrable.mono'` needs: the slices are continuous on the open quadrant,
  and for `F` (which is only known to equal the smooth `bslOp α Ψ` there) the identification is
  transported by the locality of `deriv` on the open interval. -/



/-- **Honesty of the slice `θ ↦ ∂_z g (z,θ) · sinθcos²θ` from one `H^k`-slot.**

If `g ∈ ℋ^k` with `1 ≤ k` and the slice is a.e. strongly measurable, then it is integrable on
`Iθ` for every `z > 0`.

The pointwise bound is the paper's "absorbtion" estimate
`|a·sinθcos²θ| ≤ (a·W)² + 1` with `W = w z/sin(2θ)^{η/2}` (`abs_mul_sinCos2_le_weighted`),
followed by `(∂_z g · W)² = z^{-2}·(D_z g · W)² ≤ z^{-2}·HkIntegrand α k g z ·`
(`Work.Spaces.sq_le_HkIntegrand_z` for `i = 1`), which is integrable on the slice by `HkMem`. -/
theorem integrableOn_pz_mul_sinCos2 {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k g) (hk : 1 ≤ k) {z : ℝ} (hz : 0 < z)
    (haesm : AEStronglyMeasurable
      (fun θ => Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hz2ne : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
  have hvol : (volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  refine MeasureTheory.Integrable.mono'
    (((hmem.1 z hzI).const_mul ((z ^ 2)⁻¹)).add
      (MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol)) haesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
  rw [Real.norm_eq_abs]
  -- the pointwise absorbtion estimate
  have h1 := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
    (f := fun θ => Work.Spaces.pz g z θ) hz hθ
  -- and the `i = 1` slot of the `ℋ^k`-integrand
  have hq := Work.Spaces.sq_le_HkIntegrand_z α k g z θ 1 hk
  set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hW
  have hDz : Work.Spaces.DzIter 1 g z θ = z * Work.Spaces.pz g z θ := rfl
  have hid : (Work.Spaces.pz g z θ * W) ^ 2
      = (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ * W) ^ 2) := by
    rw [hDz]
    have : (z * Work.Spaces.pz g z θ * W) ^ 2
        = z ^ 2 * (Work.Spaces.pz g z θ * W) ^ 2 := by ring
    rw [this, inv_mul_cancel_left₀ hz2ne]
  have hz2inv : (0 : ℝ) ≤ (z ^ 2)⁻¹ := by positivity
  calc |Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ|
      ≤ (Work.Spaces.pz g z θ * W) ^ 2 + 1 := h1
    _ = (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ * W) ^ 2) + 1 := by rw [hid]
    _ ≤ (z ^ 2)⁻¹ * Work.Spaces.HkIntegrand α k g z θ + 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hq hz2inv) le_rfl




end

end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary `rpow` algebra for the two weight factors -/

/-- `(s^{-e/2})² = s^{-e}` for `s ≥ 0`. -/
private lemma rpow_neg_half_sq (s e : ℝ) (hs : 0 ≤ s) : (s ^ (-(e / 2))) ^ 2 = s ^ (-e) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
  congr 1
  ring

/-- Squaring a weighted derivative: if `|x·w| ≤ A` and `s ≥ 0` then
`(x·(w·s^{-e/2}))² ≤ A²·s^{-e}`.  This is the step `w/sin(2θ)^{γ/2} = w·sin(2θ)^{-γ/2}`. -/
private lemma sq_mul_rpow_neg_le {x w s A e : ℝ} (hs : 0 ≤ s) (hx : |x * w| ≤ A) :
    (x * (w * s ^ (-(e / 2)))) ^ 2 ≤ A ^ 2 * s ^ (-e) := by
  have h1 : (x * (w * s ^ (-(e / 2)))) ^ 2 = (x * w) ^ 2 * (s ^ (-(e / 2))) ^ 2 := by ring
  rw [h1, rpow_neg_half_sq s e hs]
  exact mul_le_mul_of_nonneg_right
    (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x * w)) hx 2)
    (Real.rpow_nonneg hs _)

theorem HkIntegrand_zfar_Fstar_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (L : ℝ), 1 ≤ L →
      ∀ (z : ℝ), z ∈ Work.Spaces.Iz → ∀ (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ C * α ^ 2 * angMaj α θ / (1 + z) ^ 2 := by
  obtain ⟨Kc, hKc1, hKc⟩ := ZFBase.DzIter_oneSubChi_bound_uniform
  refine ⟨20 * (64 * Kc) ^ 2 + 100 * (6400000 * Kc) ^ 2, by positivity, ?_⟩
  intro α hα hα1 L hL z hzI θ hθ
  have hz0 : 0 ≤ z := hzI
  have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hs0 : 0 ≤ Real.sin (2 * θ) := ZFBase.sin_two_nonneg_Iθ hθ
  have hang0 : 0 ≤ angMaj α θ := angMaj_nonneg hθ
  by_cases hz1 : 1 ≤ z
  · -- #### the main case `z ≥ 1`
    have hzpos : 0 < z := by linarith
    have hden : 0 < (1 + z) ^ 2 := by positivity
    have hsη : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs0 _
    have hsgam : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs0 _
    -- the two pointwise weighted bounds
    have hDzb : ∀ i' : ℕ, i' ≤ 4 →
        |Work.Spaces.DzIter i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
          * Work.Spaces.w z| ≤ 64 * Kc * α * Work.Spaces.Gam α θ / z :=
      fun i' hi' => ZfarDzIterBound hKc hKc1 α hα hα1 L hL z hz1 θ hθ i' hi'
    have hMxb : ∀ i' j' : ℕ, 1 ≤ i' → i' + j' ≤ 4 →
        |Work.Spaces.mixed j' i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
          * Work.Spaces.w z| ≤ 6400000 * Kc * α * Work.Spaces.Gam α θ / z :=
      fun i' j' hi' hij' =>
        ZfarMixedBound hKc hKc1 α hα hα1 L hL z hz1 θ hθ i' hi' j' hij'
    -- the `D_z`-terms
    have hterm1 : ∀ i' ∈ Finset.range 5,
        (Work.Spaces.DzIter i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (64 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / z ^ 2 := by
      intro i' hi'
      have hi'4 : i' ≤ 4 := by rw [Finset.mem_range] at hi'; omega
      have hb := hDzb i' hi'4
      have hw : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hs0]
      rw [hw]
      refine le_trans (sq_mul_rpow_neg_le hs0 hb) (le_of_eq ?_)
      ring
    -- the mixed terms
    have hterm2 : ∀ i' ∈ Finset.range 5, ∀ j' ∈ Finset.range 5,
        (if 1 ≤ i' ∧ i' + j' ≤ 4 then
          (Work.Spaces.mixed j' i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ (6400000 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) / z ^ 2 := by
      intro i' hi' j' hj'
      by_cases hc : 1 ≤ i' ∧ i' + j' ≤ 4
      · rw [if_pos hc]
        have hb := hMxb i' j' hc.1 hc.2
        have hWt : Work.Spaces.Wt α z θ
            = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
          rw [Work.Spaces.Wt, Work.Spaces.wTheta]
        rw [hWt]
        refine le_trans (sq_mul_rpow_neg_le hs0 hb) (le_of_eq ?_)
        ring
      · rw [if_neg hc]
        exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg (6400000 * Kc))
          (sq_nonneg α)) (sq_nonneg (Work.Spaces.Gam α θ))) hsgam) (le_of_lt (by positivity))
    -- the two sums
    have hsum1 : (∑ i' ∈ Finset.range 5,
        (Work.Spaces.DzIter i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 5 * ((64 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / z ^ 2) := by
      calc (∑ i' ∈ Finset.range 5,
          (Work.Spaces.DzIter i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i' ∈ Finset.range 5, ((64 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / z ^ 2) := Finset.sum_le_sum hterm1
        _ = 5 * ((64 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / z ^ 2) := by
            simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsum2 : (∑ i' ∈ Finset.range 5, ∑ j' ∈ Finset.range 5,
        (if 1 ≤ i' ∧ i' + j' ≤ 4 then
          (Work.Spaces.mixed j' i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ 25 * ((6400000 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) / z ^ 2) := by
      calc (∑ i' ∈ Finset.range 5, ∑ j' ∈ Finset.range 5,
          (if 1 ≤ i' ∧ i' + j' ≤ 4 then
            (Work.Spaces.mixed j' i' (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ i' ∈ Finset.range 5, ∑ j' ∈ Finset.range 5,
              ((6400000 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) / z ^ 2) :=
            Finset.sum_le_sum (fun i' hi' => Finset.sum_le_sum (fun j' hj' => hterm2 i' hi' j' hj'))
        _ = 25 * ((6400000 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) / z ^ 2) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    -- `1/z² ≤ 4/(1+z)²` for `z ≥ 1`
    have hz2 : 1 / z ^ 2 ≤ 4 / (1 + z) ^ 2 := by
      have h1 : (0 : ℝ) < z ^ 2 := by positivity
      have h2 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
      rw [div_le_div_iff₀ h1 h2]
      nlinarith [hz1]
    -- `Γ²sin^{-η}, Γ²sin^{-γ} ≤ angMaj`
    have hη : Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ angMaj α θ := by
      rw [angMaj_apply]
      have h1 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_nonneg (sq_nonneg _) hsgam
      linarith
    have hgam : Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ angMaj α θ := by
      rw [angMaj_apply]
      have h1 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        mul_nonneg (sq_nonneg _) hsη
      linarith
    -- the final comparison
    have hkey : 5 * ((64 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / z ^ 2)
          + 25 * ((6400000 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) / z ^ 2)
        ≤ (20 * (64 * Kc) ^ 2 + 100 * (6400000 * Kc) ^ 2) * α ^ 2 * angMaj α θ
            / (1 + z) ^ 2 := by
      set X1 : ℝ := (64 * Kc) ^ 2 * α ^ 2
        * (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) with hX1
      set X2 : ℝ := (6400000 * Kc) ^ 2 * α ^ 2
        * (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) with hX2
      have hX10 : 0 ≤ X1 := by
        rw [hX1]; exact mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) hsη)
      have hX20 : 0 ≤ X2 := by
        rw [hX2]; exact mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) hsgam)
      have hX1le : X1 ≤ (64 * Kc) ^ 2 * α ^ 2 * angMaj α θ := by
        rw [hX1]
        exact mul_le_mul_of_nonneg_left hη (by positivity)
      have hX2le : X2 ≤ (6400000 * Kc) ^ 2 * α ^ 2 * angMaj α θ := by
        rw [hX2]
        exact mul_le_mul_of_nonneg_left hgam (by positivity)
      calc 5 * ((64 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / z ^ 2)
          + 25 * ((6400000 * Kc) ^ 2 * α ^ 2 * Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) / z ^ 2)
          = (5 * X1 + 25 * X2) * (1 / z ^ 2) := by rw [hX1, hX2]; ring
        _ ≤ (5 * X1 + 25 * X2) * (4 / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_left hz2 (by linarith)
        _ = (20 * X1 + 100 * X2) / (1 + z) ^ 2 := by ring
        _ ≤ (20 * ((64 * Kc) ^ 2 * α ^ 2 * angMaj α θ)
              + 100 * ((6400000 * Kc) ^ 2 * α ^ 2 * angMaj α θ))
              / (1 + z) ^ 2 :=
            div_le_div_of_nonneg_right (by linarith [hX1le, hX2le]) (le_of_lt hden)
        _ = (20 * (64 * Kc) ^ 2 + 100 * (6400000 * Kc) ^ 2) * α ^ 2 * angMaj α θ
              / (1 + z) ^ 2 := by ring
    rw [Work.Spaces.HkIntegrand]
    exact le_trans (add_le_add hsum1 hsum2) hkey
  · -- #### the vanishing case `z < 1`
    have hzlt : z < 1 := lt_of_not_ge hz1
    have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
    have hLz : z < L := lt_of_lt_of_le hzlt hL
    have hzero := ZFBase.HkIntegrand_eq_zero_of_eventually_zero (α := α) (k := 4) (z := z) (θ := θ)
      (f := Work.Stability.zfar L (Work.Construction.Fstar α))
      (ZFBase.zfar_eventually_zero hL0 hz0 hLz)
    rw [hzero]
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg α)) hang0)
      (le_of_lt (by positivity : (0 : ℝ) < (1 + z) ^ 2))

end Work.FTS.LocData
end
end
