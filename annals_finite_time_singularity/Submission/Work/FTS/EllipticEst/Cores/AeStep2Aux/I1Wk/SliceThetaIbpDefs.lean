/-
Copyright: work module for the Elgindi finite-time singularity project.

# Definitions for the θ-slice identity `S2` with a θ-cutoff (`sliceThetaIbpSep`)

This file fixes the notation for the slice identity

  `∫_θ σ ψ v v'' = -2η∫ σψv² - κ∫ σψ(v')² - (2η/(1+η))∫ σψ(v' - (1+η)v cos2θ/sin2θ)²
                    + (1/2)∫ σψ'' v²`

(`σ = sin(2θ)^{-η}`, `κ = (1-η)/(1+η)`, `η = Work.Spaces.eta = 99/100`) which is proved in
`sliceThetaIbpSep.lean` for `v ∈ C²((0,π/2))` and `ψ ∈ C²(ℝ)` with
`tsupport ψ ⊆ (a,b) ⊂ (0,π/2)`.

The identity is the integral of the total-derivative identity

  `(G v ψ)' = L v ψ - RHS v ψ`   on `(0,π/2)`,

where

  `G v ψ θ = ψ θ · (σ θ · v θ · v' θ - η · (cos 2θ · σ₁ θ) · v θ²) - (1/2) · ψ' θ · σ θ · v θ²`

is a boundary primitive whose derivative is the difference of the two integrands.  All the
elementary pieces (`σ = sin(2θ)^{-η}` and its companions `σ₁`, `σ₂`, the pointwise slice
identity of `slice_second_identity`) come from the sibling modules
`slice_second_defs` / `slice_second_trunc`.

The *only* algebraic input is the identity `theta_alg`: after division by the (positive)
factors `σ₂ ψ` it is the elementary `sin`/`cos`-polynomial identity

  `s²(v')² - 4η·c·s·v v' + 2η(1+η)c²v² = κ s²(v')² + (2η/(1+η))(s v' - (1+η)c v)²`
  (`s = sin 2θ`, `c = cos 2θ`, `η = 99/100`),
which holds because `κ = (1-η)/(1+η)`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_defs
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_trunc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

set_option autoImplicit false

/-! ## The integrands -/

/-- `c·σ₁`, i.e. `cos(2θ)·sin(2θ)^{-(1+η)}`. -/
def sigc (θ : ℝ) : ℝ := Real.cos (2 * θ) * sig1 θ

/-- The LHS integrand `σ ψ v v''`. -/
def Lfun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ := sig θ * ψ θ * (v θ * deriv (deriv v) θ)

/-- The `∫ σψv²` integrand. -/
def Afun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ := sig θ * ψ θ * (v θ) ^ 2

/-- The `∫ σψ(v')²` integrand. -/
def Bfun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ := sig θ * ψ θ * (deriv v θ) ^ 2

/-- The `∫ σψ(v' - (1+η)v cos2θ/sin2θ)²` integrand (written with `sin(2θ)^{-1}`). -/
def Cfun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  sig θ * ψ θ * (deriv v θ - (1 + Work.Spaces.eta) * v θ * Real.cos (2 * θ)
    * (Real.sin (2 * θ)) ^ (-(1 : ℝ))) ^ 2

/-- The `∫ σψ'' v²` integrand. -/
def Dfun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ := sig θ * deriv (deriv ψ) θ * (v θ) ^ 2

/-- The whole RHS integrand, `-2η σψv² - κ σψ(v')² - (2η/(1+η)) σψ(...)² + (1/2) σψ''v²`. -/
def RHSfun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  -2 * Work.Spaces.eta * Afun v ψ θ - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
      * Bfun v ψ θ
    - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * Cfun v ψ θ + (1 / 2) * Dfun v ψ θ

/-- The integrand of the total derivative: `L v ψ - RHS v ψ`. -/
def GderivFun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ := Lfun v ψ θ - RHSfun v ψ θ

/-- The boundary primitive of the θ-IBP. -/
def Gfun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ψ θ * (sig θ * (v θ * deriv v θ) - Work.Spaces.eta * (sigc θ * (v θ) ^ 2))
    - (1 / 2) * (deriv ψ θ * (sig θ * (v θ) ^ 2))

/-- The derivative of `Gfun`, in the factored form that the product-rule chain produces
(see `hasDerivAt_Gfun`). -/
def Rawk (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  Lfun v ψ θ
    + ψ θ * (sig θ * (deriv v θ) ^ 2
        - 4 * Work.Spaces.eta * (Real.cos (2 * θ) * sig1 θ) * (v θ * deriv v θ)
        + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2 * sig2 θ
            * (v θ) ^ 2)
    + 2 * Work.Spaces.eta * sig θ * ψ θ * (v θ) ^ 2
    - (1 / 2) * sig θ * deriv (deriv ψ) θ * (v θ) ^ 2

/-! ## Elementary consequences of `slice_second_trunc` -/

/-- `σ θ = σ₂ θ · sin(2θ)²`. -/
lemma sig_eq_sig2_mul_sin_sq {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    sig θ = sig2 θ * (Real.sin (2 * θ)) ^ 2 := by
  rw [sst_sig_eq_sig1_mul_sin hθ, sst_sig1_eq_sig2_mul_sin hθ]
  ring

/-- `σ₁ θ = σ₂ θ · sin(2θ)`. -/
lemma sig1_eq_sig2_mul_sin {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    sig1 θ = sig2 θ * Real.sin (2 * θ) :=
  sst_sig1_eq_sig2_mul_sin hθ

/-- `(c σ₁)' = -2σ - 2(1+η)c²σ₂`. -/
lemma hasDerivAt_sigc {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt sigc (-2 * sig θ - 2 * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2
      * sig2 θ) θ := by
  have hc : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-2 * Real.sin (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ : ℝ => 2 * θ) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_cos (2 * θ)).comp θ h1
  refine ((hc.mul (sst_hasDerivAt_sig1 hθ)).congr_deriv ?_)
  rw [sst_sig_eq_sig1_mul_sin hθ]
  ring

/-! ## Vanishing near a point outside the topological support -/

lemma eventuallyEq_zero_of_notMem_tsupport {f : ℝ → ℝ} {x : ℝ} (hx : x ∉ tsupport f) :
    f =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport hy

lemma deriv_eq_zero_of_notMem_tsupport {f : ℝ → ℝ} {x : ℝ} (hx : x ∉ tsupport f) :
    deriv f x = 0 := by
  rw [(eventuallyEq_zero_of_notMem_tsupport hx).deriv_eq]
  simp [deriv_const]

lemma deriv_deriv_eq_zero_of_notMem_tsupport {f : ℝ → ℝ} {x : ℝ} (hx : x ∉ tsupport f) :
    deriv (deriv f) x = 0 := by
  have h1 : deriv f =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    exact deriv_eq_zero_of_notMem_tsupport hy
  rw [h1.deriv_eq]
  simp [deriv_const]

/-! ## Converting a `Set.Ioo 0 (π/2)`-integral of a compactly supported function -/

/-- If `f` vanishes on `(0, π/2) \ [a,b]`, then its integral over `(0, π/2)` is its interval
integral over `[a,b]`. -/
theorem setIntegral_Ioo_eq_intervalIntegral_of_support {f : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : b < Real.pi / 2) (hab : a ≤ b)
    (hf : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → f θ = 0) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), f θ) = ∫ θ in a..b, f θ := by
  have h1 : (∫ θ in Set.Ioo 0 (Real.pi / 2), f θ) = ∫ θ in Set.Icc a b, f θ :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
      (fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩)
      (fun x hx => by
        have hx' : x ∉ Set.Icc a b := hx.2
        simp only [Set.mem_Icc, not_and_or, not_le] at hx'
        exact hf x hx.1.1 hx.1.2 hx')
  rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-! ## The algebraic core -/

/-- **The algebraic core of the slice identity.**  For `θ ∈ (0, π/2)`,
`σ v'² - 4η (cσ₁) v v' + 2η(1+η) c² σ₂ v² = κ σ v'² + (2η/(1+η)) σ (v' - (1+η)v c/s)²`
with `σ = sin(2θ)^{-η}`, `σ₁ = sin(2θ)^{-(1+η)}`, `σ₂ = sin(2θ)^{-(2+η)}`,
`s = sin 2θ`, `c = cos 2θ` and `κ = (1-η)/(1+η)`. -/
theorem theta_alg {v : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    sig θ * (deriv v θ) ^ 2
        - 4 * Work.Spaces.eta * (Real.cos (2 * θ) * sig1 θ) * (v θ * deriv v θ)
        + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2 * sig2 θ
            * (v θ) ^ 2
      = ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (sig θ * (deriv v θ) ^ 2)
        + (2 * Work.Spaces.eta / (1 + Work.Spaces.eta))
            * (sig θ * (deriv v θ - (1 + Work.Spaces.eta) * v θ * Real.cos (2 * θ)
                * (Real.sin (2 * θ)) ^ (-(1 : ℝ))) ^ 2) := by
  have hs : Real.sin (2 * θ) ≠ 0 := ne_of_gt (sst_sin_two_pos hθ)
  have h1 : (1 + Work.Spaces.eta) ≠ 0 := by
    rw [Work.Spaces.eta]; norm_num
  rw [sst_sig_eq_sig1_mul_sin hθ, sst_sig1_eq_sig2_mul_sin hθ, Real.rpow_neg_one]
  field_simp
  ring

/-- `Rawk` is the derivative of `Gfun` and equals `Lfun - RHSfun`. -/
theorem Rawk_eq (v ψ : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Rawk v ψ θ = Lfun v ψ θ - RHSfun v ψ θ := by
  unfold Rawk RHSfun Afun Bfun Cfun Dfun
  rw [theta_alg hθ]
  ring

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
