import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.Gradient.Basic
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.CurlGrad.div_crossVec_eq
import Submission.Work.FTS.PressureOn.CurlGrad.fderiv_normed_convolution_eq
import Submission.Work.FTS.PressureOn.CurlGrad.vorticity_gradient_eq_zero
import Submission.Work.FTS.PressureOn.CurlGrad.tendsto_integral_inner_fderiv_convolution
import Submission.Work.FTS.PressureOn.CurlGrad.gradient_crossVec_bundle
import Submission.Work.FTS.BSIdent.Liouville.continuous_vorticity_of_contDiff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∫ ⟪ω, ∇ψ⟫ = 0` for a curl and a compactly supported `C¹` test function

`Work.FTS.PressureOn.CurlGrad.vorticity_gradient_integral_eq_zero`: for `u : ℝ³ → ℝ³` of class `C¹`
and `ψ : ℝ³ → ℝ` of class `C¹` with compact support,

  `∫ x, ⟪vorticity u x, gradient ψ x⟫ = 0`.

This is the statement that `div (curl u) = 0` in the sense of distributions: it is what turns the
distributional Poisson equation of the pressure reconstruction into an identity against test
functions.

## Route

* **Smooth case** (`integral_vorticity_gradient_eq_zero_of_contDiff_two`): for `φ ∈ C²` with compact
  support, the field `X := u × ∇φ` is `C¹` with compact support, so `∫ div X = 0`
  (`Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt`); and pointwise
  `div X = ⟪curl u, ∇φ⟫ - ⟪u, curl ∇φ⟫ = ⟪curl u, ∇φ⟫`, the second term vanishing because the curl
  of a gradient is zero (`div_crossVec_eq`, `vorticity_gradient_eq_zero`).
* **General `ψ ∈ C¹`**: approximate by convolution with the bump family `bumpSeq ρ n`
  (`HasCompactSupport.contDiff_convolution_left`), apply the smooth case to each approximation and
  pass to the limit (`tendsto_integral_inner_fderiv_convolution`).
-/

open FiniteTimeSingularity MeasureTheory Filter
open scoped Convolution Gradient Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.CurlGrad

open Work.FTS.PressureOn (R3 crossVec)

/-! ## The smooth case -/

/-- **The smooth case**: for a `C²` compactly supported test function `φ`, `∫ ⟪curl u, ∇φ⟫ = 0`. -/
theorem integral_vorticity_gradient_eq_zero_of_contDiff_two {u : R3 → R3} (hu : ContDiff ℝ 1 u)
    {φ : R3 → ℝ} (hφ : ContDiff ℝ 2 φ) (hφcs : HasCompactSupport φ) :
    ∫ x, inner ℝ (vorticity u x) (gradient φ x) = 0 := by
  -- regularity of the field `X := fun x => u x × ∇φ x`
  have hreg := gradient_crossVec_bundle hu hφ hφcs
  obtain ⟨hgrad, hXcont, hXdiff, hXcs, hXint⟩ := hreg
  -- the pointwise identity `div X = ⟪curl u, ∇φ⟫`
  have hpoint : ∀ x, div (fun y => crossVec (u y) (gradient φ y)) x
      = inner ℝ (vorticity u x) (gradient φ x) := by
    intro x
    rw [div_crossVec_eq ((hu.differentiable_one x).hasFDerivAt) (hgrad x)]
    have hcurl : vorticity (gradient φ) x = 0 :=
      vorticity_gradient_eq_zero (x := x) hφ.contDiffAt
    rw [hcurl, inner_zero_right, sub_zero]
  rw [show (∫ x, inner ℝ (vorticity u x) (gradient φ x))
      = ∫ x, div (fun y => crossVec (u y) (gradient φ y)) x from by
        congr 1 with x
        exact (hpoint x).symm]
  exact integral_div_eq_zero_of_hasFDerivAt _ hXcs hXcont hXdiff hXint

/-! ## The bump family -/

/-- A sequence of bump functions with `rOut → 0`: `bumpSeq ρ n` has the radii of `ρ` divided by
`n + 1`. -/
noncomputable def bumpSeq (ρ : ContDiffBump (0 : R3)) (n : ℕ) : ContDiffBump (0 : R3) :=
  ⟨ρ.rIn / ((n : ℝ) + 1), ρ.rOut / ((n : ℝ) + 1), div_pos ρ.rIn_pos (by positivity),
    div_lt_div_of_pos_right ρ.rIn_lt_rOut (by positivity)⟩

@[simp] theorem bumpSeq_rIn (ρ : ContDiffBump (0 : R3)) (n : ℕ) :
    (bumpSeq ρ n).rIn = ρ.rIn / ((n : ℝ) + 1) := rfl

@[simp] theorem bumpSeq_rOut (ρ : ContDiffBump (0 : R3)) (n : ℕ) :
    (bumpSeq ρ n).rOut = ρ.rOut / ((n : ℝ) + 1) := rfl

/-- The outer radii of `bumpSeq ρ n` tend to `0`. -/
theorem tendsto_rOut_bumpSeq (ρ : ContDiffBump (0 : R3)) :
    Tendsto (fun n : ℕ => (bumpSeq ρ n).rOut) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => ρ.rOut / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) ρ.rOut).comp
      (tendsto_add_atTop_nat 1)
    convert h using 1
    ext n
    simp [Nat.cast_add, Nat.cast_one]
  simpa only [bumpSeq_rOut] using h0

/-! ## The general case -/

/-- **The main statement**: `∫ ⟪vorticity u, ∇ψ⟫ = 0` for `u ∈ C¹` and `ψ ∈ C¹` compactly
supported. -/
theorem vorticity_gradient_integral_eq_zero {u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : ContDiff ℝ 1 u) (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    ∫ x, inner ℝ (FiniteTimeSingularity.vorticity u x) (gradient ψ x) = 0 := by
  -- step 1: the integrand is `dψ(ω)`
  have h1 : (∫ x, inner ℝ (vorticity u x) (gradient ψ x))
      = ∫ x, fderiv ℝ ψ x (vorticity u x) := by
    congr 1 with x
    rw [real_inner_comm, inner_gradient_left]
  rw [h1]
  -- step 2: approximate `ψ` by smooth compactly supported functions
  let ρ : ContDiffBump (0 : R3) := default
  have hφ : Tendsto (fun n : ℕ => (bumpSeq ρ n).rOut) atTop (𝓝 0) := tendsto_rOut_bumpSeq ρ
  have hlim := tendsto_integral_inner_fderiv_convolution (ω := vorticity u)
    (Work.FTS.BSIdent.Liouville.continuous_vorticity_of_contDiff hu) hψ hψcs
    (φ := fun n => bumpSeq ρ n) hφ
  -- step 3: each approximating integral vanishes by the smooth case
  have hsmooth : ∀ n : ℕ,
      (∫ x, fderiv ℝ (MeasureTheory.convolution ((bumpSeq ρ n).normed volume) ψ
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (vorticity u x)) = 0 := by
    intro n
    set ψn : R3 → ℝ := MeasureTheory.convolution ((bumpSeq ρ n).normed volume) ψ
      (ContinuousLinearMap.lsmul ℝ ℝ) volume with hψndef
    have hsm : ContDiff ℝ 2 ψn :=
      ((bumpSeq ρ n).hasCompactSupport_normed).contDiff_convolution_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) (n := (2 : ℕ∞))
        (bumpSeq ρ n).contDiff_normed hψ.continuous.locallyIntegrable
    have hcs : HasCompactSupport ψn :=
      ((bumpSeq ρ n).hasCompactSupport_normed).convolution
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hψcs
    have h0 := integral_vorticity_gradient_eq_zero_of_contDiff_two hu hsm hcs
    rw [show (∫ x, fderiv ℝ ψn x (vorticity u x))
        = ∫ x, inner ℝ (vorticity u x) (gradient ψn x) from by
          congr 1 with x
          rw [real_inner_comm, inner_gradient_left]]
    exact h0
  -- step 4: pass to the limit
  have hzero : (∫ x, fderiv ℝ ψ x (vorticity u x)) = 0 :=
    tendsto_nhds_unique hlim
      (Filter.Tendsto.congr' (Eventually.of_forall fun n => (hsmooth n).symm)
        tendsto_const_nhds)
  exact hzero

end Work.FTS.PressureOn.CurlGrad
