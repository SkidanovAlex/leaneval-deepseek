/-
The real (`deriv`-level) form of the transported operator `kopD` of `Q0/RRDefs.lean`, together
with the bridge between `kopD` (acting on complex-valued functions) and the real operator
`kopDr` (acting on real-valued functions) applied to the real / imaginary parts.

`kopDr ψ σ θ` is exactly the right-hand side of `Work.EllipticEst.InteriorRegularity.bslOp_comp_exp`
(the operator `bslOp α` in the `(σ,θ)`-coordinates at `z = exp (α σ)`), while

* `kopD_re` : `Re (kopD ψ σ θ) = kopDr (fun σ θ => (ψ σ θ).re) σ θ`
* `kopD_im` : `Im (kopD ψ σ θ) = kopDr (fun σ θ => (ψ σ θ).im) σ θ`

for `ψ` smooth.  These are what turns the (complex) strip weak formulation into two (real)
half-strip weak formulations.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.EllipticEst.InteriorRegularity.Q0.RRDefs

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

/-- The real (`deriv`-level) form of the transported operator: this is `bslOp α` in the
`(σ,θ)`-coordinates at `z = exp (α σ)` for a test function of the form `ψ (log z / α) θ`. -/
def kopDr (ψ : ℝ → ℝ → ℝ) (σ θ : ℝ) : ℝ :=
  - deriv (fun σ' => deriv (fun σ'' => ψ σ'' θ) σ') σ
    - deriv (fun θ' => deriv (fun θ'' => ψ σ θ'') θ') θ
    - 5 * deriv (fun σ' => ψ σ' θ) σ
    + Real.tan θ * deriv (fun θ' => ψ σ θ') θ
    + ((Real.tan θ) ^ 2 - 5) * ψ σ θ

/-- `deriv` commutes with (the composition by) a continuous linear map. -/
lemma deriv_clm_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : ℝ → E} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) :
    deriv (fun y => L (f y)) x = L (deriv f x) := by
  have h2 : HasFDerivAt (fun y : ℝ => L (f y)) (L.comp (fderiv ℝ f x)) x :=
    L.hasFDerivAt.comp x hf.hasFDerivAt
  rw [h2.hasDerivAt.deriv, ContinuousLinearMap.comp_apply, (hf.hasFDerivAt.hasDerivAt).deriv]

/-- The real part of the derivative of a complex-valued function is the derivative of its real
part. -/
lemma deriv_re_fst {f : ℝ → ℂ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    (deriv f x).re = deriv (fun y => (f y).re) x := by
  have h := deriv_clm_comp (L := Complex.reCLM) hf
  simpa [Complex.reCLM_apply] using h.symm

/-- The imaginary part of the derivative of a complex-valued function is the derivative of its
imaginary part. -/
lemma deriv_im_fst {f : ℝ → ℂ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    (deriv f x).im = deriv (fun y => (f y).im) x := by
  have h := deriv_clm_comp (L := Complex.imCLM) hf
  simpa [Complex.imCLM_apply] using h.symm

/-- Differentiability of the `σ`-slices of a smooth function of two variables. -/
lemma contDiff2_fst_slice {ψ : ℝ → ℝ → ℂ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (θ : ℝ) : ContDiff ℝ 2 (fun σ' : ℝ => ψ σ' θ) := by
  have h : ContDiff ℝ 2 (fun σ' : ℝ => (σ', θ)) := ContDiff.prodMk contDiff_id contDiff_const
  have h2 : ContDiff ℝ 2 (fun σ' : ℝ => Function.uncurry ψ (σ', θ)) := (hψ 2).comp h
  simpa [Function.uncurry] using h2

/-- Differentiability of the `θ`-slices of a smooth function of two variables. -/
lemma contDiff2_snd_slice {ψ : ℝ → ℝ → ℂ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (σ : ℝ) : ContDiff ℝ 2 (fun θ' : ℝ => ψ σ θ') := by
  have h : ContDiff ℝ 2 (fun θ' : ℝ => (σ, θ')) := ContDiff.prodMk contDiff_const contDiff_id
  have h2 : ContDiff ℝ 2 (fun θ' : ℝ => Function.uncurry ψ (σ, θ')) := (hψ 2).comp h
  simpa [Function.uncurry] using h2

/-- **The real part of `kopD`.** -/
lemma kopD_re {ψ : ℝ → ℝ → ℂ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (σ θ : ℝ) :
    (kopD ψ σ θ).re = kopDr (fun σ θ => (ψ σ θ).re) σ θ := by
  have hσ : ContDiff ℝ 2 (fun σ' : ℝ => ψ σ' θ) := contDiff2_fst_slice hψ θ
  have hθ : ContDiff ℝ 2 (fun θ' : ℝ => ψ σ θ') := contDiff2_snd_slice hψ σ
  have hdσ : DifferentiableAt ℝ (fun σ' : ℝ => ψ σ' θ) σ := (hσ.differentiable (by norm_num)) σ
  have hdθ : DifferentiableAt ℝ (fun θ' : ℝ => ψ σ θ') θ := (hθ.differentiable (by norm_num)) θ
  have hdσ2 : DifferentiableAt ℝ (deriv (fun σ' : ℝ => ψ σ' θ)) σ :=
    hσ.differentiable_deriv_two σ
  have hdθ2 : DifferentiableAt ℝ (deriv (fun θ' : ℝ => ψ σ θ')) θ :=
    hθ.differentiable_deriv_two θ
  have hA : (deriv (fun σ' => deriv (fun σ'' => ψ σ'' θ) σ') σ).re
      = deriv (fun σ' => deriv (fun σ'' => (ψ σ'' θ).re) σ') σ := by
    rw [deriv_re_fst (f := fun σ' : ℝ => deriv (fun σ'' : ℝ => ψ σ'' θ) σ') hdσ2]
    congr 1
    funext σ'
    exact deriv_re_fst (f := fun σ'' : ℝ => ψ σ'' θ) ((hσ.differentiable (by norm_num)) σ')
  have hB : (deriv (fun θ' => deriv (fun θ'' => ψ σ θ'') θ') θ).re
      = deriv (fun θ' => deriv (fun θ'' => (ψ σ θ'').re) θ') θ := by
    rw [deriv_re_fst (f := fun θ' : ℝ => deriv (fun θ'' : ℝ => ψ σ θ'') θ') hdθ2]
    congr 1
    funext θ'
    exact deriv_re_fst (f := fun θ'' : ℝ => ψ σ θ'') ((hθ.differentiable (by norm_num)) θ')
  have hC : (deriv (fun σ' => ψ σ' θ) σ).re = deriv (fun σ' => (ψ σ' θ).re) σ :=
    deriv_re_fst (f := fun σ' : ℝ => ψ σ' θ) hdσ
  have hD : (deriv (fun θ' => ψ σ θ') θ).re = deriv (fun θ' => (ψ σ θ').re) θ :=
    deriv_re_fst (f := fun θ' : ℝ => ψ σ θ') hdθ
  have h5 : (5 : ℂ) = ((5 : ℝ) : ℂ) := by norm_num
  simp only [kopD]
  rw [h5]
  simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero, zero_add]
  rw [hA, hB, hC, hD]
  simp only [kopDr]
  ring

/-- **The imaginary part of `kopD`.** -/
lemma kopD_im {ψ : ℝ → ℝ → ℂ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (σ θ : ℝ) :
    (kopD ψ σ θ).im = kopDr (fun σ θ => (ψ σ θ).im) σ θ := by
  have hσ : ContDiff ℝ 2 (fun σ' : ℝ => ψ σ' θ) := contDiff2_fst_slice hψ θ
  have hθ : ContDiff ℝ 2 (fun θ' : ℝ => ψ σ θ') := contDiff2_snd_slice hψ σ
  have hdσ : DifferentiableAt ℝ (fun σ' : ℝ => ψ σ' θ) σ := (hσ.differentiable (by norm_num)) σ
  have hdθ : DifferentiableAt ℝ (fun θ' : ℝ => ψ σ θ') θ := (hθ.differentiable (by norm_num)) θ
  have hdσ2 : DifferentiableAt ℝ (deriv (fun σ' : ℝ => ψ σ' θ)) σ :=
    hσ.differentiable_deriv_two σ
  have hdθ2 : DifferentiableAt ℝ (deriv (fun θ' : ℝ => ψ σ θ')) θ :=
    hθ.differentiable_deriv_two θ
  have hA : (deriv (fun σ' => deriv (fun σ'' => ψ σ'' θ) σ') σ).im
      = deriv (fun σ' => deriv (fun σ'' => (ψ σ'' θ).im) σ') σ := by
    rw [deriv_im_fst (f := fun σ' : ℝ => deriv (fun σ'' : ℝ => ψ σ'' θ) σ') hdσ2]
    congr 1
    funext σ'
    exact deriv_im_fst (f := fun σ'' : ℝ => ψ σ'' θ) ((hσ.differentiable (by norm_num)) σ')
  have hB : (deriv (fun θ' => deriv (fun θ'' => ψ σ θ'') θ') θ).im
      = deriv (fun θ' => deriv (fun θ'' => (ψ σ θ'').im) θ') θ := by
    rw [deriv_im_fst (f := fun θ' : ℝ => deriv (fun θ'' : ℝ => ψ σ θ'') θ') hdθ2]
    congr 1
    funext θ'
    exact deriv_im_fst (f := fun θ'' : ℝ => ψ σ θ'') ((hθ.differentiable (by norm_num)) θ')
  have hC : (deriv (fun σ' => ψ σ' θ) σ).im = deriv (fun σ' => (ψ σ' θ).im) σ :=
    deriv_im_fst (f := fun σ' : ℝ => ψ σ' θ) hdσ
  have hD : (deriv (fun θ' => ψ σ θ') θ).im = deriv (fun θ' => (ψ σ θ').im) θ :=
    deriv_im_fst (f := fun θ' : ℝ => ψ σ θ') hdθ
  have h5 : (5 : ℂ) = ((5 : ℝ) : ℂ) := by norm_num
  simp only [kopD]
  rw [h5]
  simp only [Complex.neg_im, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, zero_add, zero_mul]
  rw [hA, hB, hC, hD]
  simp only [kopDr]
  try ring

end Work.EllipticEst.InteriorRegularity.Q0
