/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The quadratic weight has Hessian bound `K`

For the quadratic weight `φ(z) = K‖z‖²` on `ℂⁿ` the complex Hessian is the scalar
matrix `K·δ_{ij}`, so `φ` satisfies `HessLowerBound φ K`: the `L²` theory of `∂̄`
with weight `φ = K‖z‖²` gains a factor `K`.

The file contains the computation of `∂̄φ`, `∂φ` and `∂∂̄φ` for the quadratic
weight (the last one showing `hessPhi i j = K δ_{ij}`), and then deduces the
Hermitian-form lower bound by an explicit evaluation of the defining sum.
-/
import Mathlib
import Submission.Work.Hormander.Weights.Basic
import Submission.Work.Hormander.Weights.fderiv_quadWeight

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

variable {n : ℕ}

/-! ### The real inner product against the basis vectors -/

/-- `⟪z, e_j⟫_ℝ` is the real part of the `j`-th complex coordinate of `z`. -/
lemma hessLB_inner_evec (n : ℕ) (j : Fin n) (z : Cn n) :
    inner ℝ z (evec n j) = (coord n j z).re := by
  rw [show evec n j = (EuclideanSpace.single j 1 : Cn n) from rfl]
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single j]
  · simp [Complex.inner, coord_apply]
  · intro b _ hb
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- `⟪z, i e_j⟫_ℝ` is the imaginary part of the `j`-th complex coordinate of `z`. -/
lemma hessLB_inner_ivec (n : ℕ) (j : Fin n) (z : Cn n) :
    inner ℝ z (ivec n j) = (coord n j z).im := by
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single j]
  · simp [Complex.inner, coord_apply]
  · intro b _ hb
    simp [ivec_ofLp, Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ j) h

/-! ### The first derivatives of the quadratic weight -/

/-- `∂̄_j (K‖·‖²) = K z_j`. -/
lemma hessLB_dbarPhi_quadWeight (K : ℝ) (j : Fin n) (z : Cn n) :
    dbarPhi n j (quadWeight n K) z = K * coord n j z := by
  have hfd : fderiv ℝ (fun w : Cn n => (((quadWeight n K) w : ℝ) : ℂ)) z
      = (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (fderiv ℝ (quadWeight n K) z) := by
    have hg : DifferentiableAt ℝ (fun t : ℝ => (t : ℂ)) ((quadWeight n K) z) :=
      Complex.differentiable_ofReal.differentiableAt
    have hf : DifferentiableAt ℝ (quadWeight n K) z :=
      ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul K).differentiableAt
    have hcomp := fderiv_comp (𝕜 := ℝ) z hg hf
    simp only [Function.comp_def] at hcomp
    rw [hcomp]
    congr 1
    exact Complex.ofRealCLM.fderiv
  rw [dbarPhi, dbarCoord, hfd]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, fderiv_quadWeight,
    hessLB_inner_evec, hessLB_inner_ivec]
  conv_rhs => rw [← Complex.re_add_im (coord n j z)]
  push_cast
  ring

/-- `∂̄_j (K‖·‖²)` as an equality of functions. -/
lemma hessLB_dbarPhi_quadWeight_fun (K : ℝ) (j : Fin n) :
    dbarPhi n j (quadWeight n K) = fun w : Cn n => K * coord n j w :=
  funext fun z => hessLB_dbarPhi_quadWeight K j z

/-! ### The complex Hessian of the quadratic weight -/

/-- The complex Hessian of `K‖·‖²` is `K·δ_{ij}`. -/
lemma hessLB_hessPhi_quadWeight (K : ℝ) (i j : Fin n) (z : Cn n) :
    hessPhi n i j (quadWeight n K) z = (if i = j then (K : ℂ) else 0) := by
  unfold hessPhi
  rw [hessLB_dbarPhi_quadWeight_fun]
  have hfd : fderiv ℝ (fun w : Cn n => K * coord n j w) z
      = (K : ℝ) • ((coord n j : Cn n →L[ℂ] ℂ).restrictScalars ℝ) := by
    have hfun : (fun w : Cn n => K * coord n j w)
        = fun w => ((K : ℝ) • ((coord n j : Cn n →L[ℂ] ℂ).restrictScalars ℝ)) w := by
      funext w
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_restrictScalars',
        RCLike.real_smul_eq_coe_mul]
    rw [hfun]
    exact ContinuousLinearMap.fderiv _
  rw [dCoord, hfd]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_restrictScalars',
    RCLike.real_smul_eq_coe_mul]
  by_cases h : i = j
  · subst h
    have hIK : Complex.I * ((K:ℂ) * Complex.I) = -(K:ℂ) := by
      rw [← mul_assoc, mul_comm Complex.I (K:ℂ), mul_assoc, Complex.I_mul_I, mul_neg, mul_one]
    simp [coord_evec, coord_ivec, hIK]
    ring_nf
  · have hji : j ≠ i := fun hh => h hh.symm
    simp [coord_evec, coord_ivec, hji, h]

/-! ### The Hessian lower bound -/

theorem HessLowerBound_quadWeight {n : ℕ} (K : ℝ) :
    HessLowerBound (quadWeight n K) K := by
  intro z v
  simp only [hessLB_hessPhi_quadWeight K]
  have hterm : ∀ i, (∑ j, (if i = j then (K:ℂ) else 0) * (v i * star (v j)))
      = (K : ℂ) * ((‖v i‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
      have h2 : v i * star (v i) = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj, Complex.sq_norm]
      rw [h2]
    · intro b _ hb
      rw [if_neg (fun hh => hb hh.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hsum : (∑ i, ∑ j, (if i = j then (K:ℂ) else 0) * (v i * star (v j)))
      = (K : ℂ) * ∑ i, ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [hterm]
    rw [← Finset.mul_sum]
  rw [hsum]
  simp [pow_two, Complex.mul_re]

end Work.Hormander.Weights
