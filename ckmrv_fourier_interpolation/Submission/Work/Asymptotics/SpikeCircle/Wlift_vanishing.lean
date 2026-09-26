import Mathlib
import Submission.Work.Asymptotics.SpikeCircle.SpikeDefs

/-!
# Vanishing of the lifted spike `Wlift` at the three special points

The lifted spike

  `Wlift ℓ d τ w = Δ(τ) · Δ(w) · (AfunFun ℓ d τ w - Tleft τ w)`

is built so that the principal parts of the cleared kernel `AfunFun` at the two translates
`w = τ ± 1` are cancelled by the correction term `Tleft` (the `(2π)⁻¹`-multiple of the difference
of the two divided differences `D1`, `D2` of `w ↦ j(τ) - j(w)`), and so that the resulting
function vanishes at the three points `w = τ - 1, τ, τ + 1` where the modular discriminant
`Δ(w)` or the `j`-invariance `j(τ±1) = j(τ)` enter.

We prove here the vanishing at the three points, which is the input for the circle/divisor
bound on the spike.  The main ingredients are:

* `j`-`T`-invariance, `jInvariantFun ((1:ℝ)+ᵥτ) = jInvariantFun τ` (Mathlib-side
  `KernelFacts.jInvariantFun_vadd_one`) and its `-1` version recalled here;
* the values of `AfunFun` at the three points (`AfunFun_self`, `AfunFun_pos`, `AfunFun_neg`,
  from `SpikeDefs`);
* the values of the `dslope` functions `D1`, `D2` at the three points, computed from the
  `T`-invariance of `j` together with the derivative dictionary
  `deriv (j ∘ ofComplex) = jprime`.
-/

noncomputable section
open UpperHalfPlane
open scoped Topology Manifold

namespace Work.Asymptotics.SpikeCircle

open Work.Kernels Work.Residues

/-! ## `j`-invariance under `τ ↦ τ - 1` -/

lemma jInvariantFun_vadd_neg_one (τ : UpperHalfPlane) :
    jInvariantFun ((-1 : ℝ) +ᵥ τ) = jInvariantFun τ := by
  have h := KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ τ)
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ from by rw [← add_vadd]; norm_num] at h
  exact h.symm

/-! ## The values of `jlDiff` at the three special points -/

lemma jlDiff_eq_zero_self (τ : UpperHalfPlane) : jlDiff τ (τ : ℂ) = 0 := by
  simp only [jlDiff, ofComplex_self, sub_self]

lemma jlDiff_eq_zero_sub_one (τ : UpperHalfPlane) : jlDiff τ ((τ : ℂ) - 1) = 0 := by
  simp only [jlDiff, ofComplex_sub_one, jInvariantFun_vadd_neg_one, sub_self]

lemma jlDiff_eq_zero_add_one (τ : UpperHalfPlane) : jlDiff τ ((τ : ℂ) + 1) = 0 := by
  simp only [jlDiff, ofComplex_add_one, KernelFacts.jInvariantFun_vadd_one, sub_self]

/-! ## The derivative of `jlDiff` -/

/-- The derivative of `w ↦ j(τ) - j(w)` is `-jprime`. -/
lemma deriv_jlDiff_eq {τ : UpperHalfPlane} {w : ℂ} (hw : 0 < w.im) :
    deriv (jlDiff τ) w = - jprime (UpperHalfPlane.ofComplex w) := by
  have hc : ((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ) = w := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  have hd : DifferentiableAt ℂ (fun z : ℂ => jInvariantFun (UpperHalfPlane.ofComplex z)) w := by
    simpa using
      differentiableAt_comp_ofComplex_of_mdiff mdiff_jInvariantFun (⟨w, hw⟩ : UpperHalfPlane)
  have hcomp : deriv (fun z : ℂ => jInvariantFun (UpperHalfPlane.ofComplex z)) w
      = jprime (UpperHalfPlane.ofComplex w) := by
    have h := deriv_jInvariantFun_ofComplex (UpperHalfPlane.ofComplex w)
    simp only [Function.comp_def] at h
    rwa [hc] at h
  have heq : jlDiff τ = (fun _ : ℂ => jInvariantFun τ)
      - (fun z : ℂ => jInvariantFun (UpperHalfPlane.ofComplex z)) := rfl
  rw [heq, deriv_sub (differentiableAt_const (c := jInvariantFun τ)) hd, hcomp, deriv_const,
    zero_sub]

/-! ## The values of `D1`, `D2` at the three special points -/

lemma D1_eq_zero_self (τ : UpperHalfPlane) : D1 τ (τ : ℂ) = 0 := by
  have hne : (τ : ℂ) ≠ ((τ : ℂ) - 1) := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at hre
    linarith
  rw [D1, dslope_of_ne _ hne, slope_def_module, jlDiff_eq_zero_self, jlDiff_eq_zero_sub_one]
  simp

lemma D2_eq_zero_self (τ : UpperHalfPlane) : D2 τ (τ : ℂ) = 0 := by
  have hne : (τ : ℂ) ≠ ((τ : ℂ) + 1) := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re] at hre
    linarith
  rw [D2, dslope_of_ne _ hne, slope_def_module, jlDiff_eq_zero_self, jlDiff_eq_zero_add_one]
  simp

lemma D1_eq_zero_add_one (τ : UpperHalfPlane) : D1 τ ((τ : ℂ) + 1) = 0 := by
  have hne : (τ : ℂ) + 1 ≠ ((τ : ℂ) - 1) := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re] at hre
    linarith
  rw [D1, dslope_of_ne _ hne, slope_def_module, jlDiff_eq_zero_add_one, jlDiff_eq_zero_sub_one]
  simp

lemma D2_eq_zero_sub_one (τ : UpperHalfPlane) : D2 τ ((τ : ℂ) - 1) = 0 := by
  have hne : (τ : ℂ) - 1 ≠ ((τ : ℂ) + 1) := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re] at hre
    linarith
  rw [D2, dslope_of_ne _ hne, slope_def_module, jlDiff_eq_zero_sub_one, jlDiff_eq_zero_add_one]
  simp

lemma D1_eq_neg_jprime (τ : UpperHalfPlane) :
    D1 τ ((τ : ℂ) - 1) = - jprime ((-1 : ℝ) +ᵥ τ) := by
  have h : D1 τ ((((-1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) = - jprime ((-1 : ℝ) +ᵥ τ) := by
    rw [coe_neg_one_vadd τ, D1, dslope_same,
      deriv_jlDiff_eq (by rw [im_sub_one]; exact τ.im_pos), ofComplex_sub_one]
  rw [← coe_neg_one_vadd τ]; exact h

lemma D2_eq_neg_jprime (τ : UpperHalfPlane) :
    D2 τ ((τ : ℂ) + 1) = - jprime ((1 : ℝ) +ᵥ τ) := by
  have h : D2 τ ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) = - jprime ((1 : ℝ) +ᵥ τ) := by
    rw [coe_one_vadd τ, D2, dslope_same,
      deriv_jlDiff_eq (by rw [im_add_one]; exact τ.im_pos), ofComplex_add_one]
  rw [← coe_one_vadd τ]; exact h

/-! ## The values of `Tleft` at the three special points -/

lemma Tleft_eq_zero_self (τ : UpperHalfPlane) : Tleft τ (τ : ℂ) = 0 := by
  rw [Tleft, D1_eq_zero_self τ, D2_eq_zero_self τ, sub_zero, mul_zero]

lemma Tleft_eq_pos (τ : UpperHalfPlane) :
    Tleft τ ((τ : ℂ) + 1) = (1 / (2 * (Real.pi : ℂ))) * jprime ((1 : ℝ) +ᵥ τ) := by
  rw [Tleft, D1_eq_zero_add_one τ, D2_eq_neg_jprime τ]; ring

lemma Tleft_eq_neg (τ : UpperHalfPlane) :
    Tleft τ ((τ : ℂ) - 1) = -(1 / (2 * (Real.pi : ℂ))) * jprime ((-1 : ℝ) +ᵥ τ) := by
  rw [Tleft, D1_eq_neg_jprime τ, D2_eq_zero_sub_one τ]; ring

/-! ## Vanishing of `Wlift` at the three special points -/

theorem Wlift_vanishing (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) :
    Work.Asymptotics.SpikeCircle.Wlift ℓ d τ (τ : ℂ) = 0 ∧
    Work.Asymptotics.SpikeCircle.Wlift ℓ d τ ((τ : ℂ) + 1) = 0 ∧
    Work.Asymptotics.SpikeCircle.Wlift ℓ d τ ((τ : ℂ) - 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Wlift, ofComplex_self, AfunFun_self ℓ d hd τ, Tleft_eq_zero_self τ, sub_zero, mul_zero]
  · rw [Wlift, ofComplex_add_one, AfunFun_pos ℓ d hd τ, Tleft_eq_pos τ, sub_self, mul_zero]
  · rw [Wlift, ofComplex_sub_one, AfunFun_neg ℓ d hd τ, Tleft_eq_neg τ, sub_self, mul_zero]

end Work.Asymptotics.SpikeCircle
