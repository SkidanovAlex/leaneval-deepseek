import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Residues.normalizedDeriv_jInvariantFun

/-!
# The cusp-cleared `j`-invariant `Ψ = q · j`

`Ψ u = q(u) · j(u) = e^{2πi u} j(u)` is the product of the `q`-parameter with the modular
`j`-invariant.  Since `j = 1/q + 744 + O(q)` at the cusp, `Ψ` is holomorphic on `ℍ`, bounded
near every cusp (`Ψ → 1` at `∞`), and satisfies `Ψ = 1 + O(q)`.  The point of `Ψ` is that
`j u = Ψ u / q u`, so the large factor `q u` is separated off, and the *derivative* of `Ψ`
carries the cancellation `D Ψ = E₄² (q/Δ) (E₄ - E₆) = O(q)`.

This file collects the definition and the elementary structural facts (holomorphy, the
derivative identity, and the `T`-periodicity propagated to integer translates) on which the
quantitative estimates are built.
-/

noncomputable section

open UpperHalfPlane
open scoped Manifold

namespace Work.Asymptotics.CuspDecay

open Work.Kernels

/-- `Ψ u = q u · j u`, the cusp-cleared `j`-invariant. -/
noncomputable def Psi (u : UpperHalfPlane) : ℂ := qParamFun u * jInvariantFun u

lemma Psi_apply (u : UpperHalfPlane) : Psi u = qParamFun u * jInvariantFun u := rfl

/-- The complex exponential form of `qParamFun`. -/
lemma qParamFun_eq_exp (u : UpperHalfPlane) :
    qParamFun u = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ)) := rfl

/-- `q` is holomorphic on `ℍ`. -/
lemma mdifferentiable_qParamFun : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) qParamFun := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := fun z : ℂ =>
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)) ?_ ?_
  · have hd : Differentiable ℂ (fun z : ℂ =>
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)) := by
      have h1 : Differentiable ℂ (fun z : ℂ => (2 * (Real.pi : ℂ) * Complex.I) * z) :=
        (differentiable_const (c := (2 * (Real.pi : ℂ) * Complex.I))).mul differentiable_id
      exact h1.cexp
    exact hd.differentiableOn
  · intro z hz
    simp only [Function.comp_apply, qParamFun_eq_exp]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- `j` is holomorphic on `ℍ`. -/
lemma mdifferentiable_jInvariantFun : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jInvariantFun :=
  ((ModularFormClass.holo ModularForm.E₄).pow 3).div
    (CuspFormClass.holo CuspForm.discriminant)
    (fun z => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)

/-- `Ψ` is holomorphic on `ℍ`. -/
lemma mdifferentiable_Psi : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Psi :=
  mdifferentiable_qParamFun.mul mdifferentiable_jInvariantFun

/-- `q` is its own `q`-derivative: `D q = q`. -/
lemma normalizedDeriv_qParamFun :
    Derivative.normalizedDerivOfComplex qParamFun = qParamFun := by
  funext z
  rw [Derivative.normalizedDerivOfComplex]
  have hderiv : HasDerivAt (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w))
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z) * (2 * (Real.pi : ℂ) * Complex.I)) z :=
    by simpa using ((hasDerivAt_id ((z : ℍ) : ℂ)).const_mul
      (2 * (Real.pi : ℂ) * Complex.I)).cexp
  have hopen : IsOpen {w : ℂ | 0 < w.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hev : (qParamFun ∘ ↑UpperHalfPlane.ofComplex) =ᶠ[nhds ((z : ℍ) : ℂ)]
      (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w)) := by
    filter_upwards [hopen.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, qParamFun_eq_exp]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  rw [Filter.EventuallyEq.deriv_eq hev, hderiv.deriv]
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [qParamFun_eq_exp]
  field_simp

/-- **The derivative of `Ψ`.**  `D Ψ = E₄² · (q/Δ) · (E₄ - E₆)`, which is `O(q)` because
`E₄ - E₆ = 744 q + O(q²)`. -/
lemma normalizedDeriv_Psi :
    Derivative.normalizedDerivOfComplex Psi = fun z =>
      E4Fun z ^ 2 * (qParamFun z / DeltaFun z) * (E4Fun z - E6Fun z) := by
  rw [show Psi = qParamFun * jInvariantFun from rfl,
    Derivative.normalizedDerivOfComplex_mul qParamFun jInvariantFun
      mdifferentiable_qParamFun mdifferentiable_jInvariantFun,
    normalizedDeriv_qParamFun, Work.Residues.normalizedDeriv_jInvariantFun]
  funext z
  have hz : DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  simp only [Pi.mul_apply, Pi.add_apply]
  rw [show jInvariantFun z = E4Fun z ^ 3 / DeltaFun z from rfl]
  field_simp
  ring

/-! ## `T`-periodicity, propagated to integer translates -/

/-- A function invariant under `τ ↦ τ + 1` is invariant under every integer translate. -/
lemma vadd_int_of_vadd_one {f : UpperHalfPlane → ℂ} (h : ∀ τ, f ((1 : ℝ) +ᵥ τ) = f τ)
    (n : ℤ) (τ : UpperHalfPlane) : f ((n : ℝ) +ᵥ τ) = f τ := by
  have hnat : ∀ (m : ℕ) (τ : UpperHalfPlane), f ((m : ℝ) +ᵥ τ) = f τ := by
    intro m
    induction m with
    | zero => intro τ; rw [Nat.cast_zero, zero_vadd]
    | succ m ih =>
      intro τ
      rw [show (((m + 1 : ℕ) : ℝ)) +ᵥ τ = (1 : ℝ) +ᵥ ((m : ℝ) +ᵥ τ) by
        rw [show (((m + 1 : ℕ) : ℝ)) = 1 + (m : ℝ) by push_cast; ring, add_vadd]]
      rw [h, ih]
  rcases n with n | n
  · exact hnat n τ
  · have hcast : ((Int.negSucc n : ℤ) : ℝ) = -(((n + 1 : ℕ)) : ℝ) := by push_cast; ring
    rw [hcast]
    have hv : (((n + 1 : ℕ) : ℝ) +ᵥ ((-(((n + 1 : ℕ)) : ℝ)) +ᵥ τ) : UpperHalfPlane) = τ := by
      rw [← add_vadd, add_neg_cancel, zero_vadd]
    have key := hnat (n + 1) ((-(((n + 1 : ℕ)) : ℝ)) +ᵥ τ)
    rw [hv] at key
    exact key.symm

/-- `q` is invariant under integer translations. -/
lemma qParamFun_vadd_int (k : ℤ) (u : UpperHalfPlane) :
    qParamFun ((k : ℝ) +ᵥ u) = qParamFun u := by
  have hcoe : (((k : ℝ) +ᵥ u : UpperHalfPlane) : ℂ) = (u : ℂ) + (k : ℂ) := by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring
  have h2 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) = 1 := by
    have harg : 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      ring
    rw [harg, Complex.exp_int_mul_two_pi_mul_I]
  rw [qParamFun_eq_exp, qParamFun_eq_exp, hcoe,
    show 2 * (Real.pi : ℂ) * Complex.I * ((u : ℂ) + (k : ℂ))
        = 2 * (Real.pi : ℂ) * Complex.I * (u : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) by ring,
    Complex.exp_add, h2, mul_one]

/-- `j` is invariant under integer translations. -/
lemma jInvariantFun_vadd_int (k : ℤ) (u : UpperHalfPlane) :
    jInvariantFun ((k : ℝ) +ᵥ u) = jInvariantFun u :=
  vadd_int_of_vadd_one (fun τ => Work.Kernels.KernelFacts.jInvariantFun_vadd_one τ) k u

/-- `Ψ` is invariant under integer translations. -/
lemma Psi_vadd_int (k : ℤ) (u : UpperHalfPlane) :
    Psi ((k : ℝ) +ᵥ u) = Psi u := by
  simp only [Psi_apply, qParamFun_vadd_int, jInvariantFun_vadd_int]

end Work.Asymptotics.CuspDecay
