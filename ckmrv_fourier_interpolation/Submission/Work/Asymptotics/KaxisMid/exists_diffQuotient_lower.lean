import Mathlib
import Submission.Work.Asymptotics.KaxisMid.Basic
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Residues.ResidueTheorem
import Submission.Work.Residues.KMinusClear_TS
import Submission.Work.Residues.normalizedDeriv_jInvariantFun
import Submission.Work.Analysis.ThetaReal.imagAxis_theta_pos
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.Asymptotics.KaxisMid.exists_lambdaFun_lipschitz

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics.KaxisMid

open Work.Kernels

/-! ## Preliminaries

The strategy of the proof of `exists_diffQuotient_lower` is:

* the point `z₀ = i t₀` (`0 < t₀`, `t₀ ≠ 1`) is not an elliptic point of `SL(2,ℤ)`; concretely
  both `E₄` and `E₆` are non-zero at `z₀`, so `j' = -2πiE₄²E₆/Δ` does not vanish there;
* `j : ℍ → ℂ` is holomorphic, hence has a strict derivative at `z₀`; a strictly differentiable
  map with non-zero derivative strictly expands distances near the point
  (`exists_lipschitz_lower_bound_of_hasStrictDerivAt`), which is the statement.

The two non-vanishing facts are the content of the lemmas below:

* `E₄(i t) ≠ 0`: `E₄ = (U² + V² + W²)/2` with `U = θ₀₀⁴`, `V = θ₁₀⁴`, `W = θ₀₁⁴`, and each of
  `θ₀₀⁴, θ₁₀⁴, θ₀₁⁴` is a *positive real* on the imaginary axis
  (`Work.Analysis.ThetaReal.imagAxis_theta_pos`);
* `E₆(i t) ≠ 0` for `t ≠ 1`: `E₆ = 0` implies `j = 1728`; since `E₆(i) = 0` (automorphy of the
  weight-`6` form `E₆` under `S`, which fixes `i`), `j(i) = 1728`, and the fibres of `j` are the
  `SL(2,ℤ)`-orbits (`jInvariantFun_eq_smul_of_eq`), so `i t₀` would be in the orbit of `i`; but
  the positive imaginary axis meets the orbit of `i` only in `i` itself
  (`eq_one_or_neg_one_or_S_of_smul_imagAxis`), forcing `t₀ = 1`. -/

/-- The dictionary between the honest complex derivative of the lift `f ∘ ofComplex` and the
normalized derivative `D f = (2πi)⁻¹ d/dτ`; this holds for every `f`. -/
private lemma deriv_comp_ofComplex_eq (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    deriv (f ∘ UpperHalfPlane.ofComplex) (z : ℂ)
      = (2 * (Real.pi : ℂ) * Complex.I) * Derivative.normalizedDerivOfComplex f z := by
  rw [Derivative.normalizedDerivOfComplex, mul_inv_cancel_left₀]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

/-! ### Positivity of `θ₀₀⁴`, `θ₁₀⁴`, `θ₀₁⁴` on the imaginary axis -/

private lemma UFun_imagAxis_pos (t : ℝ) (ht : 0 < t) :
    ∃ u : ℝ, 0 < u ∧ UFun (imagAxis t ht) = ↑u := by
  obtain ⟨r, hr, hr'⟩ := Work.Analysis.ThetaReal.jacobiTheta_imag_pos t ht
  refine ⟨r ^ 4, pow_pos hr 4, ?_⟩
  simp only [UFun, theta00Fun]
  rw [show ((imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl, hr']
  push_cast
  ring

private lemma WFun_imagAxis_pos (t : ℝ) (ht : 0 < t) :
    ∃ w : ℝ, 0 < w ∧ WFun (imagAxis t ht) = ↑w := by
  obtain ⟨r, hr, hr'⟩ := Work.Analysis.ThetaReal.jacobiTheta₂_one_half_imag_pos t ht
  refine ⟨r ^ 4, pow_pos hr 4, ?_⟩
  simp only [WFun, theta01Fun]
  rw [show ((imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl, hr']
  push_cast
  ring

private lemma VFun_imagAxis_pos (t : ℝ) (ht : 0 < t) :
    ∃ v : ℝ, 0 < v ∧ VFun (imagAxis t ht) = ↑v := by
  obtain ⟨r, hr, hr'⟩ := Work.Analysis.ThetaReal.jacobiTheta₂_half_arg_imag_pos t ht
  refine ⟨Real.exp (-(Real.pi * t / 4)) ^ 4 * r ^ 4, by positivity, ?_⟩
  simp only [VFun, theta10Fun]
  rw [show ((imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl, hr']
  have hexp : Real.pi * Complex.I * ((t : ℂ) * Complex.I) / 4 = ↑(-(Real.pi * t / 4)) := by
    push_cast
    rw [show (Real.pi : ℂ) * Complex.I * (↑t * Complex.I) / 4
        = (Real.pi : ℂ) * ↑t * (Complex.I * Complex.I) / 4 by ring]
    rw [Complex.I_mul_I]
    ring
  rw [hexp, ← Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow,
    mul_pow]

/-- `E₄` does not vanish on the positive imaginary axis: on it `E₄ = (U² + V² + W²)/2` with
`U, V, W` positive real numbers. -/
private lemma E4Fun_imagAxis_ne_zero (t : ℝ) (ht : 0 < t) :
    E4Fun (imagAxis t ht) ≠ 0 := by
  obtain ⟨u, hu, hU⟩ := UFun_imagAxis_pos t ht
  obtain ⟨v, hv, hV⟩ := VFun_imagAxis_pos t ht
  obtain ⟨w, hw, hW⟩ := WFun_imagAxis_pos t ht
  rw [Work.Residues.KMinusClearTS.E4Fun_eq_theta, hU, hV, hW]
  have hval : ((↑u : ℂ) ^ 2 + (↑v : ℂ) ^ 2 + (↑w : ℂ) ^ 2) / 2
      = ((u ^ 2 + v ^ 2 + w ^ 2) / 2 : ℝ) := by push_cast; ring
  rw [hval]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))

/-! ### `E₆(i) = 0` and `E₆ = 0 ⟹ j = 1728` -/

/-- `S` fixes the point `i` of `ℍ`. -/
private lemma S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_I]
  rw [inv_neg, Complex.inv_I]
  ring

/-- `E₆(i) = 0`: the weight-`6` form `E₆` transforms by `z^6` under `S`, and `S` fixes `i`,
so `E₆(i) = i^6 E₆(i) = -E₆(i)`. -/
private lemma E6Fun_I_eq_zero : E6Fun UpperHalfPlane.I = 0 := by
  have h := Work.Residues.E6Fun_S_smul UpperHalfPlane.I
  rw [S_smul_I] at h
  have hI6 : (UpperHalfPlane.I : ℂ) ^ 6 = -1 := by
    rw [UpperHalfPlane.coe_I, show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Complex.I_sq]
    norm_num
  rw [hI6, neg_one_mul] at h
  have h2 : (2 : ℂ) * E6Fun UpperHalfPlane.I = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- If `E₆` vanishes at `z` then `j(z) = 1728`: from `Δ·j = E₄³` and `1728Δ = E₄³ - E₆²`. -/
private lemma jInvariantFun_eq_1728_of_E6Fun_eq_zero {z : UpperHalfPlane} (h : E6Fun z = 0) :
    jInvariantFun z = 1728 := by
  have h1 : DeltaFun z * jInvariantFun z = E4Fun z ^ 3 :=
    ClassicalFacts.DeltaFun_mul_jInvariantFun z
  have h2 : (1728 : ℂ) * DeltaFun z = E4Fun z ^ 3 - E6Fun z ^ 2 :=
    Work.Residues.KMinusClearTS.disc_eq z
  have h3 : E4Fun z ^ 3 = 1728 * DeltaFun z := by rw [h2, h]; ring
  have hD : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  rw [h3] at h1
  exact mul_left_cancel₀ hD (by rw [h1]; ring)

/-- **The difference quotient of `j` is bounded below near the diagonal at contour points away
from `i`.**  For `z₀ = i t₀` with `t₀ ∈ [ε,1]`, `t₀ ≠ 1`, the point `z₀` is not an elliptic point
(neither the `i`-orbit nor the `ρ`-orbit meets the open imaginary axis away from `i`), so `j'` does
not vanish there and `‖j τ - j z‖` dominates `‖τ - z‖` in a neighbourhood of the diagonal. -/
theorem exists_diffQuotient_lower {ε t₀ : ℝ} (hε : 0 < ε) (ht : ε ≤ t₀) (ht1 : t₀ ≤ 1)
    (hne : t₀ ≠ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, 0 < c ∧ ∀ τ z : UpperHalfPlane,
      ‖(τ : ℂ) - ((Work.Kernels.imagAxis t₀ (lt_of_lt_of_le hε ht)) : ℂ)‖ < ρ →
      ‖(z : ℂ) - ((Work.Kernels.imagAxis t₀ (lt_of_lt_of_le hε ht)) : ℂ)‖ < ρ →
      c * ‖(τ : ℂ) - (z : ℂ)‖ ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by
  have ht0 : 0 < t₀ := lt_of_lt_of_le hε ht
  set z₀ : UpperHalfPlane := Work.Kernels.imagAxis t₀ ht0 with hz₀
  -- non-vanishing of `E₄` and `E₆` at `z₀ = i t₀`
  have hE4 : E4Fun z₀ ≠ 0 := E4Fun_imagAxis_ne_zero t₀ ht0
  have hE6 : E6Fun z₀ ≠ 0 := by
    intro hE6zero
    have hjz : jInvariantFun z₀ = 1728 := jInvariantFun_eq_1728_of_E6Fun_eq_zero hE6zero
    have hjI : jInvariantFun UpperHalfPlane.I = 1728 :=
      jInvariantFun_eq_1728_of_E6Fun_eq_zero E6Fun_I_eq_zero
    have heq : jInvariantFun z₀ = jInvariantFun UpperHalfPlane.I := by rw [hjz, hjI]
    obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq heq
    have hI : UpperHalfPlane.I = Work.Kernels.imagAxis 1 (by norm_num : (0 : ℝ) < 1) := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_I, imagAxis, UpperHalfPlane.coe_mk]
      norm_num
    have hγ' : γ • Work.Kernels.imagAxis 1 (by norm_num : (0 : ℝ) < 1)
        = Work.Kernels.imagAxis t₀ ht0 := by
      rw [← hI, ← hz₀]
      exact hγ
    have key : Work.Kernels.imagAxis 1 (by norm_num : (0 : ℝ) < 1)
        = Work.Kernels.imagAxis t₀ ht0 := by
      rcases eq_one_or_neg_one_or_S_of_smul_imagAxis (by norm_num : (0 : ℝ) < 1) ht0 hγ' with
        h1 | h1 | h1 | h1
      · rw [h1, one_smul] at hγ'; exact hγ'
      · rw [h1, ModularGroup.SL_neg_smul, one_smul] at hγ'; exact hγ'
      · rw [h1, ← hI, S_smul_I, hI] at hγ'; exact hγ'
      · rw [h1, ModularGroup.SL_neg_smul, ← hI, S_smul_I, hI] at hγ'; exact hγ'
    have h2 := congrArg UpperHalfPlane.im key
    have h3 : (1 : ℝ) = t₀ := by simpa [imagAxis] using h2
    exact hne h3.symm
  -- the strict derivative of the lift of `j`
  have hMD : MDiff Work.Kernels.jInvariantFun :=
    ((ModularFormClass.holo ModularForm.E₄).pow 3).div
      (CuspFormClass.holo CuspForm.discriminant)
      (fun z => ClassicalFacts.DeltaFun_ne_zero z)
  have hAnaOn : AnalyticOnNhd ℂ
      (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hMD).analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hAna : AnalyticAt ℂ (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) (z₀ : ℂ) :=
    hAnaOn (z₀ : ℂ) (by simpa using z₀.im_pos)
  have hderiv_ne :
      deriv (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) (z₀ : ℂ) ≠ 0 := by
    rw [deriv_comp_ofComplex_eq, Work.Residues.normalizedDeriv_jInvariantFun]
    refine mul_ne_zero ?_ ?_
    · exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    · simp only
      exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hE4) hE6))
        (ClassicalFacts.DeltaFun_ne_zero z₀)
  obtain ⟨ρ, hρ, c, hc, h⟩ :=
    exists_lipschitz_lower_bound_of_hasStrictDerivAt hAna.hasStrictDerivAt hderiv_ne
  refine ⟨ρ, hρ, c, hc, fun τ z hτ hz => ?_⟩
  have h1 := h (τ : ℂ) (z : ℂ) hτ hz
  simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using h1

end Work.Asymptotics.KaxisMid
