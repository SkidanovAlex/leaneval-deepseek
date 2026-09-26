/-
# `j` expands distances near a non-elliptic point of the positive imaginary axis

This file records the local lower bound on `‖j τ - j z‖` needed by the CKMRV asymptotics on
the contour `{i t : t > 0}` (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196
(2022)), at every point `i t₀` of the positive imaginary axis except `i` itself:

  `∃ ρ c > 0, ∀ τ z ∈ ℍ, ‖τ - i t₀‖ < ρ → ‖z - i t₀‖ < ρ → c ‖τ - z‖ ≤ ‖j τ - j z‖`.

## Why the statement holds

Let `z₀ = i t₀` with `t₀ > 0`, `t₀ ≠ 1`.  The modular `j`-invariant is holomorphic on `ℍ`
and (the paper's (2.7))

  `j' = -2πi E₄² E₆ / Δ`,

so `j'` vanishes at `z₀` exactly when `E₄(z₀) = 0` or `E₆(z₀) = 0`, because `Δ` is nowhere
zero.  Both are excluded on the positive imaginary axis away from `i`:

* `E₄` does not vanish anywhere on the positive imaginary axis: on it
  `E₄ = (U² + V² + W²)/2` with `U = θ₀₀⁴`, `V = θ₁₀⁴`, `W = θ₀₁⁴` three *positive real*
  numbers (`Work.Analysis.ThetaReal.imagAxis_theta_pos`, proved from the theta series and
  Jacobi's imaginary transformation).
* `E₆(z) = 0` forces `j z = 1728`: from `jΔ = E₄³` and `1728Δ = E₄³ - E₆²`.  And `j = 1728`
  exactly on the `SL(2,ℤ)`-orbit of `i` (`Work.Asymptotics.jInvariantFun_eq_smul_of_eq`),
  while the positive imaginary axis meets that orbit only in `i` itself
  (`Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis`); so `E₆(i t₀) ≠ 0` for
  `t₀ ≠ 1`.

Hence `j'` is non-zero at `z₀`.  As `j` is holomorphic, hence strictly differentiable, at
`z₀`, the reverse triangle inequality with the strictly differentiable expansion of `j`
(the uniform `o(τ - z)` remainder of
`Work.Asymptotics.MiddleRange.exists_lipschitz_lower_bound_of_hasStrictDerivAt`) gives the
asserted local lower bound with `c = ‖j'(z₀)‖/2`.

## Main result

* `Work.Asymptotics.jDiff_lower_imagAxis`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Residues.ResidueTheorem
import Submission.Work.Residues.KMinusClear_TS
import Submission.Work.Residues.normalizedDeriv_jInvariantFun
import Submission.Work.Analysis.ThetaReal.imagAxis_theta_pos
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.Asymptotics.MiddleRange.exists_lambdaFun_lipschitz

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-! ## `E₄` does not vanish on the positive imaginary axis -/

/-- On the positive imaginary axis, `U = θ₀₀⁴` is a positive real number. -/
private lemma UFun_imagAxis_pos (t : ℝ) (ht : 0 < t) :
    ∃ u : ℝ, 0 < u ∧ UFun (imagAxis t ht) = ↑u := by
  obtain ⟨r, hr, hr'⟩ := Work.Analysis.ThetaReal.jacobiTheta_imag_pos t ht
  refine ⟨r ^ 4, pow_pos hr 4, ?_⟩
  simp only [UFun, theta00Fun]
  rw [show ((imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl, hr']
  push_cast
  ring

/-- On the positive imaginary axis, `W = θ₀₁⁴` is a positive real number. -/
private lemma WFun_imagAxis_pos (t : ℝ) (ht : 0 < t) :
    ∃ w : ℝ, 0 < w ∧ WFun (imagAxis t ht) = ↑w := by
  obtain ⟨r, hr, hr'⟩ := Work.Analysis.ThetaReal.jacobiTheta₂_one_half_imag_pos t ht
  refine ⟨r ^ 4, pow_pos hr 4, ?_⟩
  simp only [WFun, theta01Fun]
  rw [show ((imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl, hr']
  push_cast
  ring

/-- On the positive imaginary axis, `V = θ₁₀⁴` is a positive real number. -/
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

/-! ## `E₆(i t₀) ≠ 0` for `t₀ ≠ 1` -/

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

/-- `E₆` does not vanish at `i t₀` for `t₀ > 0`, `t₀ ≠ 1`: `E₆ = 0` would force `j = 1728`,
and the `SL(2,ℤ)`-orbit of `i` (the fibre of `j` over `1728`) meets the positive imaginary
axis only at `i = i·1`. -/
private lemma E6Fun_imagAxis_ne_zero (t : ℝ) (ht : 0 < t) (hne : t ≠ 1) :
    E6Fun (imagAxis t ht) ≠ 0 := by
  intro hE6zero
  have hjz : jInvariantFun (imagAxis t ht) = 1728 :=
    jInvariantFun_eq_1728_of_E6Fun_eq_zero hE6zero
  have hjI : jInvariantFun UpperHalfPlane.I = 1728 :=
    jInvariantFun_eq_1728_of_E6Fun_eq_zero E6Fun_I_eq_zero
  have heq : jInvariantFun (imagAxis t ht) = jInvariantFun UpperHalfPlane.I := by rw [hjz, hjI]
  obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq heq
  have hI : UpperHalfPlane.I = imagAxis 1 (by norm_num : (0 : ℝ) < 1) := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_I, imagAxis, UpperHalfPlane.coe_mk]
    norm_num
  have hγ' : γ • imagAxis 1 (by norm_num : (0 : ℝ) < 1) = imagAxis t ht := by
    rw [← hI]
    exact hγ
  have key : imagAxis 1 (by norm_num : (0 : ℝ) < 1) = imagAxis t ht := by
    rcases eq_one_or_neg_one_or_S_of_smul_imagAxis (by norm_num : (0 : ℝ) < 1) ht hγ' with
      h1 | h1 | h1 | h1
    · rw [h1, one_smul] at hγ'; exact hγ'
    · rw [h1, ModularGroup.SL_neg_smul, one_smul] at hγ'; exact hγ'
    · rw [h1, ← hI, S_smul_I, hI] at hγ'; exact hγ'
    · rw [h1, ModularGroup.SL_neg_smul, ← hI, S_smul_I, hI] at hγ'; exact hγ'
  have h2 := congrArg UpperHalfPlane.im key
  have h3 : (1 : ℝ) = t := by simpa [imagAxis] using h2
  exact hne h3.symm

/-! ## The derivative of `j` at a non-elliptic contour point -/

/-- The dictionary between the honest complex derivative of the lift `f ∘ ofComplex` and the
normalized derivative `D f = (2πi)⁻¹ d/dτ`; this holds for every `f`. -/
private lemma deriv_comp_ofComplex_eq (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    deriv (f ∘ UpperHalfPlane.ofComplex) (z : ℂ)
      = (2 * (Real.pi : ℂ) * Complex.I) * Derivative.normalizedDerivOfComplex f z := by
  rw [Derivative.normalizedDerivOfComplex, mul_inv_cancel_left₀]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

/-- **The difference quotient of `j` is bounded below near the diagonal at every non-elliptic
point of the positive imaginary axis.**  For `z₀ = i t₀` with `t₀ > 0`, `t₀ ≠ 1`, `j'` does not
vanish at `z₀` (`E₄` and `E₆` do not), so the strictly differentiable holomorphic `j` expands
Euclidean distances near `z₀`. -/
theorem jDiff_lower_imagAxis {t₀ : ℝ} (ht₀ : 0 < t₀) (hne : t₀ ≠ 1) :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ τ z : UpperHalfPlane,
      ‖(τ : ℂ) - ((Work.Kernels.imagAxis t₀ ht₀ : UpperHalfPlane) : ℂ)‖ < ρ →
      ‖(z : ℂ) - ((Work.Kernels.imagAxis t₀ ht₀ : UpperHalfPlane) : ℂ)‖ < ρ →
      c * ‖(τ : ℂ) - (z : ℂ)‖ ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by
  set z₀ : UpperHalfPlane := Work.Kernels.imagAxis t₀ ht₀ with hz₀
  -- `j' = -2πiE₄²E₆/Δ` does not vanish at `z₀`
  have hE4 : E4Fun z₀ ≠ 0 := E4Fun_imagAxis_ne_zero t₀ ht₀
  have hE6 : E6Fun z₀ ≠ 0 := E6Fun_imagAxis_ne_zero t₀ ht₀ hne
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
  -- the strictly differentiable map `j` expands distances near `z₀`
  obtain ⟨ρ, hρ, c, hc, h⟩ :=
    MiddleRange.exists_lipschitz_lower_bound_of_hasStrictDerivAt hAna.hasStrictDerivAt hderiv_ne
  refine ⟨ρ, c, hρ, hc, fun τ z hτ hz => ?_⟩
  have h1 := h (τ : ℂ) (z : ℂ) hτ hz
  simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using h1

end Work.Asymptotics
