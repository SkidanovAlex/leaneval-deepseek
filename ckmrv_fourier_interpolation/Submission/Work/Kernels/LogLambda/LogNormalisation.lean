/-
# The normalisation of the logarithm: `L_S = Λ_S` on `{im z > 1/2}`

The chosen logarithm `Lfun` of `λ` is the unique holomorphic logarithm of `λ` on `ℍ` which
agrees with the explicit branch `LU = Λ` on `{im z > 1}`.  In `LogExtension` we proved that
this agreement in fact holds on the larger half plane `W = {im z > 1/2}`.

In this file we show that the companion function `Lfun_S(z) = Lfun(-z⁻¹)` (which is a
holomorphic logarithm of `λ_S(z) = λ(-1/z)`) agrees with the explicit branch

  `Λ_S(z) = 4 log θ₀₁(z) - 4 log θ₀₀(z)`

on `W`.  The difference `Lfun_S - Λ_S` is continuous with values in `2πiℤ` on the connected set
`W`, hence constant; the constant is evaluated at the fixed point `z = i` of `z ↦ -z⁻¹`, where
both `LU(i)` and `Λ_S(i)` are real (they are logarithms of the positive real numbers
`λ(i) = λ_S(i) = 1/2`), so the constant vanishes.
-/
import Mathlib
import Submission.Work.Kernels.LogLambda.LogExtension
import Submission.Work.Kernels.LogLambda.LambdaLaws
import Submission.Work.Analysis.ThetaReal.imagAxis_theta_pos

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Complex Set Filter Topology
open scoped Modular

namespace Work.Kernels.LogLambda

lemma lamSC_ne_zero {z : ℂ} (hz : 0 < z.im) : lamSC z ≠ 0 := by
  rw [lamSC_eq_lamC_inv hz]
  exact lamC_ne_zero (im_neg_inv_pos hz)

lemma I_mem_W : (Complex.I : ℂ) ∈ W := by
  simp only [W, Set.mem_ofPred_eq]
  norm_num

lemma continuousOn_neg_inv : ContinuousOn (fun z : ℂ => -z⁻¹) U := by
  have h2 : ContinuousOn (fun z : ℂ => z⁻¹) U :=
    ContinuousOn.inv₀ continuousOn_id (fun z hz => by
      intro h
      rw [h] at hz
      simp only [U, Set.mem_ofPred_eq, Complex.zero_im, lt_self_iff_false] at hz)
  exact h2.neg

/-! ## Reality at the fixed point `i` -/

lemma LU_I_real : ∃ r : ℝ, LU Complex.I = ↑r := by
  obtain ⟨⟨r0, hr0, h0⟩, -, ⟨r2, hr2, h2⟩⟩ :=
    Work.Analysis.ThetaReal.imagAxis_theta_pos 1 (by norm_num)
  simp at h0 h2
  refine ⟨-(Real.pi) + 4 * Real.log 2 + 4 * Real.log r2 - 4 * Real.log r0, ?_⟩
  have hI : (Real.pi : ℂ) * Complex.I * Complex.I = -(Real.pi : ℂ) := by
    rw [mul_assoc, Complex.I_mul_I]; ring
  rw [LU, thetaC10_div_exp, h2, show thetaC00 Complex.I = ↑r0 from h0]
  rw [← Complex.ofReal_log (le_of_lt hr2), ← Complex.ofReal_log (le_of_lt hr0)]
  rw [hI]
  push_cast
  ring

lemma LamS_I_real : ∃ r : ℝ, LamS Complex.I = ↑r := by
  obtain ⟨⟨r0, hr0, h0⟩, ⟨r1, hr1, h1⟩, -⟩ :=
    Work.Analysis.ThetaReal.imagAxis_theta_pos 1 (by norm_num)
  simp at h0 h1
  refine ⟨4 * Real.log r1 - 4 * Real.log r0, ?_⟩
  have h1' : thetaC01 Complex.I = ↑r1 := by simpa [thetaC01] using h1
  have h0' : thetaC00 Complex.I = ↑r0 := h0
  rw [LamS, h1', h0']
  rw [← Complex.ofReal_log (le_of_lt hr1), ← Complex.ofReal_log (le_of_lt hr0)]
  push_cast
  ring

lemma inv_I_eq : -(Complex.I : ℂ)⁻¹ = Complex.I := by
  rw [Complex.inv_I]; ring

lemma Lfun_I_eq_LamS_I : Lfun Complex.I = LamS Complex.I := by
  have hI_U : Complex.I ∈ U := W_subset_U I_mem_W
  have hL : Lfun Complex.I = LU Complex.I := Lfun_eq_LU_on_W Complex.I I_mem_W
  have hdisc : ∃ n : ℤ, Lfun Complex.I - LamS Complex.I = n * (2 * Real.pi * Complex.I) := by
    have h1 : Complex.exp (Lfun Complex.I - LamS Complex.I) = 1 := by
      rw [Complex.exp_sub, Lfun_spec.2.1 Complex.I hI_U, exp_LamS_W Complex.I I_mem_W,
        lamSC_eq_lamC_inv hI_U, inv_I_eq]
      exact div_self (lamC_ne_zero hI_U)
    exact Complex.exp_eq_one_iff.mp h1
  obtain ⟨n, hn⟩ := hdisc
  obtain ⟨r, hr⟩ := LU_I_real
  obtain ⟨r', hr'⟩ := LamS_I_real
  have hreal : Lfun Complex.I - LamS Complex.I = ↑(r - r') := by
    rw [hL, hr, hr']
    push_cast
    ring
  rw [hreal] at hn
  have him : (n : ℝ) * (2 * Real.pi) = 0 := by
    have h := congrArg Complex.im hn
    simpa [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] using h
  have hn_real : (n : ℝ) = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h (by positivity)
  have hn0 : n = 0 := by exact_mod_cast hn_real
  rw [hn0] at hn
  have hz : Lfun Complex.I - LamS Complex.I = 0 := by
    rw [hreal]
    simpa using hn
  exact sub_eq_zero.mp hz

/-! ## The main normalisation statement -/

theorem Lfun_inv_eq_LamS : ∀ z ∈ W, Lfun (-z⁻¹) = LamS z := by
  have hval : ∀ z ∈ W,
      ∃ n : ℤ, (fun w : ℂ => Lfun (-w⁻¹) - LamS w) z = n * (2 * Real.pi * Complex.I) := by
    intro z hz
    have hzU : z ∈ U := W_subset_U hz
    have h1 : Complex.exp ((fun w : ℂ => Lfun (-w⁻¹) - LamS w) z) = 1 := by
      show Complex.exp (Lfun (-z⁻¹) - LamS z) = 1
      rw [Complex.exp_sub, Lfun_spec.2.1 (-z⁻¹) (im_neg_inv_pos hzU), exp_LamS_W z hz,
        lamSC_eq_lamC_inv hzU]
      exact div_self (lamC_ne_zero (im_neg_inv_pos hzU))
    exact Complex.exp_eq_one_iff.mp h1
  have hcont : ContinuousOn (fun w : ℂ => Lfun (-w⁻¹) - LamS w) W :=
    (Lfun_spec.1.continuousOn.comp (continuousOn_neg_inv.mono W_subset_U)
      (fun z hz => im_neg_inv_pos (W_subset_U hz))).sub continuousOn_LamS_W
  have hconst := Work.Analysis.DiscreteValues.eq_const_of_isPreconnected isPreconnected_W hcont
    hval I_mem_W
  intro z hz
  have hzc := hconst z hz
  have h0 : Lfun (-Complex.I⁻¹) - LamS Complex.I = 0 := by
    rw [inv_I_eq, Lfun_I_eq_LamS_I, sub_self]
  rw [h0] at hzc
  exact sub_eq_zero.mp hzc

end Work.Kernels.LogLambda
