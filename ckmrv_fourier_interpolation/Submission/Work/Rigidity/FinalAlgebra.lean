import Mathlib
import Submission.Work.Rigidity.AnnMinusAux
import Submission.Work.Rigidity.MulEqZeroEqZero

noncomputable section

open UpperHalfPlane ModularGroup Matrix Filter
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

/-- A primitive sixth/cube root of unity, `ω = (-1 + √3 i)/2`. -/
noncomputable def w3 : ℂ := (-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2

lemma I_sqrt3_sq : (Complex.I * (Real.sqrt 3 : ℂ)) ^ 2 = -3 := by
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  calc (Complex.I * (Real.sqrt 3 : ℂ)) ^ 2
      = Complex.I ^ 2 * ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 := by ring
    _ = -1 * 3 := by rw [Complex.I_sq, hs]
    _ = -3 := by norm_num

lemma w3_sq : w3 ^ 2 + w3 + 1 = 0 := by
  simp only [w3]
  linear_combination (1 / 4) * I_sqrt3_sq

lemma w3_ne_one : w3 ≠ 1 := by
  intro h
  have hsq := w3_sq
  rw [h] at hsq
  norm_num at hsq

lemma w3_sq_ne_one : w3 ^ 2 ≠ 1 := by
  intro h
  have hsq := w3_sq
  have h2 : w3 = -2 := by linear_combination hsq - h
  rw [h2] at hsq
  norm_num at hsq

lemma w3_cube : w3 ^ 3 = 1 := by
  linear_combination (w3 - 1) * w3_sq

lemma w3_pow_four : w3 ^ 4 = w3 := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, w3_cube, one_mul]

/-- The weight-`k` slash action of `T` is translation: `(F ∣[k] T) τ = F (τ + 1)`. -/
lemma slash_T_eq_shift (k : ℤ) (F : ℍ → ℂ) :
    F ∣[k] ModularGroup.T = fun τ : ℍ => F ((1 : ℝ) +ᵥ τ) := by
  funext τ
  rw [Work.Kernels.slash_apply', Work.Kernels.jFun_apply, UpperHalfPlane.modular_T_smul]
  have h10 : ((ModularGroup.T : SL(2, ℤ)) 1 0 : ℂ) = 0 := by simp [ModularGroup.coe_T]
  have h11 : ((ModularGroup.T : SL(2, ℤ)) 1 1 : ℂ) = 1 := by simp [ModularGroup.coe_T]
  rw [h10, h11, zero_mul, zero_add, _root_.one_zpow, mul_one]

/-- The first difference of a holomorphic function is holomorphic. -/
lemma mdifferentiable_fstDiff {f : ℍ → ℂ} (hf : MDiff f) : MDiff (fstDiff f) := by
  have h1 : fstDiff f = f ∣[(4 : ℤ)] ModularGroup.T - f := by
    funext τ
    rw [fstDiff_apply, slash_T_eq_shift]
    rfl
  rw [h1]
  exact ((hf.slash (4 : ℤ) (Work.Kernels.glOf ModularGroup.T))).sub hf

/-- `fstDiff f (S • τ) = τ⁴ · (fstDiff f ∣[4] S) τ`. -/
lemma fstDiff_S_smul (f : ℍ → ℂ) (τ : ℍ) :
    fstDiff f (ModularGroup.S • τ) = (τ : ℂ) ^ (4 : ℤ) * sdef f τ := by
  have hz : (τ : ℂ) ≠ 0 := coe_ne_zero τ
  have h : (τ : ℂ) ^ (-4 : ℤ) * fstDiff f (ModularGroup.S • τ) = sdef f τ := rfl
  have h4 : (τ : ℂ) ^ (4 : ℤ) * (τ : ℂ) ^ (-4 : ℤ) = 1 := by
    rw [← zpow_add₀ hz]; norm_num
  calc fstDiff f (ModularGroup.S • τ)
      = 1 * fstDiff f (ModularGroup.S • τ) := by ring
    _ = (τ : ℂ) ^ (4 : ℤ) * ((τ : ℂ) ^ (-4 : ℤ) * fstDiff f (ModularGroup.S • τ)) := by
        rw [← mul_assoc, h4, one_mul]
    _ = (τ : ℂ) ^ (4 : ℤ) * sdef f τ := by rw [h]

theorem FinalAlgebra {f : UpperHalfPlane → ℂ} (hP : Work.Kernels.InP f)
    (hT2 : Work.Rigidity.AnnT2 f) (hS : Work.Rigidity.SlashEigen 4 (1 : ℂ) f)
    (hI : Work.Rigidity.I2 f = 0) : Work.Rigidity.fstDiff f = 0 := by
  have hf : MDiff f := hP.1
  have hu : MDiff (fstDiff f) := mdifferentiable_fstDiff hf
  have hH : MDiff (sdef f) := by
    have h : sdef f = fstDiff f ∣[(4 : ℤ)] ModularGroup.S := by
      funext τ
      rw [Work.Kernels.slash_S_apply, sdef, mul_comm]
    rw [h]
    exact hu.slash (4 : ℤ) (Work.Kernels.glOf ModularGroup.S)
  have hFmd : MDiff (fun τ : ℍ => fstDiff f τ - w3 * sdef f τ) := by
    have hc : MDiff (fun _ : ℍ => w3) := mdifferentiable_const (c := w3)
    exact hu.sub (hc.mul hH)
  have hGmd : MDiff (fun τ : ℍ => fstDiff f τ - w3^2 * sdef f τ) := by
    have hc : MDiff (fun _ : ℍ => w3^2) := mdifferentiable_const (c := w3^2)
    exact hu.sub (hc.mul hH)
  have hfac : (fun τ : ℍ => fstDiff f τ - w3 * sdef f τ)
      * (fun τ : ℍ => fstDiff f τ - w3^2 * sdef f τ) = 0 := by
    funext τ
    simp only [Pi.mul_apply, Pi.zero_apply]
    have hτ : (fstDiff f τ)^2 + fstDiff f τ * sdef f τ + (sdef f τ)^2 = 0 := by
      have h := congrFun hI τ
      simpa only [I2, Pi.zero_apply] using h
    have h1 : (fstDiff f τ - w3 * sdef f τ) * (fstDiff f τ - w3^2 * sdef f τ)
        = (fstDiff f τ)^2 + fstDiff f τ * sdef f τ + (sdef f τ)^2 := by
      linear_combination (-(fstDiff f τ * sdef f τ)) * w3_sq
        + ((sdef f τ)^2 * (w3 - 1)) * w3_sq
    rw [h1, hτ]
  rcases (UpperHalfPlane.mul_eq_zero_iff hFmd hGmd).mp hfac with hF0 | hG0
  · funext τ
    have huτ : fstDiff f τ = w3 * sdef f τ := by
      have h := congrFun hF0 τ
      simpa using sub_eq_zero.mp h
    have huSτ : fstDiff f (ModularGroup.S • τ) = w3 * sdef f (ModularGroup.S • τ) := by
      have h := congrFun hF0 (ModularGroup.S • τ)
      simpa using sub_eq_zero.mp h
    have hA : fstDiff f (ModularGroup.S • τ) = (τ : ℂ)^4 * sdef f τ := fstDiff_S_smul f τ
    have hB : sdef f (ModularGroup.S • τ) = (τ : ℂ)^4 * fstDiff f τ := sdef_S_smul f τ
    have hEq : (τ : ℂ)^4 * sdef f τ = w3^2 * ((τ : ℂ)^4 * sdef f τ) := by
      calc (τ : ℂ)^4 * sdef f τ = fstDiff f (ModularGroup.S • τ) := hA.symm
        _ = w3 * sdef f (ModularGroup.S • τ) := huSτ
        _ = w3 * ((τ : ℂ)^4 * fstDiff f τ) := by rw [hB]
        _ = w3 * ((τ : ℂ)^4 * (w3 * sdef f τ)) := by rw [huτ]
        _ = w3^2 * ((τ : ℂ)^4 * sdef f τ) := by ring
    have hz : (τ : ℂ) ≠ 0 := coe_ne_zero τ
    have h4 : (τ : ℂ)^4 ≠ 0 := pow_ne_zero 4 hz
    have hzero : sdef f τ = 0 := by
      have hmm : (1 - w3^2) * ((τ : ℂ)^4 * sdef f τ) = 0 := by
        linear_combination hEq
      rcases mul_eq_zero.mp hmm with h | h
      · exact absurd h (sub_ne_zero.mpr (Ne.symm w3_sq_ne_one))
      · exact (mul_eq_zero.mp h).resolve_left h4
    rw [huτ, hzero, mul_zero]
    rfl
  · funext τ
    have huτ : fstDiff f τ = w3^2 * sdef f τ := by
      have h := congrFun hG0 τ
      simpa using sub_eq_zero.mp h
    have huSτ : fstDiff f (ModularGroup.S • τ) = w3^2 * sdef f (ModularGroup.S • τ) := by
      have h := congrFun hG0 (ModularGroup.S • τ)
      simpa using sub_eq_zero.mp h
    have hA : fstDiff f (ModularGroup.S • τ) = (τ : ℂ)^4 * sdef f τ := fstDiff_S_smul f τ
    have hB : sdef f (ModularGroup.S • τ) = (τ : ℂ)^4 * fstDiff f τ := sdef_S_smul f τ
    have hEq : (τ : ℂ)^4 * sdef f τ = w3 * ((τ : ℂ)^4 * sdef f τ) := by
      calc (τ : ℂ)^4 * sdef f τ = fstDiff f (ModularGroup.S • τ) := hA.symm
        _ = w3^2 * sdef f (ModularGroup.S • τ) := huSτ
        _ = w3^2 * ((τ : ℂ)^4 * fstDiff f τ) := by rw [hB]
        _ = w3^2 * ((τ : ℂ)^4 * (w3^2 * sdef f τ)) := by rw [huτ]
        _ = (w3^2 * w3^2) * ((τ : ℂ)^4 * sdef f τ) := by ring
        _ = w3 * ((τ : ℂ)^4 * sdef f τ) := by
              rw [show w3 ^ 2 * w3 ^ 2 = w3 ^ 4 by ring, w3_pow_four]
    have hz : (τ : ℂ) ≠ 0 := coe_ne_zero τ
    have h4 : (τ : ℂ)^4 ≠ 0 := pow_ne_zero 4 hz
    have hzero : sdef f τ = 0 := by
      have hmm : (1 - w3) * ((τ : ℂ)^4 * sdef f τ) = 0 := by
        linear_combination hEq
      rcases mul_eq_zero.mp hmm with h | h
      · exact absurd h (sub_ne_zero.mpr (Ne.symm w3_ne_one))
      · exact (mul_eq_zero.mp h).resolve_left h4
    rw [huτ, hzero, mul_zero]
    rfl

end Work.Rigidity
