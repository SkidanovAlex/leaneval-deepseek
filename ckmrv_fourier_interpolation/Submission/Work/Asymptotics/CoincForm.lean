/-
# The coincidence points of `j` near the contour, in the strip `|Im w - 1/t| ≤ 1/2`

If `j w = j (i t)` and `|Im w - 1/t| ≤ 1/2` with `t < 3/4`, then `w` is one of the points
`n + i/t` (`n ∈ ℤ`): the `SL(2,ℤ)`-orbit points that can reach up to height `1/t` are exactly
those.  This is the orbit classification used to identify the zeros of `w ↦ K^clear(w, i t)` in
the one-zero estimate near the three coincidence points `i/t`, `±1 + i/t`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm

noncomputable section

set_option maxHeartbeats 2000000

open Work.Kernels

/-- The two real equations satisfied by the coefficients of `γ = !![a,b;c,d]` when
`γ • (i t) = w`: `b = w.re * d - w.im * c * t` and `a * t = w.re * c * t + w.im * d`. -/
lemma entries_of_smul_imagAxis_aux {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} {t : ℝ}
    (ht : 0 < t) (w : UpperHalfPlane) (h : γ • Work.Kernels.imagAxis t ht = w) :
    ((γ 0 1 : ℤ) : ℝ) = w.re * ((γ 1 1 : ℤ) : ℝ) - w.im * ((γ 1 0 : ℤ) : ℝ) * t ∧
    ((γ 0 0 : ℤ) : ℝ) * t = w.re * ((γ 1 0 : ℤ) : ℝ) * t + w.im * ((γ 1 1 : ℤ) : ℝ) := by
  have hcoe : ((γ • Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (w : ℂ) := by rw [h]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply] at hcoe
  simp only [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk] at hcoe
  have hcast : ∀ m : ℤ, ((algebraMap ℤ ℝ m : ℂ)) = (m : ℂ) := fun m => by simp
  simp only [hcast] at hcoe
  have hden : ((γ 1 0 : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      mul_zero, sub_zero, zero_mul, add_zero, mul_one] at hre him
    have h11 : γ 1 1 = 0 := by
      have hh : ((γ 1 1 : ℤ) : ℝ) = 0 := by simpa using hre
      exact_mod_cast hh
    have h10 : γ 1 0 = 0 := by
      have ht0 : (t : ℝ) ≠ 0 := ne_of_gt ht
      have hh : ((γ 1 0 : ℤ) : ℝ) * t = 0 := by simpa using him
      have : ((γ 1 0 : ℤ) : ℝ) = 0 := (mul_eq_zero.mp hh).resolve_right ht0
      exact_mod_cast this
    have hdet := γ.2
    rw [Matrix.det_fin_two] at hdet
    rw [h10, h11] at hdet
    norm_num at hdet
  have hmain : ((γ 0 0 : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + ((γ 0 1 : ℤ) : ℂ)
      = (w : ℂ) * (((γ 1 0 : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + ((γ 1 1 : ℤ) : ℂ)) :=
    (div_eq_iff hden).mp hcoe
  have hwcoe : (w : ℂ) = (w.re : ℂ) + (w.im : ℂ) * Complex.I := by
    have hh := Complex.re_add_im (w : ℂ)
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hh
    exact hh.symm
  rw [hwcoe] at hmain
  constructor
  · have h := congrArg Complex.re hmain
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im, Complex.add_im,
      mul_zero, sub_zero, zero_mul, add_zero, mul_one] at h
    push_cast at h
    linarith [h]
  · have h := congrArg Complex.im hmain
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im, Complex.add_im,
      mul_zero, sub_zero, zero_mul, add_zero, mul_one] at h
    push_cast at h
    linarith [h]

/-- **The orbit points of `i t` inside the strip `|Im w - 1/t| ≤ 1/2` are `n + i/t`.** -/
theorem CoincForm (t : ℝ) (ht : 0 < t) (ht34 : t < 3 / 4) (w : UpperHalfPlane)
    (hj : Work.Kernels.jInvariantFun w = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (him : |w.im - t⁻¹| ≤ 1 / 2) :
    ∃ n : ℤ, (w : ℂ) = (n : ℂ) + ((t⁻¹ : ℝ) : ℂ) * Complex.I := by
  obtain ⟨γ₀, hγ₀⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq
    (τ := Work.Kernels.imagAxis t ht) (w := w) hj.symm
  set γ : Matrix.SpecialLinearGroup (Fin 2) ℤ := γ₀⁻¹ with hγdef
  have hγ : γ • Work.Kernels.imagAxis t ht = w := by
    have h1 : γ • (γ₀ • w) = γ • Work.Kernels.imagAxis t ht := by rw [hγ₀]
    rw [← mul_smul] at h1
    rw [hγdef, inv_mul_cancel, one_smul] at h1
    exact h1.symm
  obtain ⟨hE1, hE2⟩ := entries_of_smul_imagAxis_aux ht w hγ
  set x : ℝ := w.re with hx
  set y : ℝ := w.im with hy
  set A : ℝ := ((γ 0 0 : ℤ) : ℝ) with hA
  set B : ℝ := ((γ 0 1 : ℤ) : ℝ) with hB
  set C : ℝ := ((γ 1 0 : ℤ) : ℝ) with hC
  set D : ℝ := ((γ 1 1 : ℤ) : ℝ) with hD
  have hE1' : B = x * D - y * C * t := by
    rw [hB, hx, hD, hy, hC]; exact hE1
  have hE2' : A * t = x * C * t + y * D := by
    rw [hA, hx, hC, hy, hD]; exact hE2
  have hdet : A * D - B * C = 1 := by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    have h' := congrArg (fun m : ℤ => ((m : ℝ))) h
    push_cast at h'
    rw [hA, hB, hC, hD]
    linarith [h']
  -- the imaginary part
  have hupper : y * (C ^ 2 * t ^ 2 + D ^ 2) = t := by
    have e1 : y * (C ^ 2 * t ^ 2 + D ^ 2)
        = D * (x * C * t + y * D) - (C * t) * (x * D - y * C * t) := by ring
    have e2 : D * (x * C * t + y * D) - (C * t) * (x * D - y * C * t) = D * (A * t) - (C * t) * B := by
      rw [← hE2', ← hE1']
    have e3 : D * (A * t) - (C * t) * B = t := by
      have h : D * (A * t) - (C * t) * B = t * (A * D - B * C) := by ring
      rw [h, hdet]; ring
    rw [e1, e2, e3]
  have hDne : C ^ 2 * t ^ 2 + D ^ 2 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hupper
    linarith [ht]
  have hDpos : 0 < C ^ 2 * t ^ 2 + D ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm hDne)
  have hyval : y = t / (C ^ 2 * t ^ 2 + D ^ 2) := by
    rw [eq_div_iff (ne_of_gt hDpos)]; exact hupper
  -- the height bound on the coefficients
  have hheight : t⁻¹ - 1 / 2 ≤ y := by
    have := (abs_le.mp him).1
    rw [hy]; linarith
  have hlow : (2 - t) / (2 * t) ≤ t / (C ^ 2 * t ^ 2 + D ^ 2) := by
    have h3 : t⁻¹ - 1 / 2 = (2 - t) / (2 * t) := by field_simp
    rw [h3] at hheight
    rw [hyval] at hheight
    exact hheight
  have hDle : C ^ 2 * t ^ 2 + D ^ 2 ≤ 2 * t ^ 2 / (2 - t) := by
    have h2t : 0 < 2 - t := by linarith
    have h1 : (2 - t) * (C ^ 2 * t ^ 2 + D ^ 2) ≤ t * (2 * t) := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * t) hDpos] at hlow
      exact hlow
    rw [le_div_iff₀ h2t]
    nlinarith [h1]
  have hsmall : 2 * t ^ 2 / (2 - t) < 1 := by
    have h2t : 0 < 2 - t := by linarith
    rw [div_lt_one h2t]
    nlinarith [ht, ht34]
  have hDsq : D ^ 2 < 1 := by
    have h1 : D ^ 2 ≤ C ^ 2 * t ^ 2 + D ^ 2 := by nlinarith [sq_nonneg C, sq_nonneg t]
    linarith [hDle, hsmall, h1]
  have hDabs : |D| < 1 := by
    rw [← sq_lt_one_iff_abs_lt_one]; exact hDsq
  have hD0 : γ 1 1 = 0 := by
    have h1 : ((γ 1 1 : ℤ) : ℝ) < 1 := by rw [← hD]; exact (abs_lt.mp hDabs).2
    have h2 : -1 < ((γ 1 1 : ℤ) : ℝ) := by rw [← hD]; exact (abs_lt.mp hDabs).1
    have h3 : γ 1 1 < 1 := by exact_mod_cast h1
    have h4 : -1 < γ 1 1 := by exact_mod_cast h2
    omega
  have hD0' : D = 0 := by rw [hD]; simp [hD0]
  have hBC : B * C = -1 := by
    have h := hdet
    rw [hD0'] at h
    linarith [h]
  have hBCint : γ 0 1 * γ 1 0 = -1 := by
    have h1 : B * C = -1 := hBC
    rw [hB, hC] at h1
    have h2 : ((γ 0 1 * γ 1 0 : ℤ) : ℝ) = -1 := by push_cast; exact h1
    exact_mod_cast h2
  have hCpm : γ 1 0 = 1 ∨ γ 1 0 = -1 := by
    have h1 : (-γ 0 1) * γ 1 0 = 1 := by linear_combination -hBCint
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hCsq : C ^ 2 = 1 := by
    rw [hC]
    rcases hCpm with h | h <;> rw [h] <;> norm_num
  -- the real part
  have hxval : x = A * C := by
    have e1 : x * (C ^ 2 * t ^ 2 + D ^ 2) = (C * t) * (x * C * t + y * D) + D * (x * D - y * C * t) := by
      ring
    have e2 : (C * t) * (x * C * t + y * D) + D * (x * D - y * C * t) = (C * t) * (A * t) + D * B := by
      rw [← hE2', ← hE1']
    have e3 : x * (C ^ 2 * t ^ 2 + D ^ 2) = (C * t) * (A * t) + D * B := by rw [e1, e2]
    have h4 : x * t ^ 2 = (A * C) * t ^ 2 := by
      rw [hD0', hCsq] at e3
      nlinarith [e3]
    exact mul_right_cancel₀ (pow_ne_zero 2 (ne_of_gt ht)) h4
  have hyinv : y = t⁻¹ := by
    rw [hyval, hD0', hCsq]
    simp only [one_mul, zero_pow (by norm_num : (2:ℕ) ≠ 0), add_zero]
    field_simp
  have hcoe : (w : ℂ) = (w.re : ℂ) + (w.im : ℂ) * Complex.I := by
    have hh := Complex.re_add_im (w : ℂ)
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hh
    exact hh.symm
  refine ⟨γ 0 0 * γ 1 0, ?_⟩
  rw [hcoe, ← hx, ← hy, hxval, hyinv]
  have hcast : ((A * C : ℝ) : ℂ) = ((γ 0 0 * γ 1 0 : ℤ) : ℂ) := by
    rw [hA, hC]; push_cast; ring
  rw [hcast]

end

end Work.Asymptotics
