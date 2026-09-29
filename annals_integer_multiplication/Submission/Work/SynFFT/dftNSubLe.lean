import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.yMulFacts

/-!
# Lipschitz continuity of the length-`t` synthetic transform `dftN` in the sup norm

`dftN r t sgn a j c = (1/t) Σ_{k<t} (y^{sgn·(2r/t)·j·k} · a_k)_c` is the coefficient `c` of the
`j`-th entry of the one-dimensional synthetic transform of the array `a`.  Each term is a
`yMul`-image of `a k`, and `yMul r e` acts on `ℂ[y]/(y^r+1)` by a signed permutation of the
coefficients (`Work.SynFFT.yMulFacts`), hence it is an isometry for the sup norm on `Fin r → ℂ`.

Consequently, if two arrays agree coefficientwise up to `δ` on the first `t` positions, so do
their transforms.  This is the "`dftN` is `1`-Lipschitz" step used to propagate the error
bounds of the FFT program through the axis transforms.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

/-- Multiplication by `y^e` is additive in the coefficient vector. -/
lemma dftN_yMul_sub (r : ℕ) (hr : 0 < r) (e : ℤ) (a b : Fin r → ℂ) :
    yMul r e (a - b) = yMul r e a - yMul r e b := by
  have hadd : yMul r e (a - b) + yMul r e b = yMul r e a := by
    rw [← (yMulFacts r hr).2.2.1 e (a - b) b, sub_add_cancel]
  rw [← hadd]
  abel

/-- Each coordinate of `yMul r e v` is `±` a coordinate of `v`; hence if all coordinates of `v`
are bounded by `δ`, so is the coordinate `c` of `yMul r e v`. -/
lemma dftN_yMul_apply_le (r : ℕ) (hr : 0 < r) (e : ℤ) (δ : ℝ) (v : Fin r → ℂ)
    (hv : ∀ c, ‖v c‖ ≤ δ) (c : Fin r) : ‖yMul r e v c‖ ≤ δ := by
  obtain ⟨s, j, hs, hsj⟩ := (yMulFacts r hr).2.2.2.2.1 e v c
  rw [hsj, norm_mul]
  rcases hs with h1 | h1
  · rw [h1]; simp only [norm_one, one_mul]; exact hv j
  · rw [h1]; simp only [norm_neg, norm_one, one_mul]; exact hv j

theorem dftNSubLe (r t : ℕ) (ht : 0 < t) (sgn : ℤ) (a b : Work.SynFFT.Arr r) (δ : ℝ)
    (h : ∀ k, k < t → ∀ c : Fin r, ‖a k c - b k c‖ ≤ δ) :
    ∀ (j : ℕ) (c : Fin r),
      ‖Work.SynFFT.dftN r t sgn a j c - Work.SynFFT.dftN r t sgn b j c‖ ≤ δ := by
  intro j c
  by_cases hr : r = 0
  · subst hr; exact Fin.elim0 c
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  simp only [dftN]
  set Sa : ℂ := ∑ k ∈ Finset.range t, yMul r (sgn * ((2 * r / t * j * k : ℕ) : ℤ)) (a k) c with hSa
  set Sb : ℂ := ∑ k ∈ Finset.range t, yMul r (sgn * ((2 * r / t * j * k : ℕ) : ℤ)) (b k) c with hSb
  have hEq : Sa - Sb = ∑ k ∈ Finset.range t,
      yMul r (sgn * ((2 * r / t * j * k : ℕ) : ℤ)) (a k - b k) c := by
    rw [hSa, hSb, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [dftN_yMul_sub r hrpos (sgn * ((2 * r / t * j * k : ℕ) : ℤ)) (a k) (b k)]
    rfl
  have hnorm : ‖Sa - Sb‖ ≤ (t : ℝ) * δ := by
    rw [hEq]
    calc ‖∑ k ∈ Finset.range t, yMul r (sgn * ((2 * r / t * j * k : ℕ) : ℤ)) (a k - b k) c‖
        ≤ ∑ k ∈ Finset.range t, ‖yMul r (sgn * ((2 * r / t * j * k : ℕ) : ℤ)) (a k - b k) c‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range t, δ := by
          apply Finset.sum_le_sum
          intro k hk
          exact dftN_yMul_apply_le r hrpos _ δ (a k - b k)
            (fun c' => h k (Finset.mem_range.mp hk) c') c
      _ = (t : ℝ) * δ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hine : ‖(1 : ℂ) / (t : ℂ)‖ = (t : ℝ)⁻¹ := by
    rw [one_div, norm_inv, Complex.norm_natCast]
  calc ‖1 / (t : ℂ) * Sa - 1 / (t : ℂ) * Sb‖
      = ‖1 / (t : ℂ) * (Sa - Sb)‖ := by rw [mul_sub]
    _ = ‖1 / (t : ℂ)‖ * ‖Sa - Sb‖ := norm_mul _ _
    _ = (t : ℝ)⁻¹ * ‖Sa - Sb‖ := by rw [hine]
    _ ≤ (t : ℝ)⁻¹ * ((t : ℝ) * δ) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = δ := by
        have hne : (t : ℝ) ≠ 0 := by positivity
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end Work.SynFFT
