import Mathlib
import Submission.Work.Main.defs

namespace Work.Main.recover

open Work.Main

/-- Real part of the complex number `(a + c·i)/2^n`. -/
lemma re_of_int_pair (a c : ℤ) (n : ℕ) :
    ((((a : ℂ) + (c : ℂ) * Complex.I) / (((2:ℝ)^n : ℝ) : ℂ))).re = (a:ℝ)/(2:ℝ)^n := by
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.normSq_ofReal, Complex.intCast_re, Complex.intCast_im]
  rw [div_eq_mul_inv, mul_comm]
  have : (2:ℝ)^n ≠ 0 := by positivity
  field_simp
  ring

theorem recov_eq {S p b : ℕ} (hb : 2 * b < p) {H : ℤ} {z : ℤ × ℤ}
    (h : ‖(H : ℂ) - (2 : ℂ) ^ (2 * b) * (S : ℂ) * HvdH.fxC p z‖ < 1 / 4) :
    recov S p b z = H := by
  set d := p - 2 * b with hd
  have hd1 : 1 ≤ d := by omega
  have hp_eq : p = 2 * b + d := by omega
  have hd_exp1 : p - 2 * b - 1 = d - 1 := by omega
  have hd_exp2 : p - 2 * b = d := by omega
  set N : ℕ := 2 ^ d with hN
  set M : ℕ := 2 ^ (d - 1) with hM
  have hNM : N = 2 * M := by
    rw [hN, hM, mul_comm, ← pow_succ, Nat.sub_add_cancel hd1]
  have hMz : (2:ℤ)^(d-1) = (M:ℤ) := by rw [hM]; push_cast; ring
  have hNz : (2:ℤ)^d = (N:ℤ) := by rw [hN]; push_cast; ring
  have hNa : (N:ℝ) = (2:ℝ)^d := by rw [hN]; push_cast; ring
  have hNpos_nat : (0:ℕ) < N := by rw [hN]; exact pow_pos (by norm_num : (0:ℕ) < 2) d
  have hNpos : (0:ℤ) < (N:ℤ) := by exact_mod_cast hNpos_nat
  have hMnn : (0:ℝ) ≤ (M:ℝ) := by positivity
  have h4 : (N:ℝ)/4 ≤ (M:ℝ) := by
    rw [hNM]; push_cast; nlinarith
  have hcast : (((2:ℝ)^d : ℝ) : ℂ) = (2:ℂ)^d := by rw [Complex.ofReal_pow]; norm_num
  have hweq : (2:ℂ)^(2*b) * (S:ℂ) * HvdH.fxC p z
      = ((((S * z.1 : ℤ) : ℂ) + (((S * z.2 : ℤ) : ℂ)) * Complex.I)) / (((2:ℝ)^d : ℝ) : ℂ) := by
    have hppow : (2:ℂ)^p = (2:ℂ)^(2*b) * (2:ℂ)^d := by rw [hp_eq, pow_add]
    rw [HvdH.fxC, hppow, hcast]
    field_simp
    push_cast
    ring
  have hrew : ((2:ℂ)^(2*b) * (S:ℂ) * HvdH.fxC p z).re = (S:ℝ)*(z.1:ℝ)/(2:ℝ)^d := by
    rw [hweq, re_of_int_pair]
    push_cast
    ring
  have hbound : |(H:ℝ) - (S:ℝ)*(z.1:ℝ)/(2:ℝ)^d| < 1/4 := by
    have h1 : |((H:ℂ) - (2:ℂ)^(2*b) * (S:ℂ) * HvdH.fxC p z).re|
        ≤ ‖(H:ℂ) - (2:ℂ)^(2*b) * (S:ℂ) * HvdH.fxC p z‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.intCast_re, hrew] at h1
    exact lt_of_le_of_lt h1 h
  have hpos : (0:ℝ) < (2:ℝ)^d := by positivity
  have hmul : |(H:ℝ)*(2:ℝ)^d - (S:ℝ)*(z.1:ℝ)| < (2:ℝ)^d/4 := by
    have h2 : |((H:ℝ) - (S:ℝ)*(z.1:ℝ)/(2:ℝ)^d) * (2:ℝ)^d| < (1/4) * (2:ℝ)^d := by
      rw [abs_mul, abs_of_pos hpos]
      exact mul_lt_mul_of_pos_right hbound hpos
    have e : ((H:ℝ) - (S:ℝ)*(z.1:ℝ)/(2:ℝ)^d) * (2:ℝ)^d = (H:ℝ)*(2:ℝ)^d - (S:ℝ)*(z.1:ℝ) := by
      field_simp
    rw [e] at h2
    rwa [show (1:ℝ)/4 * (2:ℝ)^d = (2:ℝ)^d/4 by ring] at h2
  have hint : |(((H * (N:ℤ) - (S:ℤ)*z.1) : ℤ) : ℝ)| < (N:ℝ)/4 := by
    have e1 : (((H * (N:ℤ) - (S:ℤ)*z.1) : ℤ) : ℝ) = (H:ℝ)*(2:ℝ)^d - (S:ℝ)*(z.1:ℝ) := by
      push_cast; rw [hNa]
    have e2 : (N:ℝ)/4 = (2:ℝ)^d/4 := by rw [hNa]
    rw [e1, e2]; exact hmul
  have hr1 : (((H * (N:ℤ) - (S:ℤ)*z.1) : ℤ) : ℝ) ≤ (M:ℝ) :=
    le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_abs_self _) hint) h4)
  have hr2 : -((M:ℝ)) < (((H * (N:ℤ) - (S:ℤ)*z.1) : ℤ) : ℝ) := by
    have hx : -(((H * (N:ℤ) - (S:ℤ)*z.1) : ℤ) : ℝ) < (M:ℝ) :=
      lt_of_lt_of_le (lt_of_le_of_lt (neg_le_abs _) hint) h4
    linarith
  have hle1 : H * (N:ℤ) ≤ (S:ℤ) * z.1 + (M:ℤ) := by
    have h0 : H * (N:ℤ) - (S:ℤ)*z.1 ≤ (M:ℤ) := by exact_mod_cast hr1
    omega
  have hlt2 : (S:ℤ) * z.1 + (M:ℤ) < H * (N:ℤ) + (N:ℤ) := by
    have h0 : -((M:ℤ)) < H * (N:ℤ) - (S:ℤ)*z.1 := by exact_mod_cast hr2
    have hNMz : (N:ℤ) = 2 * (M:ℤ) := by rw [hNM]; push_cast; ring
    omega
  have hfdiv : ((S:ℤ) * z.1 + (M:ℤ)).fdiv (N:ℤ) = H := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hNpos)]
    apply le_antisymm
    · rw [Int.ediv_le_iff_le_mul hNpos]; linarith
    · rw [Int.le_ediv_iff_mul_le hNpos]; linarith
  rw [recov, hd_exp1, hd_exp2, hMz, hNz]
  exact hfdiv

end Work.Main.recover
