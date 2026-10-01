import Mathlib
import Submission.Work.ZeroDensity.Ingham.zetaAfeDefs
import Submission.Work.ZeroDensity.Ingham.AfeSelf.Defs
import Submission.Work.ZeroDensity.Ingham.chi_eq_gamma_sin
import Submission.Work.ZeroDensity.Ingham.norm_zetaChi_critical

/-!
# Auxiliary vocabulary for the residual of the approximate functional equation

This module collects the definitions shared by `zetaAfeResidual` and the
*resonance sum bound* it rests on: the critical-line point `cls t = 1/2 + it`,
the `k`-th term `afeTerm t k` of the sawtooth–Fourier sum, the sum `afeTsum t`,
and the two truncated Dirichlet sums `afeMain t` (the main sum `Σ_{n ≤ afeNt t} n^{-s}`)
and `afeDual t` (the dual sum `Σ_{m ≤ afeMt t} m^{s-1}`).

It also records the resonance identity `zetaChi s = (s/π)(2π)^s c₀(s)` used to identify the
sawtooth–Fourier sum with the dual truncated Dirichlet sum.
-/

namespace Work.ZeroDensity.Ingham

open scoped BigOperators

noncomputable section

/-- The critical-line point `1/2 + i t`. -/
abbrev cls (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I

@[simp] lemma cls_re (t : ℝ) : (cls t).re = 1 / 2 := by simp [cls]
@[simp] lemma cls_im (t : ℝ) : (cls t).im = t := by simp [cls]

lemma cls_ne_one (t : ℝ) : cls t ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [cls_re] at this
  norm_num at this

lemma cls_re_pos (t : ℝ) : 0 < (cls t).re := by rw [cls_re]; norm_num

lemma cls_re_lt_one (t : ℝ) : (cls t).re < 1 := by rw [cls_re]; norm_num

lemma norm_cls (t : ℝ) : ‖cls t‖ = Real.sqrt (1 / 4 + t ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply, cls_re, cls_im]
  congr 1
  ring

lemma continuous_cls : Continuous cls := by
  unfold cls; fun_prop

/-- The resonance identity `zetaChi s = (s/π)·(2π)^s·c₀(s)`. -/
theorem afe_resonance {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    zetaChi s = (s / (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)) ^ s * afeC0 s := by
  rw [chi_eq_gamma_sin s hs0 hs1]
  unfold afeC0
  ring

/-- The sawtooth factor `(s/π)(2π)^s` of the resonance identity, on the critical line. -/
lemma norm_afeGauge (t : ℝ) :
    ‖(cls t / (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)) ^ (cls t)‖
      = ‖cls t‖ * Real.sqrt (2 * Real.pi) / Real.pi := by
  have hbase : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have hnorm : ‖(2 * (Real.pi : ℂ)) ^ (cls t)‖ = Real.sqrt (2 * Real.pi) := by
    rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), cls_re]
    rw [← Real.sqrt_eq_rpow]
  rw [norm_mul, hnorm, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  ring

/-- `1 ≤ afeNt t` for every `t`. -/
lemma one_le_afeNt (t : ℝ) : 1 ≤ afeNt t := by
  rw [afeNt]; exact Nat.succ_le_succ (Nat.zero_le _)

/-- The `k`-th term of the sawtooth–Fourier sum. -/
def afeTerm (t : ℝ) (k : ℕ) : ℂ :=
  (((k : ℝ) + 1 : ℂ)) ^ (cls t - 1) *
    afeT (cls t) (2 * Real.pi * ((k : ℝ) + 1) * (afeNt t : ℝ))

/-- The sawtooth–Fourier sum `Σ_k (k+1)^{s-1} afeT s (2π(k+1)·N)`, `s = 1/2+it`, `N = afeNt t`. -/
def afeTsum (t : ℝ) : ℂ := ∑' k : ℕ, afeTerm t k

/-- The main truncated Dirichlet sum `Σ_{n ≤ afeNt t} n^{-s}`. -/
def afeMain (t : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 (afeNt t), (n : ℂ) ^ (-(cls t))

/-- The dual truncated Dirichlet sum `Σ_{m ≤ afeMt t} m^{s-1}`. -/
def afeDual (t : ℝ) : ℂ := ∑ m ∈ Finset.Icc 1 (afeMt t), (m : ℂ) ^ (cls t - 1)

lemma afeTsum_apply (t : ℝ) : afeTsum t = ∑' k : ℕ, afeTerm t k := rfl

lemma afeMain_apply (t : ℝ) :
    afeMain t = ∑ n ∈ Finset.Icc 1 (afeNt t), (n : ℂ) ^ (-(cls t)) := rfl

lemma afeDual_apply (t : ℝ) :
    afeDual t = ∑ m ∈ Finset.Icc 1 (afeMt t), (m : ℂ) ^ (cls t - 1) := rfl

/-- Every term of the main sum has modulus at most `1`. -/
lemma norm_cpow_neg_cls_le_one {t : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-(cls t))‖ ≤ 1 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  have h : (-(cls t)).re = -(1 / 2) := by simp [cls]
  rw [h]
  have h2 : ((n : ℝ) ^ (-(1 / 2) : ℝ)) = (((n : ℝ) ^ (1 / 2 : ℝ))⁻¹) :=
    Real.rpow_neg (le_of_lt hn0) (1 / 2)
  rw [h2]
  exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num : (0:ℝ) ≤ 1/2))

/-- Every term of the dual sum has modulus at most `1`. -/
lemma norm_cpow_cls_sub_one_le_one {t : ℝ} {m : ℕ} (hm : 1 ≤ m) :
    ‖(m : ℂ) ^ (cls t - 1)‖ ≤ 1 := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hm0]
  have h : (cls t - 1).re = -(1 / 2) := by norm_num [cls]
  rw [h]
  have h2 : ((m : ℝ) ^ (-(1 / 2) : ℝ)) = (((m : ℝ) ^ (1 / 2 : ℝ))⁻¹) :=
    Real.rpow_neg (le_of_lt hm0) (1 / 2)
  rw [h2]
  exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by exact_mod_cast hm) (by norm_num : (0:ℝ) ≤ 1/2))

lemma norm_afeMain_le (t : ℝ) : ‖afeMain t‖ ≤ (afeNt t : ℝ) := by
  rw [afeMain_apply]
  calc ‖∑ n ∈ Finset.Icc 1 (afeNt t), (n : ℂ) ^ (-(cls t))‖
      ≤ ∑ n ∈ Finset.Icc 1 (afeNt t), ‖(n : ℂ) ^ (-(cls t))‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 (afeNt t), (1 : ℝ) :=
        Finset.sum_le_sum (fun n hn => norm_cpow_neg_cls_le_one (Finset.mem_Icc.mp hn).1)
    _ = (afeNt t : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc]; simp

lemma norm_afeDual_le (t : ℝ) : ‖afeDual t‖ ≤ (afeMt t : ℝ) := by
  rw [afeDual_apply]
  calc ‖∑ m ∈ Finset.Icc 1 (afeMt t), (m : ℂ) ^ (cls t - 1)‖
      ≤ ∑ m ∈ Finset.Icc 1 (afeMt t), ‖(m : ℂ) ^ (cls t - 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 (afeMt t), (1 : ℝ) :=
        Finset.sum_le_sum (fun m hm => norm_cpow_cls_sub_one_le_one (Finset.mem_Icc.mp hm).1)
    _ = (afeMt t : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc]; simp

lemma afeNt_le_self_add_one {t : ℝ} (ht : 1 ≤ t) : (afeNt t : ℝ) ≤ t + 1 := by
  have h1 : (afeNt t : ℝ) ≤ Real.sqrt (t / (2 * Real.pi)) + 1 := by
    rw [afeNt]
    push_cast
    have := Nat.floor_le (Real.sqrt_nonneg (t / (2 * Real.pi)))
    linarith
  have h2 : Real.sqrt (t / (2 * Real.pi)) ≤ Real.sqrt t := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three, ht]
  have h3 : Real.sqrt t ≤ t := by
    rw [Real.sqrt_le_iff]; exact ⟨by linarith, by nlinarith⟩
  linarith

lemma afeMt_le_self {t : ℝ} (ht : 0 ≤ t) : (afeMt t : ℝ) ≤ t := by
  have h1 : (afeMt t : ℝ) ≤ t / (2 * Real.pi * (afeNt t : ℝ)) := by
    rw [afeMt]
    push_cast
    exact Nat.floor_le (by positivity)
  have h2 : (1 : ℝ) ≤ (afeNt t : ℝ) := by exact_mod_cast one_le_afeNt t
  have h3 : (1 : ℝ) ≤ 2 * Real.pi * (afeNt t : ℝ) := by
    nlinarith [Real.pi_gt_three, h2]
  calc (afeMt t : ℝ) ≤ t / (2 * Real.pi * (afeNt t : ℝ)) := h1
    _ ≤ t / 1 := div_le_div_of_nonneg_left ht (by norm_num) h3
    _ = t := by ring

end

end Work.ZeroDensity.Ingham
