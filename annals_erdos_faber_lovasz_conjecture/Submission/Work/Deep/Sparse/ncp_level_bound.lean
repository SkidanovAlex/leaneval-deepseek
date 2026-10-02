import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ncpTailDefs
import Submission.Work.Deep.Sparse.NcpDefs

/-!
# The level bound `4 D 2^J / J! ≤ exp (-T)` for the cutoff level `J = ncpJlev D`

This file proves `Work.Deep.Sparse.ncp_level_bound`: with

* `L = ncpL D = log (D + 2)`,
* `T = ncpT D = L^4/5000 + 2`, and
* `J = ncpJlev D = 19 + 2 (⌈L^4/5000⌉₊ + ⌈L⌉₊ + 50)`,

one has `4 · D · 2^J / J! ≤ exp (-T)`.  In the language of the sparse colouring
concentration (`Submission/Work/Deep/Sparse/NCP_CONCENTRATION_STATUS.md`) this is the assertion
that the contribution of a *fixed* colour class of size `≥ J` to the class-sum statistic is
negligible: `J` is far beyond the scale `T = L^4/5000` at which the exponent of the target
bound settles, and the exponential decay of `2^J/J!` supplies the slack.

## The argument

Write `d = (D : ℝ)`, `twoJ = (2 : ℝ)^J`, `fac = ((J.factorial : ℕ) : ℝ)`.

*Factorial bound.*  For every `n ≥ 3`, `3 · 4^n ≤ 32 · n!` (induction on `n - 3`; equality holds
at `n = 3, 4`).  Equivalently `fac ≥ (3/32) · twoJ^2`, i.e. `(3/32) 2^{2J} ≤ J!`.

*Level bound.*  Since `⌈x⌉₊ ≥ x` for real `x`, one has `J ≥ 119 + 2L + L^4/2500`.

*The multiplicative key inequality.*  It suffices to prove `128 d e^T ≤ 3 · 2^J`: multiplying by
`2^J` and cancelling the factor `32`, this gives

`4 d 2^J e^T ≤ (3/32) 2^{2J} ≤ J!`,

and multiplying the outer inequality `4 d 2^J ≤ J! e^{-T}` by `e^T` gives the goal after dividing
by `J!`.  To prove `128 d e^T ≤ 3 · 2^J` take logarithms.  The right-hand side becomes
`log 3 + J log 2` and the left-hand side `log 128 + L + T = 7 log 2 + L + L^4/5000 + 2`, which is
at most `7 + L + L^4/5000 + 2` since `log 2 ≤ 1` (`log x ≤ x - 1`) and `log D ≤ L` (as
`e^L = D + 2`).  On the other side `J log 2 ≥ J/2 ≥ (119 + 2L + L^4/2500)/2 = 119/2 + L + L^4/5000`
using `log 2 ≥ 1/2`, which follows from `e < 3 < 4` (indeed `e^{1/2} < 2` because
`(e^{1/2})^2 = e < 4 = 2^2`).  The two sides meet: `7 + 2 ≤ 119/2`.

Note the hypothesis `44 ≤ ncpL D` is not needed for the estimate; it is part of the interface
of the concentration proof and is kept for compatibility.
-/

set_option linter.unusedVariables false

namespace Work.Deep.Sparse

/-! ## Elementary bounds for `log 2` -/

private lemma log2_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

private lemma half_le_log2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h2 : (Real.exp ((1 / 2 : ℝ))) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add, show ((1 : ℝ) / 2 + 1 / 2) = 1 from by norm_num]
  have hsq : (Real.exp ((1 / 2 : ℝ))) ^ 2 < (2 : ℝ) ^ 2 := by
    rw [h2]
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
    linarith
  have h3 : Real.exp ((1 / 2 : ℝ)) < 2 := (sq_lt_sq₀ (by positivity) (by positivity)).mp hsq
  have h4 : Real.log (Real.exp ((1 / 2 : ℝ))) ≤ Real.log 2 := Real.log_le_log (Real.exp_pos _) h3.le
  rwa [Real.log_exp] at h4

/-! ## The factorial bound `3 · 4^n ≤ 32 · n!` for `n ≥ 3` -/

private lemma fac_nat_aux : ∀ k : ℕ, (3 : ℕ) * 4 ^ (3 + k) ≤ 32 * (3 + k).factorial := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    have hp : (4 : ℕ) ^ (3 + k + 1) = 4 ^ (3 + k) * 4 := pow_succ _ _
    have hf : (3 + k + 1).factorial = (3 + k + 1) * (3 + k).factorial := Nat.factorial_succ _
    have h4 : (4 : ℕ) ≤ 3 + k + 1 := by omega
    calc (3 : ℕ) * 4 ^ (3 + k + 1)
        = 4 * ((3 : ℕ) * 4 ^ (3 + k)) := by rw [hp]; ring
      _ ≤ 4 * (32 * (3 + k).factorial) := Nat.mul_le_mul_left 4 ih
      _ ≤ (3 + k + 1) * (32 * (3 + k).factorial) := Nat.mul_le_mul_right _ h4
      _ = 32 * (3 + k + 1).factorial := by rw [hf]; ring

private lemma fac_nat {n : ℕ} (hn : 3 ≤ n) : (3 : ℕ) * 4 ^ n ≤ 32 * n.factorial := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 + k := ⟨n - 3, by omega⟩
  exact fac_nat_aux k

/-- The factorial bound in the shape in which it is used: `3 · 2^n · 2^n ≤ 32 · n!` over `ℝ`. -/
private lemma fac_real {n : ℕ} (hn : 3 ≤ n) :
    ((3 : ℝ)) * ((2 : ℝ) ^ n) * ((2 : ℝ) ^ n) ≤ ((32 : ℝ)) * (((n.factorial : ℕ) : ℝ)) := by
  have h : (((3 : ℕ) * 4 ^ n : ℕ) : ℝ) ≤ ((32 * n.factorial : ℕ) : ℝ) := by
    exact_mod_cast fac_nat hn
  push_cast at h
  have hpow : ((4 : ℝ)) ^ n = ((2 : ℝ) ^ n) * ((2 : ℝ) ^ n) := by
    rw [← pow_add, ← two_mul, pow_mul, show ((2 : ℝ) ^ 2) = 4 from by norm_num]
  rw [mul_assoc, ← hpow]
  exact h

/-! ## The logarithmic comparison -/

/-- `log 128 + L + T ≤ log 3 + J log 2` under the level hypothesis `J ≥ 119 + 2L + L^4/2500`. -/
private lemma log_chain {L T : ℝ} {J : ℕ}
    (hT : T = L ^ 4 / 5000 + 2)
    (hJ : ((119 : ℝ)) + 2 * L + L ^ 4 / 2500 ≤ ((J : ℕ) : ℝ)) :
    Real.log ((128 : ℝ)) + L + T ≤ Real.log ((3 : ℝ)) + ((J : ℕ) : ℝ) * Real.log 2 := by
  have hlog128 : Real.log ((128 : ℝ)) = 7 * Real.log 2 := by
    rw [show ((128 : ℝ)) = ((2 : ℝ)) ^ 7 from by norm_num, Real.log_pow]
    push_cast
    ring
  have h7 : 7 * Real.log 2 ≤ 7 := by
    have := mul_le_mul_of_nonneg_left log2_le_one (by norm_num : (0 : ℝ) ≤ 7)
    simpa using this
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hLHS : Real.log ((128 : ℝ)) + L + T ≤ 7 + L + L ^ 4 / 5000 + 2 := by
    rw [hlog128, hT]
    linarith
  have hRHS : ((119 : ℝ)) / 2 + L + L ^ 4 / 5000
      ≤ Real.log ((3 : ℝ)) + ((J : ℕ) : ℝ) * Real.log 2 := by
    have hJ2 : (((119 : ℝ)) + 2 * L + L ^ 4 / 2500) * (1 / 2) ≤ ((J : ℕ) : ℝ) * (1 / 2) :=
      mul_le_mul_of_nonneg_right hJ (by norm_num)
    have hJlog2 : ((J : ℕ) : ℝ) * (1 / 2) ≤ ((J : ℕ) : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left half_le_log2 (Nat.cast_nonneg _)
    have hsplit : (((119 : ℝ)) + 2 * L + L ^ 4 / 2500) * (1 / 2)
        = 119 / 2 + L + L ^ 4 / 5000 := by ring
    rw [hsplit] at hJ2
    linarith
  linarith

/-- From the logarithmic comparison to the exponential key inequality `128 d e^T ≤ 3·2^J`. -/
private lemma key_exp {d L T : ℝ} {J : ℕ}
    (hexpL : Real.exp L = d + 2)
    (hlogle : Real.log ((128 : ℝ)) + L + T ≤ Real.log ((3 : ℝ)) + ((J : ℕ) : ℝ) * Real.log 2) :
    ((128 : ℝ)) * d * Real.exp T ≤ ((3 : ℝ)) * ((2 : ℝ) ^ J) := by
  have h128 : (0 : ℝ) < 128 := by norm_num
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have htwoJpos : (0 : ℝ) < ((2 : ℝ) ^ J) := by positivity
  have h1 : d ≤ Real.exp L := by rw [hexpL]; linarith
  have h1' : ((128 : ℝ)) * d ≤ ((128 : ℝ)) * Real.exp L :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  have h2 : ((128 : ℝ)) * d * Real.exp T ≤ ((128 : ℝ)) * Real.exp L * Real.exp T :=
    mul_le_mul h1' (le_refl _) (Real.exp_nonneg _) (mul_nonneg (by norm_num) (Real.exp_nonneg _))
  have h3 : ((128 : ℝ)) * Real.exp L * Real.exp T = Real.exp (Real.log ((128 : ℝ)) + L + T) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log h128]
  have h4 : Real.exp (Real.log ((128 : ℝ)) + L + T)
      ≤ Real.exp (Real.log ((3 : ℝ)) + ((J : ℕ) : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hlogle
  have h5 : Real.exp (Real.log ((3 : ℝ)) + ((J : ℕ) : ℝ) * Real.log 2)
      = ((3 : ℝ)) * ((2 : ℝ) ^ J) := by
    rw [Real.exp_add, Real.exp_log h3pos, ← Real.log_pow (2 : ℝ) J, Real.exp_log htwoJpos]
  calc ((128 : ℝ)) * d * Real.exp T
      ≤ ((128 : ℝ)) * Real.exp L * Real.exp T := h2
    _ = Real.exp (Real.log ((128 : ℝ)) + L + T) := h3
    _ ≤ Real.exp (Real.log ((3 : ℝ)) + ((J : ℕ) : ℝ) * Real.log 2) := h4
    _ = ((3 : ℝ)) * ((2 : ℝ) ^ J) := h5

/-! ## From the key inequality to the goal -/

/-- Assembly: the factorial bound turns `128 d e^T ≤ 3·2^J` into `4 d 2^J / J! ≤ e^{-T}`. -/
private lemma final_assembly {d T : ℝ} {J : ℕ} (hJ3 : 3 ≤ J)
    (hkey : ((128 : ℝ)) * d * Real.exp T ≤ ((3 : ℝ)) * ((2 : ℝ) ^ J)) :
    4 * d * ((2 : ℝ) ^ J) / (((J.factorial : ℕ) : ℝ)) ≤ Real.exp (-T) := by
  have hfacpos : (0 : ℝ) < ((J.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos J
  have htwoJpos : (0 : ℝ) < ((2 : ℝ) ^ J) := by positivity
  have hfac := fac_real hJ3
  rw [div_le_iff₀ hfacpos]
  have hEqT : Real.exp T * Real.exp (-T) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hone : 4 * d * ((2 : ℝ) ^ J) * Real.exp T * Real.exp (-T) = 4 * d * ((2 : ℝ) ^ J) := by
    rw [mul_assoc, hEqT, mul_one]
  have hA : ((128 : ℝ)) * d * Real.exp T * ((2 : ℝ) ^ J)
      ≤ ((3 : ℝ)) * ((2 : ℝ) ^ J) * ((2 : ℝ) ^ J) :=
    mul_le_mul hkey (le_refl _) htwoJpos.le (by positivity)
  have hB : (32 : ℝ) * (4 * d * ((2 : ℝ) ^ J) * Real.exp T)
      ≤ (32 : ℝ) * (((J.factorial : ℕ) : ℝ)) := by
    have h32 : (32 : ℝ) * (4 * d * ((2 : ℝ) ^ J) * Real.exp T)
        = ((128 : ℝ)) * d * Real.exp T * ((2 : ℝ) ^ J) := by ring
    rw [h32]
    exact hA.trans hfac
  have hmain : 4 * d * ((2 : ℝ) ^ J) * Real.exp T ≤ (((J.factorial : ℕ) : ℝ)) :=
    (mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 32)).mp hB
  calc 4 * d * ((2 : ℝ) ^ J)
      = 4 * d * ((2 : ℝ) ^ J) * Real.exp T * Real.exp (-T) := hone.symm
    _ ≤ (((J.factorial : ℕ) : ℝ)) * Real.exp (-T) :=
        mul_le_mul_of_nonneg_right hmain (Real.exp_nonneg _)
    _ = Real.exp (-T) * (((J.factorial : ℕ) : ℝ)) := by ring

/-! ## The level bound -/

theorem ncp_level_bound (D : ℕ) (hL : 44 ≤ ncpL D) :
    4 * (D : ℝ) * (2 : ℝ) ^ (ncpJlev D) / ((ncpJlev D).factorial : ℝ) ≤ Real.exp (-(ncpT D)) := by
  -- The cutoff level dominates `119 + 2L + L^4/2500`
  have hJge : ((119 : ℝ)) + 2 * ncpL D + (ncpL D) ^ 4 / 2500 ≤ ((ncpJlev D : ℕ) : ℝ) := by
    have hb : (ncpL D) ^ 4 / 5000 ≤ ((⌈(ncpL D) ^ 4 / 5000⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hc : ncpL D ≤ ((⌈ncpL D⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    simp only [ncpJlev]
    push_cast
    have hinner : (ncpL D) ^ 4 / 5000 + ncpL D + 50
        ≤ ((⌈(ncpL D) ^ 4 / 5000⌉₊ : ℕ) : ℝ) + ((⌈ncpL D⌉₊ : ℕ) : ℝ) + 50 := by linarith
    have hmul : 2 * ((ncpL D) ^ 4 / 5000 + ncpL D + 50)
        ≤ 2 * (((⌈(ncpL D) ^ 4 / 5000⌉₊ : ℕ) : ℝ) + ((⌈ncpL D⌉₊ : ℕ) : ℝ) + 50) :=
      mul_le_mul_of_nonneg_left hinner (by norm_num)
    have hsplit : 19 + 2 * ((ncpL D) ^ 4 / 5000 + ncpL D + 50)
        = 119 + 2 * ncpL D + (ncpL D) ^ 4 / 2500 := by ring
    linarith
  have hJ3 : 3 ≤ ncpJlev D := by
    simp only [ncpJlev]
    omega
  have hd2 : (0 : ℝ) < (D : ℝ) + 2 := by positivity
  have hexpL : Real.exp (ncpL D) = (D : ℝ) + 2 := Real.exp_log hd2
  have hT : ncpT D = (ncpL D) ^ 4 / 5000 + 2 := rfl
  have hlogle := log_chain hT hJge
  exact final_assembly hJ3 (key_exp hexpL hlogle)

end Work.Deep.Sparse
