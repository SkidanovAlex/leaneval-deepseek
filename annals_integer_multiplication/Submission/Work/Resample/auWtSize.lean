import Mathlib
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auH_err

/-!
# Size of the computed weight value (`Work.Resample.auWt`)

`auWtSize`: the integer value computed by the weight word always fits the uniform size
bound `auSZ p = 10p + 400` of `Work.Resample.auKit`.

The only case needing work is the non-guard branch, where `auZ p α t N ≤ (p+10)·2^{auPrec p}`.
There `auWt` is the truncated quotient of `auH p (−auZ p α t N) (auNstep p)` by
`2^{auPrec p − p}·2α`.  We show `auH p (−z) (auNstep p).natAbs ≤ 2^{5p+121}`: the working value is
the partial sum `Σ_{k ≤ auNstep p} (−x)^k/k!` with `x = z/2^{auPrec p} ∈ [0, p+10]` (the guard),
perturbed by the truncation error of `auH_err`; the triangle inequality bounds this by
`e^{p+10} ≤ 2^{2p+20}` at the working scale `2^{auPrec p} = 2^{3p+100}`.  Division by the
(positive) denominator only decreases the absolute value, and `2^{5p+121} < 2^{10p+398}` gives
the size bound.  In the guard branch `auWt = 0` by definition.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

/-- `e^n ≤ 4^n = 2^{2n}` for natural `n`. -/
theorem au_exp_nat_le_two_pow (n : ℕ) : Real.exp (n : ℝ) ≤ (2:ℝ)^(2*n) := by
  have h1 : Real.exp (n:ℝ) = Real.exp 1 ^ n := by
    simpa using Real.exp_nat_mul 1 n
  rw [h1]
  have h4 : Real.exp 1 ≤ (4:ℝ) := by linarith [Real.exp_one_lt_three]
  calc Real.exp 1 ^ n ≤ (4:ℝ)^n := pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) h4 n
    _ = (2:ℝ)^(2*n) := by rw [show (4:ℝ) = 2^2 by norm_num, ← pow_mul]

/-- The truncated exponential series is dominated by `exp |y|`. -/
theorem au_pot_abs_le_exp (y : ℝ) (i : ℕ) : |Work.Fx.pot y 0 i| ≤ Real.exp |y| := by
  have h1 : Work.Fx.pot y 0 i = ∑ k ∈ Finset.range i, y ^ k / (k.factorial : ℝ) :=
    Work.Fx.expRec.2.2.2.2 y i
  have h2 : Work.Fx.pot |y| 0 i = ∑ k ∈ Finset.range i, |y| ^ k / (k.factorial : ℝ) :=
    Work.Fx.expRec.2.2.2.2 |y| i
  calc |Work.Fx.pot y 0 i|
      = |∑ k ∈ Finset.range i, y ^ k / (k.factorial : ℝ)| := by rw [h1]
    _ ≤ ∑ k ∈ Finset.range i, |y ^ k / (k.factorial : ℝ)| :=
        Finset.abs_sum_le_sum_abs (fun k => y ^ k / (k.factorial : ℝ)) (Finset.range i)
    _ = ∑ k ∈ Finset.range i, |y| ^ k / (k.factorial : ℝ) := by
        apply Finset.sum_congr rfl
        intro k _
        have hfac : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
        rw [abs_div, abs_pow, abs_of_pos hfac]
    _ = Work.Fx.pot |y| 0 i := by rw [h2]
    _ ≤ Real.exp |y| := Work.Fx.expRec.2.2.1 |y| (abs_nonneg y) 0 i

/-- Size of the fixed-point Horner value: if `0 ≤ z ≤ (p+10)·2^{auPrec p}` then
`|auH p (−z) (auNstep p)| ≤ 2^{5p+121}`. -/
theorem auH_abs_le (p : ℕ) (z : ℤ) (hz0 : 0 ≤ z)
    (hzb : z ≤ ((p + 10 : ℕ) : ℤ) * (2:ℤ)^(auPrec p)) :
    (auH p (-z) (auNstep p)).natAbs ≤ 2 ^ (5 * p + 121) := by
  have h2P : (0:ℝ) < (2:ℝ)^(auPrec p) := by positivity
  have hzR : (0:ℝ) ≤ (z:ℝ) := by exact_mod_cast hz0
  have hyabs : |(((-z : ℤ) : ℝ) / (2:ℝ)^(auPrec p))| ≤ ((p+10:ℕ):ℝ) := by
    have hzbR : (z:ℝ) ≤ ((p+10:ℕ):ℝ) * (2:ℝ)^(auPrec p) := by exact_mod_cast hzb
    have hneg : ((-z : ℤ) : ℝ) = -(z:ℝ) := by simp
    rw [abs_div, abs_of_pos h2P, hneg, abs_neg, abs_of_nonneg hzR, div_le_iff₀ h2P]
    exact hzbR
  have hpotabs : |Work.Fx.pot (((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)) 0 (auNstep p + 1)|
      ≤ Real.exp |((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)| := au_pot_abs_le_exp _ _
  have herr := auH_err p (-z) (auNstep p) le_rfl
  rw [Nat.sub_self] at herr
  have hexp2 : Real.exp |((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)| ≤ (2:ℝ)^(2*p+20) := by
    have h1 : Real.exp |((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)| ≤ Real.exp ((p+10:ℕ):ℝ) :=
      Real.exp_le_exp.mpr hyabs
    have h3 := au_exp_nat_le_two_pow (p+10)
    have h4 : 2*(p+10) = 2*p+20 := by omega
    rw [h4] at h3
    linarith
  have hcoef : (2:ℝ)/(2:ℝ)^(auPrec p) ≤ 1 := by
    rw [div_le_one h2P]
    have hP : (1:ℕ) ≤ auPrec p := by simp only [auPrec]; omega
    calc (2:ℝ) = (2:ℝ)^1 := by norm_num
      _ ≤ (2:ℝ)^(auPrec p) := pow_le_pow_right₀ (by norm_num) hP
  have hE : (0:ℝ) ≤ Real.exp |((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)| := le_of_lt (Real.exp_pos _)
  have hmain : |((auH p (-z) (auNstep p) : ℤ) : ℝ) / (2:ℝ)^(auPrec p)| ≤ (2:ℝ)^(2*p+21) := by
    have htri : |((auH p (-z) (auNstep p) : ℤ) : ℝ) / (2:ℝ)^(auPrec p)|
        ≤ |((auH p (-z) (auNstep p) : ℤ) : ℝ) / (2:ℝ)^(auPrec p)
              - Work.Fx.pot (((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)) 0 (auNstep p + 1)|
          + |Work.Fx.pot (((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)) 0 (auNstep p + 1)| := by
      have h := abs_add_le
        (((auH p (-z) (auNstep p) : ℤ) : ℝ) / (2:ℝ)^(auPrec p)
          - Work.Fx.pot (((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)) 0 (auNstep p + 1))
        (Work.Fx.pot (((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)) 0 (auNstep p + 1))
      rwa [sub_add_cancel] at h
    calc |((auH p (-z) (auNstep p) : ℤ) : ℝ) / (2:ℝ)^(auPrec p)|
        ≤ |((auH p (-z) (auNstep p) : ℤ) : ℝ) / (2:ℝ)^(auPrec p)
              - Work.Fx.pot (((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)) 0 (auNstep p + 1)|
          + |Work.Fx.pot (((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)) 0 (auNstep p + 1)| := htri
      _ ≤ (2:ℝ)/(2:ℝ)^(auPrec p) * Real.exp |((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)|
          + Real.exp |((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)| := add_le_add herr hpotabs
      _ ≤ (2:ℝ)^(2*p+21) := by
          have h1 : (2:ℝ)/(2:ℝ)^(auPrec p) * Real.exp |((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)|
              ≤ Real.exp |((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)| :=
            calc (2:ℝ)/(2:ℝ)^(auPrec p) * Real.exp |((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)|
                ≤ 1 * Real.exp |((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)| :=
                  mul_le_mul_of_nonneg_right hcoef hE
              _ = Real.exp |((-z:ℤ):ℝ)/(2:ℝ)^(auPrec p)| := one_mul _
          have h3 : (2:ℝ)^(2*p+21) = 2 * (2:ℝ)^(2*p+20) := by
            rw [show 2*p+21 = 2*p+20+1 by omega, pow_succ]; ring
          rw [h3]
          linarith [hexp2, h1, hE]
  have hmain' : |((auH p (-z) (auNstep p) : ℤ) : ℝ)| ≤ (2:ℝ)^(2*p+21) * (2:ℝ)^(auPrec p) := by
    rw [abs_div, abs_of_pos h2P] at hmain
    exact (div_le_iff₀ h2P).mp hmain
  have hkey : ((auH p (-z) (auNstep p)).natAbs : ℝ) ≤ (2:ℝ)^(5*p+121) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    calc |((auH p (-z) (auNstep p) : ℤ) : ℝ)|
        ≤ (2:ℝ)^(2*p+21) * (2:ℝ)^(auPrec p) := hmain'
      _ = (2:ℝ)^(2*p+21+auPrec p) := by rw [← pow_add]
      _ = (2:ℝ)^(5*p+121) := by
          have hm : 2*p+21+auPrec p = 5*p+121 := by simp only [auPrec]; ring
          rw [hm]
  exact_mod_cast hkey

theorem auWtSize (p α t : ℕ) (N : ℤ) (hN : 0 ≤ N) (hα : 2 ≤ α) (ht : 1 ≤ t) (hp : 100 ≤ p) :
    HvdH.isz (Work.Resample.auWt p α t N) ≤ Work.Resample.auSZ p := by
  rw [auWt]
  split_ifs with hg
  · have hz0 : 0 ≤ auZ p α t N := auZ_nonneg p α t N hN
    have hnat := auH_abs_le p (auZ p α t N) hz0 hg
    have htd : (Int.tdiv (auH p (-(auZ p α t N)) (auNstep p))
          ((2:ℤ)^(auPrec p - p) * (2*(α:ℤ)))).natAbs
        ≤ (auH p (-(auZ p α t N)) (auNstep p)).natAbs := by
      rw [Int.natAbs_tdiv]
      exact Nat.div_le_self _ _
    have hsz : (Int.tdiv (auH p (-(auZ p α t N)) (auNstep p))
          ((2:ℤ)^(auPrec p - p) * (2*(α:ℤ)))).natAbs < 2^(5*p+122) :=
      lt_of_le_of_lt (le_trans htd hnat) (Nat.pow_lt_pow_right one_lt_two (by omega))
    rw [HvdH.isz, auSZ]
    have hsize := Nat.size_le.mpr hsz
    omega
  · rw [HvdH.isz, auSZ]
    rw [Int.natAbs_zero, Nat.size_zero]
    omega

end Work.Resample
