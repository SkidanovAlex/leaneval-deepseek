import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For `n ≥ 2` the Baker–Wüstholz constant grows fast enough to absorb one factor
`64 n (n+1) d` when the rank is raised from `n-1` to `n` and the degree is kept:

`64 n (n+1) d · C(n-1,d) ≤ C(n,d)`.

The point is that `C(n,d)/C(n-1,d) = 32 (n+1) d · (n^{n+1}/(n-1)^n) · (log(2nd)/log(2(n-1)d))`,
that `n^{n+1}/(n-1)^n = n (n/(n-1))^n ≥ 2n` (Bernoulli), and that `log(2nd) ≥ log(2(n-1)d) > 0`. -/
theorem elim_Cstep {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) :
    64 * (n : ℝ) * ((n : ℝ) + 1) * (d : ℝ) * BakerWustholz.C (n - 1) d ≤ BakerWustholz.C n d := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : n - 1 + 2 = n + 1 := by omega
  have hn3 : n - 1 + 1 = n := by omega
  -- The only genuinely multiplicative input: `2 (n-1)^n ≤ n^n`, i.e. `(1 + 1/(n-1))^n ≥ 2`
  -- (Bernoulli, exponent `n ≥ n-1`).
  have hkey : 2 * (((n - 1 : ℕ) : ℝ)) ^ n ≤ (n : ℝ) ^ n := by
    have hN_eq : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
      have h := Nat.cast_sub (R := ℝ) hn1
      push_cast at h
      linarith
    set m : ℝ := ((n - 1 : ℕ) : ℝ) with hmdef
    have hm1 : (1 : ℝ) ≤ m := by
      rw [hmdef]; exact_mod_cast (by omega : 1 ≤ n - 1)
    have hmpos : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm1
    have hmeq : (n : ℝ) = m + 1 := by rw [hN_eq, hmdef]
    have hmle : m ≤ (n : ℝ) := by rw [hmeq]; linarith
    have hbern : 1 + (n : ℝ) * (1 / m) ≤ (1 + 1 / m) ^ n := by
      apply one_add_mul_le_pow
      have : (0:ℝ) < 1/m := by positivity
      linarith
    have hge : (2 : ℝ) ≤ 1 + (n : ℝ) * (1 / m) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) / m := by
        rw [one_le_div hmpos]; exact hmle
      have h2 : (n : ℝ) * (1 / m) = (n : ℝ) / m := by rw [mul_one_div]
      linarith [h1, h2]
    have hstep : 2 * m ^ n ≤ (1 + 1 / m) ^ n * m ^ n := by
      calc 2 * m ^ n ≤ (1 + (n : ℝ) * (1 / m)) * m ^ n :=
            mul_le_mul_of_nonneg_right hge (pow_nonneg hmpos.le n)
        _ ≤ (1 + 1 / m) ^ n * m ^ n :=
            mul_le_mul_of_nonneg_right hbern (pow_nonneg hmpos.le n)
    have hpow : (1 + 1 / m) ^ n * m ^ n = (m + 1) ^ n := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [hmeq]
    linarith [hstep, hpow]
  -- Monotonicity and positivity of the logarithm factors.
  have hMleN : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.sub_le n 1)
  have hlogargpos : (1:ℝ) < 2 * ((n - 1 : ℕ) : ℝ) * (d : ℝ) := by
    have hm : (1:ℝ) ≤ ((n-1:ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ n - 1)
    have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    nlinarith
  have hlogarg0 : (0:ℝ) < 2 * ((n - 1 : ℕ) : ℝ) * (d : ℝ) := by linarith
  have hZpos : 0 < Real.log (2 * ((n - 1 : ℕ) : ℝ) * (d : ℝ)) := Real.log_pos hlogargpos
  have hlogarg : 2 * ((n - 1 : ℕ) : ℝ) * (d : ℝ) ≤ 2 * (n : ℝ) * (d : ℝ) := by
    have hd0 : (0:ℝ) ≤ (d:ℝ) := by positivity
    nlinarith [hMleN, hd0]
  have hlog : Real.log (2 * ((n - 1 : ℕ) : ℝ) * (d : ℝ)) ≤ Real.log (2 * (n : ℝ) * (d : ℝ)) :=
    Real.log_le_log hlogarg0 hlogarg
  have hcore : 2 * (((n - 1 : ℕ) : ℝ)) ^ n * Real.log (2 * ((n - 1 : ℕ) : ℝ) * (d : ℝ))
      ≤ (n : ℝ) ^ n * Real.log (2 * (n : ℝ) * (d : ℝ)) :=
    mul_le_mul hkey hlog (le_of_lt hZpos) (pow_nonneg (by positivity) n)
  -- Unfold the two constants.
  have hC1 : BakerWustholz.C (n - 1) d
      = 18 * ((n.factorial : ℕ) : ℝ) * (((n-1:ℕ):ℝ))^n * (32*(d:ℝ))^(n+1)
        * Real.log (2 * ((n-1:ℕ):ℝ) * (d:ℝ)) := by
    unfold BakerWustholz.C
    rw [hn3, hn2]
  have hC2 : BakerWustholz.C n d
      = 18 * (((n+1).factorial : ℕ) : ℝ) * (n:ℝ)^(n+1) * (32*(d:ℝ))^(n+2)
        * Real.log (2 * (n:ℝ) * (d:ℝ)) := rfl
  have hfact : (((n+1).factorial : ℕ) : ℝ) = ((n : ℝ) + 1) * (((n.factorial : ℕ) : ℝ)) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hp1 : (n:ℝ)^(n+1) = (n:ℝ)^n * (n:ℝ) := pow_succ _ _
  have hp2 : (32*(d:ℝ))^(n+2) = (32*(d:ℝ))^(n+1) * (32*(d:ℝ)) := by
    rw [show n + 2 = (n+1) + 1 from by omega, pow_succ]
  rw [hC1, hC2]
  have hcoef : 0 ≤ 18 * ((n.factorial:ℕ):ℝ) * (32*(d:ℝ))^(n+1) * (32*(d:ℝ)*(n:ℝ)*((n:ℝ)+1)) := by
    have hF : (0:ℝ) < ((n.factorial:ℕ):ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hQ : (0:ℝ) ≤ (32*(d:ℝ))^(n+1) := pow_nonneg (by positivity) _
    have hrest : (0:ℝ) ≤ 32*(d:ℝ)*(n:ℝ)*((n:ℝ)+1) := by positivity
    positivity
  calc 64 * (n : ℝ) * ((n : ℝ) + 1) * (d : ℝ)
        * (18 * ((n.factorial:ℕ):ℝ) * (((n-1:ℕ):ℝ))^n * (32*(d:ℝ))^(n+1)
           * Real.log (2 * ((n-1:ℕ):ℝ) * (d:ℝ)))
      = 18 * ((n.factorial:ℕ):ℝ) * (32*(d:ℝ))^(n+1) * (32*(d:ℝ)*(n:ℝ)*((n:ℝ)+1))
          * (2 * (((n-1:ℕ):ℝ))^n * Real.log (2 * ((n-1:ℕ):ℝ) * (d:ℝ))) := by ring
    _ ≤ 18 * ((n.factorial:ℕ):ℝ) * (32*(d:ℝ))^(n+1) * (32*(d:ℝ)*(n:ℝ)*((n:ℝ)+1))
          * ((n:ℝ)^n * Real.log (2 * (n:ℝ) * (d:ℝ))) :=
        mul_le_mul_of_nonneg_left hcore hcoef
    _ = 18 * (((n+1).factorial : ℕ) : ℝ) * (n:ℝ)^(n+1) * (32*(d:ℝ))^(n+2)
          * Real.log (2 * (n:ℝ) * (d:ℝ)) := by
        rw [hfact, hp1, hp2]
        ring

end Work.BW
