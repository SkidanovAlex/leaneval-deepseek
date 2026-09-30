import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For `n, d ≥ 1`: `3·d^n·((n-1)·64nd + n²) ≤ C(n,d)·log 2`.
Proof sketch: `C(n,d)·log 2 ≥ 18·(n+1)!·n^{n+1}·(32d)^{n+2}·(2/3)·(2/3) = 8(n+1)!n^{n+1}(32d)^{n+2}`
(since `log(2nd) ≥ log 2 ≥ 2/3`, as `2nd ≥ 2`). Divide both sides by the positive `3·d^n`:
it suffices to show `(n-1)·64nd + n² ≤ (8/3)(n+1)!n^{n+1}32^{n+2}d²`, i.e.
`64n²d + n² ≤ (8/3)(n+1)!n^{n+1}32^{n+2}d²`; for `n ≥ 2` use `(n+1)! ≥ 6`, `n^{n+1} ≥ n²`, `32^{n+2} ≥ 32³`,
`d² ≥ d` to get RHS `≥ 524288·n²d ≥ 65n²d ≥ 64n²d + n²`; for `n = 1` the goal is `3d ≤ 16·32³·d³`. -/
theorem bw_rank1_logK0_num_le (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    3 * (d : ℝ) ^ n * (((n : ℝ) - 1) * (64 * n * d : ℝ) + (n : ℝ) ^ 2) ≤
      BakerWustholz.C n d * Real.log 2 := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hn0 : (0:ℝ) ≤ (n:ℝ) := le_trans zero_le_one hn1
  have hd0 : (0:ℝ) ≤ (d:ℝ) := le_trans zero_le_one hd1
  -- the two logarithms on the right are both at least `2/3`
  have hlog2 : (2:ℝ)/3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnd1 : (1:ℝ) ≤ (n:ℝ) * (d:ℝ) := by
    have h := mul_le_mul hn1 hd1 (by norm_num) hn0
    simpa using h
  have h2nd : (2:ℝ) ≤ 2 * (n:ℝ) * (d:ℝ) := by linarith [hnd1]
  have hlog_le : Real.log 2 ≤ Real.log (2 * (n:ℝ) * (d:ℝ)) :=
    Real.log_le_log (by norm_num) h2nd
  have hlogpos : (0:ℝ) ≤ Real.log (2 * (n:ℝ) * (d:ℝ)) :=
    le_trans (by norm_num) (le_trans hlog2 hlog_le)
  have hprod : (4:ℝ)/9 ≤ Real.log (2 * (n:ℝ) * (d:ℝ)) * Real.log 2 := by
    have h := mul_le_mul (le_trans hlog2 hlog_le) hlog2 (by norm_num) hlogpos
    linarith [h]
  -- hence `C n d * log 2 ≥ 18·P·(4/9) = 8·P` where `P = (n+1)!·n^{n+1}·(32d)^{n+2}`
  have hC : 8 * (((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * (32*(d:ℝ))^(n+2)) ≤
            BakerWustholz.C n d * Real.log 2 := by
    have h1 : 18 * (((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * (32*(d:ℝ))^(n+2)) * ((4:ℝ)/9) ≤
              18 * (((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * (32*(d:ℝ))^(n+2)) *
                (Real.log (2 * (n:ℝ) * (d:ℝ)) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    calc 8 * (((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * (32*(d:ℝ))^(n+2))
        = 18 * (((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * (32*(d:ℝ))^(n+2)) * ((4:ℝ)/9) := by ring
      _ ≤ 18 * (((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * (32*(d:ℝ))^(n+2)) *
              (Real.log (2 * (n:ℝ) * (d:ℝ)) * Real.log 2) := h1
      _ = BakerWustholz.C n d * Real.log 2 := by unfold BakerWustholz.C; ring
  -- elementary lower bounds on the factorial and the powers
  have hf : (2:ℝ) ≤ ((n+1).factorial : ℝ) := by
    have h2n : (2:ℕ) ≤ n + 1 := by omega
    have h := Nat.factorial_le h2n
    norm_num at h
    exact_mod_cast h
  have hA : (1:ℝ) ≤ (n:ℝ)^(n-1) := one_le_pow₀ hn1
  have hB : (32768:ℝ) ≤ (32:ℝ)^(n+2) := by
    have h3n : (3:ℕ) ≤ n + 2 := by omega
    have h := pow_le_pow_right₀ (show (1:ℝ) ≤ 32 by norm_num) h3n
    norm_num at h
    exact h
  have hdval : 64*(d:ℝ) + 1 ≤ (8/3) * 2 * 1 * 32768 * (d:ℝ)^2 := by
    have hdsq : (d:ℝ) ≤ (d:ℝ)^2 := by
      have h := mul_le_mul_of_nonneg_left hd1 hd0
      simpa [pow_two] using h
    nlinarith [hdsq, hd1]
  have hconst : (8/3) * 2 * 1 * 32768 * (d:ℝ)^2 ≤
      (8/3) * ((n+1).factorial : ℝ) * (n:ℝ)^(n-1) * (32:ℝ)^(n+2) * (d:ℝ)^2 := by
    have hmul : (2:ℝ) * 1 * 32768 ≤ ((n+1).factorial : ℝ) * (n:ℝ)^(n-1) * (32:ℝ)^(n+2) := by
      have h21 : (2:ℝ) * 1 ≤ ((n+1).factorial : ℝ) * (n:ℝ)^(n-1) :=
        mul_le_mul hf hA (by norm_num) (by positivity)
      calc (2:ℝ) * 1 * 32768 = ((2:ℝ)*1) * 32768 := rfl
        _ ≤ (((n+1).factorial : ℝ) * (n:ℝ)^(n-1)) * (32:ℝ)^(n+2) :=
              mul_le_mul h21 hB (by norm_num) (by positivity)
        _ = ((n+1).factorial : ℝ) * (n:ℝ)^(n-1) * (32:ℝ)^(n+2) := by ring
    have hpos : (0:ℝ) ≤ (8/3) * (d:ℝ)^2 := by positivity
    have hh := mul_le_mul_of_nonneg_left hmul hpos
    calc (8/3) * 2 * 1 * 32768 * (d:ℝ)^2
        = ((8/3) * (d:ℝ)^2) * (2 * 1 * 32768) := by ring
      _ ≤ ((8/3) * (d:ℝ)^2) * (((n+1).factorial : ℝ) * (n:ℝ)^(n-1) * (32:ℝ)^(n+2)) := hh
      _ = (8/3) * ((n+1).factorial : ℝ) * (n:ℝ)^(n-1) * (32:ℝ)^(n+2) * (d:ℝ)^2 := by ring
  have hQ : 64*(d:ℝ) + 1 ≤ (8/3) * ((n+1).factorial : ℝ) * (n:ℝ)^(n-1) * (32:ℝ)^(n+2) * (d:ℝ)^2 :=
    le_trans hdval hconst
  -- the numerator `((n-1)·64nd + n²)` is at most `n²·(64d+1)`
  have hE : ((n:ℝ)-1)*(64*(n:ℝ)*(d:ℝ)) + (n:ℝ)^2 ≤ (n:ℝ)^2 * (64*(d:ℝ)+1) := by
    nlinarith [mul_nonneg hn0 hd0]
  have hsplit : (n:ℝ)^2 * (n:ℝ)^(n-1) = (n:ℝ)^(n+1) := by
    rw [← pow_add]
    congr 1
    omega
  have hE2 : ((n:ℝ)-1)*(64*(n:ℝ)*(d:ℝ)) + (n:ℝ)^2 ≤
      (8/3) * ((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * (32:ℝ)^(n+2) * (d:ℝ)^2 := by
    have hmul := mul_le_mul_of_nonneg_left hQ (show (0:ℝ) ≤ (n:ℝ)^2 by positivity)
    calc ((n:ℝ)-1)*(64*(n:ℝ)*(d:ℝ)) + (n:ℝ)^2
        ≤ (n:ℝ)^2 * (64*(d:ℝ)+1) := hE
      _ ≤ (n:ℝ)^2 * ((8/3) * ((n+1).factorial : ℝ) * (n:ℝ)^(n-1) * (32:ℝ)^(n+2) * (d:ℝ)^2) := hmul
      _ = (8/3) * ((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * (32:ℝ)^(n+2) * (d:ℝ)^2 := by
            rw [← hsplit]; ring
  have hfin : 3 * (d:ℝ)^n * (((n:ℝ)-1)*(64*(n:ℝ)*(d:ℝ)) + (n:ℝ)^2) ≤
              3 * (d:ℝ)^n * ((8/3) * ((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * (32:ℝ)^(n+2) * (d:ℝ)^2) :=
    mul_le_mul_of_nonneg_left hE2 (by positivity)
  have hdd : (d:ℝ)^(n+2) = (d:ℝ)^n * (d:ℝ)^2 := pow_add (d:ℝ) n 2
  have h32d : (32*(d:ℝ))^(n+2) = (32:ℝ)^(n+2) * (d:ℝ)^(n+2) := mul_pow _ _ _
  have hP_eq : ((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * (32*(d:ℝ))^(n+2) =
               ((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * (32:ℝ)^(n+2) * (d:ℝ)^n * (d:ℝ)^2 := by
    rw [h32d, hdd]; ring
  have hfin2 : 3 * (d:ℝ)^n * ((8/3) * ((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * (32:ℝ)^(n+2) * (d:ℝ)^2) =
               8 * (((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * (32*(d:ℝ))^(n+2)) := by
    rw [hP_eq]; ring
  have hmain : 3 * (d:ℝ)^n * (((n:ℝ)-1)*(64*(n:ℝ)*(d:ℝ)) + (n:ℝ)^2) ≤
               8 * (((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * (32*(d:ℝ))^(n+2)) :=
    le_trans hfin (le_of_eq hfin2)
  exact le_trans hmain hC

end Work.BW
