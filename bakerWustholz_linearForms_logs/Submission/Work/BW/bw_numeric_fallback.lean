import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Elementary two-sided estimate for `log 2`, used to dominate the `2n` term. -/
private lemma log_two_bounds : (2:ℝ)/3 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  refine ⟨?_, ?_⟩
  · have h := Real.log_two_gt_d9
    have h' : (2:ℝ)/3 ≤ 0.6931471803 := by norm_num
    linarith
  · have h := Real.log_two_lt_d9
    have h' : (0.6931471808:ℝ) ≤ 1 := by norm_num
    linarith

/-- The Baker–Wüstholz constant is large enough to absorb the elementary
"fallback" bound `d^n (2n + d log 2)`. -/
theorem bw_numeric_fallback {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) :
    (d : ℝ) ^ n * (2 * (n : ℝ) + (d : ℝ) * Real.log 2) ≤
      BakerWustholz.C n d * Real.log 2 := by
  set L : ℝ := Real.log 2 with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; exact Real.log_pos (by norm_num)
  obtain ⟨hL23, hL1⟩ := log_two_bounds
  have hL23' : (2:ℝ)/3 ≤ L := by rw [hLdef]; exact hL23
  have hL1' : L ≤ 1 := by rw [hLdef]; exact hL1
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdn : (0:ℝ) ≤ (d:ℝ) := by linarith
  -- Step 1: pull the `d` inside and pass from `d^n` to `d^(n+1)`.
  have h1 : 2 * (n:ℝ) + (d:ℝ) * L ≤ (d:ℝ) * (2 * (n:ℝ) + L) := by
    have h2n : (0:ℝ) ≤ 2 * (n:ℝ) := by positivity
    have hx : 2 * (n:ℝ) ≤ (d:ℝ) * (2 * (n:ℝ)) := by nlinarith [hd1, h2n]
    nlinarith [hx]
  have step1 : (d:ℝ)^n * (2*(n:ℝ) + (d:ℝ)*L) ≤ (d:ℝ)^(n+1) * (2*(n:ℝ)+L) := by
    have hdn0 : (0:ℝ) ≤ (d:ℝ)^n := by positivity
    calc (d:ℝ)^n * (2*(n:ℝ) + (d:ℝ)*L)
        ≤ (d:ℝ)^n * ((d:ℝ) * (2*(n:ℝ)+L)) := mul_le_mul_of_nonneg_left h1 hdn0
      _ = (d:ℝ)^(n+1) * (2*(n:ℝ)+L) := by rw [← mul_assoc, ← pow_succ]
  -- Step 2: `d^(n+1) ≤ (32 d)^(n+2)`.
  have step2a : (d:ℝ)^(n+1) ≤ (32*(d:ℝ))^(n+2) := by
    have ha : (d:ℝ)^(n+1) ≤ (32*(d:ℝ))^(n+1) :=
      pow_le_pow_left₀ hdn (by linarith) (n+1)
    have hb : (32*(d:ℝ))^(n+1) ≤ (32*(d:ℝ))^(n+2) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  have step2 : (d:ℝ)^(n+1) * (2*(n:ℝ)+L) ≤ (32*(d:ℝ))^(n+2) * (2*(n:ℝ)+L) :=
    mul_le_mul_of_nonneg_right step2a (by positivity)
  -- Step 3: `2n + log 2 ≤ 18 (n+1)! n^(n+1) (log 2)^2`.
  have hF : (2:ℝ) ≤ ((n+1).factorial : ℝ) := by
    have h2n : 2 ≤ (n+1).factorial := by
      calc 2 ≤ n+1 := by omega
        _ ≤ (n+1).factorial := Nat.self_le_factorial (n+1)
    exact_mod_cast h2n
  have hP : (n:ℝ) ≤ (n:ℝ)^(n+1) := by
    calc (n:ℝ) = (n:ℝ)^1 := (pow_one _).symm
      _ ≤ (n:ℝ)^(n+1) := pow_le_pow_right₀ hn1 (by omega)
  have hLsq : (4:ℝ)/9 ≤ L^2 := by nlinarith [sq_nonneg (L - 2/3), hL23']
  have hprod : (2:ℝ) * (n:ℝ) * (4/9) ≤ ((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * L^2 := by
    have hFP : (2:ℝ) * (n:ℝ) ≤ ((n+1).factorial : ℝ) * (n:ℝ)^(n+1) :=
      mul_le_mul hF hP (by positivity) (by positivity)
    exact mul_le_mul hFP hLsq (by norm_num) (by positivity)
  have h18 : (16:ℝ) * (n:ℝ) ≤ 18 * (((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * L^2) := by
    have hh := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ) ≤ 18)
    nlinarith [hh]
  have step3 : 2*(n:ℝ) + L ≤ 18 * ((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * L^2 := by
    nlinarith [h18, hL1', hn1]
  -- Step 4: absorb `(log 2)^2` into `log (2 n d) * log 2`.
  have hlog : L ≤ Real.log (2 * (n:ℝ) * (d:ℝ)) := by
    rw [hLdef]
    apply Real.log_le_log (by norm_num)
    have : (2:ℝ) ≤ 2*(n:ℝ)*(d:ℝ) := by nlinarith [hn1, hd1]
    linarith
  have hA : (0:ℝ) ≤ (32*(d:ℝ))^(n+2) * (18*((n+1).factorial:ℝ)*(n:ℝ)^(n+1)) := by positivity
  have hkey : L^2 ≤ Real.log (2*(n:ℝ)*(d:ℝ)) * L := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hlog hLpos.le
  have step4 : (32*(d:ℝ))^(n+2) * (18*((n+1).factorial:ℝ)*(n:ℝ)^(n+1)*L^2) ≤
      BakerWustholz.C n d * L := by
    rw [BakerWustholz.C]
    calc (32*(d:ℝ))^(n+2) * (18*((n+1).factorial:ℝ)*(n:ℝ)^(n+1)*L^2)
        = ((32*(d:ℝ))^(n+2) * (18*((n+1).factorial:ℝ)*(n:ℝ)^(n+1))) * L^2 := by ring
      _ ≤ ((32*(d:ℝ))^(n+2) * (18*((n+1).factorial:ℝ)*(n:ℝ)^(n+1))) *
            (Real.log (2*(n:ℝ)*(d:ℝ)) * L) :=
            mul_le_mul_of_nonneg_left hkey hA
      _ = 18*((n+1).factorial:ℝ)*(n:ℝ)^(n+1)*(32*(d:ℝ))^(n+2)*
            Real.log (2*(n:ℝ)*(d:ℝ))*L := by ring
  calc (d:ℝ)^n * (2*(n:ℝ) + (d:ℝ)*L)
      ≤ (d:ℝ)^(n+1) * (2*(n:ℝ)+L) := step1
    _ ≤ (32*(d:ℝ))^(n+2) * (2*(n:ℝ)+L) := step2
    _ ≤ (32*(d:ℝ))^(n+2) * (18*((n+1).factorial:ℝ)*(n:ℝ)^(n+1)*L^2) :=
          mul_le_mul_of_nonneg_left step3 (by positivity)
    _ ≤ BakerWustholz.C n d * L := step4

end Work.BW
