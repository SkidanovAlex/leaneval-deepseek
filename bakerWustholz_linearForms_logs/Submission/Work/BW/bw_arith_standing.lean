import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

namespace Work.BW

/-- Expansion of `X(n,d) = log C(n,d) − n log d − log(n+d)` into a sum of logarithms,
valid for `n, d ≥ 1`. -/
lemma Xbw_expansion (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    Xbw n d = Real.log 18 + Real.log ((n + 1).factorial : ℝ)
      + ((n : ℝ) + 1) * Real.log (n : ℝ)
      + ((n : ℝ) + 2) * Real.log 32 + 2 * Real.log (d : ℝ)
      + Real.log (Real.log (2 * (n : ℝ) * (d : ℝ))) - Real.log ((n : ℝ) + (d : ℝ)) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hn0 : (0:ℝ) < (n:ℝ) := lt_of_lt_of_le one_pos hn1
  have hd0 : (0:ℝ) < (d:ℝ) := lt_of_lt_of_le one_pos hd1
  have hL0 : (0:ℝ) < Real.log (2 * (n:ℝ) * (d:ℝ)) := by
    apply Real.log_pos; nlinarith
  rw [Xbw, BakerWustholz.C,
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow,
      Real.log_mul (by norm_num : (32:ℝ) ≠ 0) (by positivity : (d:ℝ) ≠ 0)]
  push_cast
  ring

theorem bw_arith_standing (n d : ℕ) (H : ℝ) (hn : 2 ≤ n) (hd : 1 ≤ d) (hH : Xbw n d ≤ H) :
    Real.exp 1 ≤ (60 * (d : ℝ) * Real.log (6 * (d : ℝ))) ^ n * (n.factorial : ℝ) ∧
    Real.log ((60 * (d : ℝ) * Real.log (6 * (d : ℝ))) ^ n * (n.factorial : ℝ)) < n * H := by
  have hn1 : 1 ≤ n := by omega
  have hN1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hN2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hNpos : (0:ℝ) < (n:ℝ) := by linarith
  have hNnn : (0:ℝ) ≤ (n:ℝ) := le_of_lt hNpos
  have hD1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hDpos : (0:ℝ) < (d:ℝ) := by linarith
  have hlog6 : 0 < Real.log (6 * (d:ℝ)) := Real.log_pos (by nlinarith)
  have hlog2nd : 0 < Real.log (2 * (n:ℝ) * (d:ℝ)) := Real.log_pos (by nlinarith)
  have hlog6_1 : (1:ℝ) ≤ Real.log (6 * (d:ℝ)) := by
    rw [Real.le_log_iff_exp_le (by nlinarith : (0:ℝ) < 6 * (d:ℝ))]
    linarith [Real.exp_one_lt_three, hD1]
  have hlogN : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hN1
  have hF1 : (1:ℝ) ≤ (n.factorial:ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n))
  have hlogF : 0 ≤ Real.log ((n.factorial:ℝ)) := Real.log_nonneg hF1
  have hG1 : (1:ℝ) ≤ ((n+1).factorial:ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (n+1)))
  have hlogG : 0 ≤ Real.log (((n+1).factorial:ℝ)) := Real.log_nonneg hG1
  refine ⟨?_, ?_⟩
  · -- first conjunct
    have hc1 : (1:ℝ) ≤ 60 * (d:ℝ) * Real.log (6*(d:ℝ)) := by nlinarith
    have h60 : (60:ℝ) ≤ 60 * (d:ℝ) * Real.log (6*(d:ℝ)) := by nlinarith
    have hpow : (60:ℝ) ≤ (60 * (d:ℝ) * Real.log (6*(d:ℝ)))^n := by
      have h1 : (60 * (d:ℝ) * Real.log (6*(d:ℝ)))^1 ≤ (60 * (d:ℝ) * Real.log (6*(d:ℝ)))^n :=
        pow_le_pow_right₀ hc1 hn1
      rw [pow_one] at h1
      exact le_trans h60 h1
    have hge : (60:ℝ) ≤ (60 * (d:ℝ) * Real.log (6*(d:ℝ)))^n * (n.factorial:ℝ) := by
      have h := mul_le_mul hpow hF1 (by norm_num : (0:ℝ) ≤ 1)
        (le_trans (by norm_num : (0:ℝ) ≤ 60) hpow)
      calc (60:ℝ) = 60 * 1 := by ring
        _ ≤ _ := h
    linarith [Real.exp_one_lt_three, hge]
  · -- second conjunct
    have hX := Xbw_expansion n d hn1 hd
    have hLHS : Real.log ((60 * (d:ℝ) * Real.log (6 * (d:ℝ)))^n * (n.factorial:ℝ))
        = (n:ℝ) * (Real.log 60 + Real.log (d:ℝ) + Real.log (Real.log (6*(d:ℝ))))
          + Real.log ((n.factorial:ℝ)) := by
      have h1 : Real.log ((60 * (d:ℝ) * Real.log (6*(d:ℝ)))^n * (n.factorial:ℝ))
          = Real.log ((60 * (d:ℝ) * Real.log (6*(d:ℝ)))^n) + Real.log ((n.factorial:ℝ)) :=
        Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_ne_zero n))
      have h2 : Real.log ((60 * (d:ℝ) * Real.log (6*(d:ℝ)))^n)
          = (n:ℝ) * Real.log (60 * (d:ℝ) * Real.log (6*(d:ℝ))) := Real.log_pow _ _
      have h3 : Real.log (60 * (d:ℝ) * Real.log (6*(d:ℝ)))
          = Real.log (60 * (d:ℝ)) + Real.log (Real.log (6*(d:ℝ))) :=
        Real.log_mul (by positivity) (ne_of_gt hlog6)
      have h4 : Real.log (60 * (d:ℝ)) = Real.log 60 + Real.log (d:ℝ) :=
        Real.log_mul (by norm_num) (ne_of_gt hDpos)
      rw [h1, h2, h3, h4]
    have hkey : Real.log ((60 * (d:ℝ) * Real.log (6 * (d:ℝ)))^n * (n.factorial:ℝ))
        < (n:ℝ) * Xbw n d := by
      rw [hLHS, hX]
      -- numeric combination
      have h1 : -3*(n:ℝ) ≤ (n:ℝ) * (Real.log 18 - Real.log 60) := by
        have h1830 : -(3:ℝ) ≤ Real.log 18 - Real.log 60 := by
          have hle := Real.log_le_sub_one_of_pos (show (0:ℝ) < 60/18 by norm_num)
          have hdv : Real.log (60/18) = Real.log 60 - Real.log 18 :=
            Real.log_div (by norm_num) (by norm_num)
          linarith [hle, hdv]
        have := mul_le_mul_of_nonneg_left h1830 hNnn
        linarith [this]
      have h2 : 0 ≤ (n:ℝ) * Real.log ((n+1).factorial:ℝ) - Real.log ((n.factorial:ℝ)) := by
        have hsplit : Real.log ((n+1).factorial:ℝ)
            = Real.log ((n:ℝ)+1) + Real.log ((n.factorial:ℝ)) := by
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
            Real.log_mul (by positivity) (by positivity)]
        have hlogn1 : 0 ≤ Real.log ((n:ℝ)+1) := Real.log_nonneg (by linarith)
        nlinarith [hsplit, hlogn1, hlogF, hN1, hNnn]
      have h3 : 0 ≤ (n:ℝ) * (((n:ℝ)+1) * Real.log (n:ℝ)) := by
        have : 0 ≤ ((n:ℝ)+1) * Real.log (n:ℝ) := mul_nonneg (by linarith) hlogN
        exact mul_nonneg hNnn this
      have h4 : 3 * ((n:ℝ) * ((n:ℝ)+2)) ≤ (n:ℝ) * (((n:ℝ)+2) * Real.log 32) := by
        have h32 : (3:ℝ) ≤ Real.log 32 := by
          have h := Real.log_two_gt_d9
          rw [show (32:ℝ) = 2^5 by norm_num, Real.log_pow]
          push_cast
          linarith
        have hstep : ((n:ℝ)+2) * 3 ≤ ((n:ℝ)+2) * Real.log 32 :=
          mul_le_mul_of_nonneg_left h32 (by linarith)
        calc 3 * ((n:ℝ) * ((n:ℝ)+2)) = (n:ℝ) * (((n:ℝ)+2) * 3) := by ring
          _ ≤ (n:ℝ) * (((n:ℝ)+2) * Real.log 32) := mul_le_mul_of_nonneg_left hstep hNnn
      have h5 : -((n:ℝ)*(n:ℝ)) ≤ (n:ℝ) * (Real.log (d:ℝ) - Real.log ((n:ℝ)+(d:ℝ))) := by
        have harg : 0 < ((n:ℝ)+(d:ℝ))/(d:ℝ) := by positivity
        have hle := Real.log_le_sub_one_of_pos harg
        have hdiv : Real.log (((n:ℝ)+(d:ℝ))/(d:ℝ))
            = Real.log ((n:ℝ)+(d:ℝ)) - Real.log (d:ℝ) :=
          Real.log_div (by linarith) (ne_of_gt hDpos)
        have hratio : ((n:ℝ)+(d:ℝ))/(d:ℝ) - 1 ≤ (n:ℝ) := by
          rw [div_sub_one (ne_of_gt hDpos), div_le_iff₀ hDpos]
          nlinarith
        have hb : Real.log ((n:ℝ)+(d:ℝ)) - Real.log (d:ℝ) ≤ (n:ℝ) := by
          rw [← hdiv]; linarith
        have hc : -(n:ℝ) ≤ Real.log (d:ℝ) - Real.log ((n:ℝ)+(d:ℝ)) := by linarith
        have := mul_le_mul_of_nonneg_left hc hNnn
        nlinarith [this]
      have h6 : -2 ≤ (n:ℝ) * (Real.log (Real.log (2*(n:ℝ)*(d:ℝ)))
            - Real.log (Real.log (6*(d:ℝ)))) := by
        rcases le_or_gt n 2 with hn2 | hn3
        · have hn_eq : n = 2 := by omega
          subst hn_eq
          have h42 : (6:ℝ) * (d:ℝ) ≤ (4 * (d:ℝ))^2 := by nlinarith
          have hy : 0 < Real.log (6*(d:ℝ)) := hlog6
          have hx4 : 0 < Real.log (4*(d:ℝ)) := Real.log_pos (by nlinarith)
          have hx : Real.log (6*(d:ℝ)) ≤ 2 * Real.log (4*(d:ℝ)) := by
            have h := Real.log_le_log (show (0:ℝ) < 6*(d:ℝ) by nlinarith) h42
            rw [show (4*(d:ℝ))^2 = (4*(d:ℝ))^(2:ℕ) from rfl, Real.log_pow] at h
            push_cast at h
            linarith [h]
          have hhalf : (1/2:ℝ) ≤ Real.log (4*(d:ℝ)) / Real.log (6*(d:ℝ)) := by
            rw [le_div_iff₀ hy]; linarith [hx]
          have hdiff : Real.log (Real.log (4*(d:ℝ))) - Real.log (Real.log (6*(d:ℝ)))
              = Real.log (Real.log (4*(d:ℝ)) / Real.log (6*(d:ℝ))) := by
            rw [Real.log_div (ne_of_gt hx4) (ne_of_gt hy)]
          have hloghalf : Real.log ((1:ℝ)/2) = -Real.log 2 := by
            rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
          have hfin : -(1:ℝ) ≤ Real.log (Real.log (4*(d:ℝ))) - Real.log (Real.log (6*(d:ℝ))) := by
            rw [hdiff]
            have h1 : Real.log ((1:ℝ)/2) ≤ Real.log (Real.log (4*(d:ℝ)) / Real.log (6*(d:ℝ))) :=
              Real.log_le_log (by norm_num) hhalf
            rw [hloghalf] at h1
            have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
            linarith
          norm_num
          linarith [hfin]
        · have hn3R : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 3 ≤ n)
          have hge : 6*(d:ℝ) ≤ 2*(n:ℝ)*(d:ℝ) := by nlinarith
          have hmono : Real.log (Real.log (6*(d:ℝ))) ≤ Real.log (Real.log (2*(n:ℝ)*(d:ℝ))) :=
            Real.log_le_log hlog6 (Real.log_le_log (by nlinarith) hge)
          nlinarith [hmono, hNnn]
      have h7 : (0:ℝ) < 2*((n:ℝ)*(n:ℝ)) + 3*(n:ℝ) - 2 := by nlinarith
      nlinarith [h1, h2, h3, h4, h5, h6, h7]
    calc Real.log ((60 * (d:ℝ) * Real.log (6 * (d:ℝ)))^n * (n.factorial:ℝ))
        < (n:ℝ) * Xbw n d := hkey
      _ ≤ (n:ℝ) * H := mul_le_mul_of_nonneg_left hH hNnn

end Work.BW
