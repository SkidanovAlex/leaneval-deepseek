import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.bw_numeric_fallback
import Submission.Work.BW.log_sub_log_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The Baker–Wüstholz constant `C(n,d) = 18·(n+1)!·n^{n+1}·(32d)^{n+2}·log(2nd)` is
positive as soon as `n, d ≥ 1` (all factors are positive and `log(2nd) > 0`). -/
private lemma C_pos {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) : 0 < BakerWustholz.C n d := by
  have hlog : 0 < Real.log (2 * (n : ℝ) * (d : ℝ)) := by
    apply Real.log_pos
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have h1 : (0 : ℝ) < ((n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h2 : (0 : ℝ) < ((n : ℝ)) ^ (n + 1) := by
    apply pow_pos; exact_mod_cast hn
  have h3 : (0 : ℝ) < 32 * (d : ℝ) := by
    have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have h4 : (0 : ℝ) < (32 * (d : ℝ)) ^ (n + 2) := pow_pos h3 _
  unfold BakerWustholz.C
  exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) h1) h2) h4) hlog

theorem fallback_arith {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    {β M P : ℝ} (hβ1 : 1 ≤ β) (hβX : Real.log β ≤ Work.BW.Xbw n d)
    (hM1 : Real.log β ≤ M) (hM2 : Real.log 2 ≤ M)
    (hPpos : 0 < P) (hPlow : (1 : ℝ) / (d : ℝ) ^ n ≤ P) :
    n * β * (d : ℝ) ^ n * P + (d : ℝ) * Real.log 2 ≤ BakerWustholz.C n d * M * P := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβ1
  have hA : 0 < BakerWustholz.C n d := C_pos hn hd
  have hq : 0 < (d : ℝ) ^ n := pow_pos (by exact_mod_cast hd : (0 : ℝ) < (d : ℝ)) _
  have hdl2 : 0 ≤ (d : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg d) (le_of_lt hlog2pos)
  have hnum := bw_numeric_fallback hn hd
  -- Exponentiating the hypothesis `log β ≤ Xbw n d` bounds `β` by `C(n,d) / (d^n (n+d))`.
  have hbound : β ≤ BakerWustholz.C n d / ((d : ℝ) ^ n * ((n : ℝ) + (d : ℝ))) := by
    have hArg : Real.log β ≤
        Real.log (BakerWustholz.C n d / ((d : ℝ) ^ n * ((n : ℝ) + (d : ℝ)))) := by
      rw [Work.BW.Xbw] at hβX
      rw [Real.log_div (ne_of_gt hA) (by positivity),
          Real.log_mul (ne_of_gt hq) (by positivity),
          Real.log_pow]
      linarith
    calc β = Real.exp (Real.log β) := (Real.exp_log hβpos).symm
      _ ≤ Real.exp (Real.log (BakerWustholz.C n d / ((d : ℝ) ^ n * ((n : ℝ) + (d : ℝ))))) :=
            Real.exp_le_exp.mpr hArg
      _ = BakerWustholz.C n d / ((d : ℝ) ^ n * ((n : ℝ) + (d : ℝ))) :=
            Real.exp_log (by positivity)
  -- The core estimate, independent of `P`.
  have hmain : (d : ℝ) ^ n * ((n : ℝ) * β + (d : ℝ) * Real.log 2) ≤
      BakerWustholz.C n d * M := by
    rcases lt_or_ge β 2 with hβlt | hβge
    · -- Small `β`: use up the slack in the constant.
      have h1 : (n : ℝ) * β ≤ 2 * (n : ℝ) := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [hβlt.le, this]
      calc (d : ℝ) ^ n * ((n : ℝ) * β + (d : ℝ) * Real.log 2)
          ≤ (d : ℝ) ^ n * (2 * (n : ℝ) + (d : ℝ) * Real.log 2) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hq); linarith
        _ ≤ BakerWustholz.C n d * Real.log 2 := hnum
        _ ≤ BakerWustholz.C n d * M := mul_le_mul_of_nonneg_left hM2 (le_of_lt hA)
    · -- Large `β`: the logarithm of `β` itself pays for the linear term.
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hβqn : β ≤ BakerWustholz.C n d / ((d : ℝ) ^ n * (n : ℝ)) := by
        have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
        have hnd : (n : ℝ) ≤ (n : ℝ) + (d : ℝ) := by linarith
        have hden : (d : ℝ) ^ n * (n : ℝ) ≤ (d : ℝ) ^ n * ((n : ℝ) + (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hnd (le_of_lt hq)
        have hle : BakerWustholz.C n d / ((d : ℝ) ^ n * ((n : ℝ) + (d : ℝ))) ≤
            BakerWustholz.C n d / ((d : ℝ) ^ n * (n : ℝ)) :=
          div_le_div₀ (le_of_lt hA) le_rfl (mul_pos hq hnpos) hden
        linarith [hbound, hle]
      have hcy : ((d : ℝ) ^ n * (n : ℝ)) * β ≤ BakerWustholz.C n d := by
        rw [le_div_iff₀ (mul_pos hq hnpos)] at hβqn
        linarith [hβqn]
      have hstep := log_sub_log_lower (x := 2) (y := β) (c := (d : ℝ) ^ n * (n : ℝ))
        (A := BakerWustholz.C n d) (by norm_num) hβge hA hcy
      have hnum2 : 2 * ((d : ℝ) ^ n * (n : ℝ)) + (d : ℝ) ^ n * ((d : ℝ) * Real.log 2) ≤
          BakerWustholz.C n d * Real.log 2 := by
        linarith [hnum]
      nlinarith [hstep, hnum2, hM1, hA, le_of_lt hlog2pos]
  -- Multiply the core estimate by `P ≥ 1/d^n`.
  have hPq : 1 ≤ (d : ℝ) ^ n * P := by
    calc (1 : ℝ) = (1 / (d : ℝ) ^ n) * (d : ℝ) ^ n := (div_mul_cancel₀ 1 (ne_of_gt hq)).symm
      _ = (d : ℝ) ^ n * (1 / (d : ℝ) ^ n) := by ring
      _ ≤ (d : ℝ) ^ n * P := mul_le_mul_of_nonneg_left hPlow (le_of_lt hq)
  calc (n : ℝ) * β * (d : ℝ) ^ n * P + (d : ℝ) * Real.log 2
      = (d : ℝ) ^ n * P * ((n : ℝ) * β) + (d : ℝ) * Real.log 2 := by ring
    _ ≤ (d : ℝ) ^ n * P * ((n : ℝ) * β) + ((d : ℝ) ^ n * P) * ((d : ℝ) * Real.log 2) := by
        have := mul_le_mul_of_nonneg_right hPq hdl2
        linarith
    _ = (d : ℝ) ^ n * P * ((n : ℝ) * β + (d : ℝ) * Real.log 2) := by ring
    _ = ((d : ℝ) ^ n * ((n : ℝ) * β + (d : ℝ) * Real.log 2)) * P := by ring
    _ ≤ (BakerWustholz.C n d * M) * P := mul_le_mul_of_nonneg_right hmain (le_of_lt hPpos)
    _ = BakerWustholz.C n d * M * P := by ring

end Work.BW
