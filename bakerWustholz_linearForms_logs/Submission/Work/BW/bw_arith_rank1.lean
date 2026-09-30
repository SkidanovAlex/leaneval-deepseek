import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.bw_rank1_logK0_le
import Submission.Work.BW.bw_rank1_K0_mul_le
import Submission.Work.BW.bw_rank1_dpow_le
import Submission.Work.BW.bw_rank1_logK0_num_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The rank-one arithmetic step of BW §11 (`r = 1`)

This file proves `Work.BW.bw_arith_rank1`, the purely numeric step that closes the rank-one
case of the Baker–Wüstholz argument. In the rank-one case the (relative) Liouville estimate
applied to the single auxiliary point `α'₁` gives a lower bound of the shape
`log ‖Λ‖ ≥ -(log d + log σ₁ + d σ₁ + d log 2)`; the lemma here shows that this quantity is
dominated by `C(n,d) · max(log B, 1/d) · P` as soon as `σ₁ ≤ κ(n,d,1,v,c) · P` and
`P ≥ d^{-n}` (the latter being the hypothesis on the product of the modified heights).

## Mathematical shape of the proof

Write `dℝ = (d:ℝ)`, `C = BakerWustholz.C n d`, `π = max (log B) (1/dℝ)`, and put

`K₀ := (64·n·d)^{n-1} · n!/2^{n-1}`  (≥ κ(n,d,1,v,c), since `min (c/2^v) 1 ≤ 1`).

Since `σ₁ ≤ K₀ P`, it is enough to bound `E + log P + dℝ·K₀·P` where
`E = log dℝ + log K₀ + dℝ log 2`. The key point is that `P` is allowed to range over
`[dℝ^{-n}, ∞)`, so the logarithm `log P` must be paid for by the *linear* term `A·P`,
`A := C π - dℝ K₀`. Two facts make this work:

* `A ≥ dℝ^n`, so the function `P ↦ E + log P - A P` is decreasing on `[dℝ^{-n}, ∞)`
  (elementary form: for `y = P dℝ^n ≥ 1`, `log y - (A/dℝ^n)(y-1) ≤ log y - (y-1) ≤ 0`);
  hence it suffices to check `P = dℝ^{-n}`, i.e. `dℝ^n (E - n log dℝ) ≤ A`;
* `dℝ^n (E - n log dℝ) ≤ dℝ^n (log K₀ + dℝ log 2) ≤ (1/3 + 1/3)·C log 2 ≤ A`,
  the last step using `3 dℝ K₀ ≤ C log 2`.

The four arithmetic inequalities used above are proved in the sibling files
`bw_rank1_logK0_le`, `bw_rank1_logK0_num_le`, `bw_rank1_K0_mul_le`, `bw_rank1_dpow_le`.
-/

namespace Work.BW

open Complex

/-- `2^(n-1) ≤ n!` for every `n` (each factor of `n!` after the first is at least `2`). -/
private lemma two_pow_sub_one_le_factorial : ∀ n : ℕ, 2 ^ (n - 1) ≤ n.factorial
  | 0 => by decide
  | 1 => by decide
  | (n + 2) => by
      have ih := two_pow_sub_one_le_factorial (n + 1)
      have h : n + 2 - 1 = (n + 1 - 1) + 1 := by omega
      calc 2 ^ (n + 2 - 1) = 2 * 2 ^ (n + 1 - 1) := by rw [h, pow_succ]; ring
        _ ≤ 2 * (n + 1).factorial := Nat.mul_le_mul_left 2 ih
        _ ≤ (n + 2).factorial := by
            rw [Nat.factorial_succ]
            exact Nat.mul_le_mul_right _ (by omega)

/-- Positivity of the Baker–Wüstholz constant for `n, d ≥ 1`. -/
private lemma Cpos (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) : 0 < BakerWustholz.C n d := by
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

theorem bw_arith_rank1 (n d v : ℕ) (c σ₁ P : ℝ) (B : ℕ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hc : 1 < c) (hP : 0 < P) (hPn : (d : ℝ) ^ (-(n : ℤ)) ≤ P)
    (hB : 2 ≤ B) (hσ : σ₁ ≤ kappa n d 1 v c * P) (hσpos : 0 < σ₁) :
    Real.log d + Real.log σ₁ + d * σ₁ + d * Real.log 2 ≤
      BakerWustholz.C n d * max (Real.log B) (1 / (d : ℝ)) * P := by
  have hnR1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hdR1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hnRpos : (0:ℝ) < (n:ℝ) := by linarith
  have hdRpos : (0:ℝ) < (d:ℝ) := by linarith
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcpos : (0:ℝ) < c := by linarith
  -- `K₀`, the `v`- and `c`-independent bound for `κ(n,d,1,v,c)`
  set K : ℝ := (64 * n * d : ℝ) ^ (n - 1) * ((n.factorial : ℝ) / 2 ^ (n - 1)) with hK
  have h64pos : (0:ℝ) < (64 * n * d : ℝ) := by positivity
  have hKpos : 0 < K := by
    rw [hK]
    exact mul_pos (pow_pos h64pos _)
      (div_pos (by exact_mod_cast Nat.factorial_pos n) (by positivity))
  -- `κ(n,d,1,v,c) ≤ K₀` because `min (c/2^v) 1 ≤ 1`
  have hκK : kappa n d 1 v c ≤ K := by
    rw [hK, kappa]
    have hmin : min (c / 2 ^ v) 1 ≤ 1 := min_le_right _ _
    have hnn : (0:ℝ) ≤ (64 * n * d : ℝ) ^ (n - 1) * ((n.factorial : ℝ) / 2 ^ (n - 1)) := by
      positivity
    calc (64 * n * d : ℝ) ^ (n - 1) * ((n.factorial : ℝ) / 2 ^ (n - 1)) * min (c / 2 ^ v) 1
        ≤ (64 * n * d : ℝ) ^ (n - 1) * ((n.factorial : ℝ) / 2 ^ (n - 1)) * 1 :=
          mul_le_mul_of_nonneg_left hmin hnn
      _ = (64 * n * d : ℝ) ^ (n - 1) * ((n.factorial : ℝ) / 2 ^ (n - 1)) := mul_one _
  have hσKP : σ₁ ≤ K * P := le_trans hσ (mul_le_mul_of_nonneg_right hκK (le_of_lt hP))
  have hlogσ : Real.log σ₁ ≤ Real.log K + Real.log P := by
    have h1 : Real.log σ₁ ≤ Real.log (K * P) := Real.log_le_log hσpos hσKP
    rwa [Real.log_mul (ne_of_gt hKpos) (ne_of_gt hP)] at h1
  have hdσ : (d:ℝ) * σ₁ ≤ ((d:ℝ) * K) * P := by
    calc (d:ℝ) * σ₁ ≤ (d:ℝ) * (K * P) := mul_le_mul_of_nonneg_left hσKP (le_of_lt hdRpos)
      _ = ((d:ℝ) * K) * P := by ring
  -- `n!/2^{n-1} ≥ 1` and `d^{n-1} ≤ K₀`
  have hfact : 2 ^ (n - 1) ≤ n.factorial := two_pow_sub_one_le_factorial n
  have hfact1 : (1:ℝ) ≤ (n.factorial : ℝ) / 2 ^ (n - 1) := by
    have h2 : (2:ℝ)^(n-1) ≤ (n.factorial:ℝ) := by exact_mod_cast hfact
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^(n-1))]
    simpa using h2
  have hdn_le_K : (d:ℝ)^(n-1) ≤ K := by
    rw [hK]
    have hle1 : (d:ℝ)^(n-1) ≤ (64 * n * d : ℝ)^(n-1) := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [hnR1, hdR1]
    exact le_trans hle1 (le_mul_of_one_le_right (by positivity) hfact1)
  have hdn_decomp : (d:ℝ)^n = (d:ℝ)^(n-1) * (d:ℝ) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
  have hdn_le_2dK : (d:ℝ)^n ≤ 2 * ((d:ℝ) * K) := by
    rw [hdn_decomp]
    have h1 : (d:ℝ)^(n-1) * (d:ℝ) ≤ (d:ℝ) * K := by
      calc (d:ℝ)^(n-1) * (d:ℝ) ≤ K * (d:ℝ) :=
            mul_le_mul_of_nonneg_right hdn_le_K (by positivity)
        _ = (d:ℝ) * K := by ring
    nlinarith [h1, hdRpos, hKpos]
  -- the two lower bounds on `π = max (log B) (1/d)`
  have hπge : Real.log 2 ≤ max (Real.log B) (1/(d:ℝ)) :=
    le_trans (Real.log_le_log (by norm_num) (by exact_mod_cast hB)) (le_max_left _ _)
  have hCpos : 0 < BakerWustholz.C n d := Cpos n d hn hd
  have hCpi : BakerWustholz.C n d * Real.log 2
      ≤ BakerWustholz.C n d * max (Real.log B) (1/(d:ℝ)) :=
    mul_le_mul_of_nonneg_left hπge (le_of_lt hCpos)
  -- the four arithmetic inputs
  have A1 := bw_rank1_K0_mul_le n d hn hd
  have A2 := bw_rank1_dpow_le n d hn hd
  have A3 := bw_rank1_logK0_num_le n d hn hd
  have A4 := bw_rank1_logK0_le n d hn hd
  set A : ℝ := BakerWustholz.C n d * max (Real.log B) (1/(d:ℝ)) - (d:ℝ) * K with hA
  have hA_ge : (d:ℝ)^n ≤ A := by
    rw [hA]
    linarith [hCpi, A1, hdn_le_2dK]
  have hA_pos : 0 < A := lt_of_lt_of_le (pow_pos hdRpos n) hA_ge
  have hA_lb : (2/3) * (BakerWustholz.C n d * Real.log 2) ≤ A := by
    rw [hA]
    linarith [hCpi, A1]
  -- `d^n (log K₀ + d log 2) ≤ A`
  have hmain : (d:ℝ)^n * (Real.log K + (d:ℝ) * Real.log 2) ≤ A := by
    have h1 : (d:ℝ)^n * Real.log K ≤ (1/3) * (BakerWustholz.C n d * Real.log 2) := by
      have hlog : Real.log K ≤ ((n:ℝ) - 1) * (64 * n * d : ℝ) + (n:ℝ)^2 := by rw [hK]; exact A4
      have h2 : (d:ℝ)^n * Real.log K
          ≤ (d:ℝ)^n * (((n:ℝ)-1)*(64*n*d:ℝ) + (n:ℝ)^2) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      linarith [h2, A3]
    have h2 : (d:ℝ)^n * ((d:ℝ) * Real.log 2) ≤ (1/3) * (BakerWustholz.C n d * Real.log 2) := by
      have h2' := A2
      rw [pow_succ] at h2'
      linarith [h2']
    calc (d:ℝ)^n * (Real.log K + (d:ℝ) * Real.log 2)
        = (d:ℝ)^n * Real.log K + (d:ℝ)^n * ((d:ℝ) * Real.log 2) := by ring
      _ ≤ (1/3) * (BakerWustholz.C n d * Real.log 2) + (1/3) * (BakerWustholz.C n d * Real.log 2) := by
            linarith
      _ ≤ A := by linarith [hA_lb]
  -- `d^n (E - n log d) ≤ A`
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hdR1
  have hconst : (d:ℝ)^n * (Real.log d + Real.log K + (d:ℝ) * Real.log 2 - (n:ℝ) * Real.log d) ≤ A := by
    have hle : Real.log d + Real.log K + (d:ℝ) * Real.log 2 - (n:ℝ) * Real.log d ≤
        Real.log K + (d:ℝ) * Real.log 2 := by nlinarith [hlogd, hnR1]
    exact le_trans (mul_le_mul_of_nonneg_left hle (by positivity)) hmain
  have hx : (0:ℝ) < (d:ℝ)^n := pow_pos hdRpos n
  have hEx : Real.log d + Real.log K + (d:ℝ)*Real.log 2 - (n:ℝ)*Real.log d ≤
      A * ((d:ℝ)^n)⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hconst (by positivity : (0:ℝ) ≤ ((d:ℝ)^n)⁻¹)
    have hid : (d:ℝ)^n * (Real.log d + Real.log K + (d:ℝ)*Real.log 2 - (n:ℝ)*Real.log d) * ((d:ℝ)^n)⁻¹
        = Real.log d + Real.log K + (d:ℝ)*Real.log 2 - (n:ℝ)*Real.log d := by
      rw [mul_assoc,
        mul_comm (Real.log d + Real.log K + (d:ℝ)*Real.log 2 - (n:ℝ)*Real.log d) ((d:ℝ)^n)⁻¹,
        ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hx), one_mul]
    rwa [hid] at h
  have hPn' : ((d:ℝ)^n)⁻¹ ≤ P := by
    have h := hPn
    rwa [zpow_neg, zpow_natCast] at h
  have hy1 : 1 ≤ P * (d:ℝ)^n := by
    have h := mul_le_mul_of_nonneg_right hPn' (le_of_lt hx)
    rwa [inv_mul_cancel₀ (ne_of_gt hx)] at h
  have hlogP : Real.log P + (n:ℝ) * Real.log d = Real.log (P * (d:ℝ)^n) := by
    rw [Real.log_mul (ne_of_gt hP) (ne_of_gt hx), Real.log_pow]
  have hxy : ((d:ℝ)^n)⁻¹ * (P * (d:ℝ)^n) = P := by
    rw [← mul_assoc, mul_comm ((d:ℝ)^n)⁻¹ P, mul_assoc, inv_mul_cancel₀ (ne_of_gt hx), mul_one]
  have hAx : 1 ≤ A * ((d:ℝ)^n)⁻¹ := by
    have h1 : (d:ℝ)^n * ((d:ℝ)^n)⁻¹ ≤ A * ((d:ℝ)^n)⁻¹ :=
      mul_le_mul_of_nonneg_right hA_ge (by positivity)
    rwa [mul_inv_cancel₀ (ne_of_gt hx)] at h1
  -- the `P`-dependent step: `E + log P ≤ A P`
  have hAP : Real.log d + Real.log K + (d:ℝ) * Real.log 2 + Real.log P ≤ A * P := by
    set y : ℝ := P * (d:ℝ)^n with hy
    have hy1' : 1 ≤ y := hy1
    have hlogy : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have hmul : y - 1 ≤ A * ((d:ℝ)^n)⁻¹ * (y - 1) := by
      have hnn : (0:ℝ) ≤ y - 1 := by linarith
      calc y - 1 = 1 * (y - 1) := by ring
        _ ≤ A * ((d:ℝ)^n)⁻¹ * (y - 1) := mul_le_mul_of_nonneg_right hAx hnn
    have hEid : Real.log d + Real.log K + (d:ℝ) * Real.log 2 + Real.log P
        = (Real.log d + Real.log K + (d:ℝ) * Real.log 2 - (n:ℝ) * Real.log d) + Real.log y := by
      rw [← hlogP]; ring
    have hAPeq : A * P = A * ((d:ℝ)^n)⁻¹ * y := by
      rw [← hxy]; ring
    rw [hEid, hAPeq]
    linarith [hEx, hlogy, hmul]
  have hmain1 : Real.log d + Real.log σ₁ + (d:ℝ)*σ₁ + (d:ℝ)*Real.log 2 ≤
      (Real.log d + Real.log K + (d:ℝ)*Real.log 2) + Real.log P + ((d:ℝ)*K)*P := by
    linarith [hlogσ, hdσ]
  calc Real.log d + Real.log σ₁ + (d:ℝ)*σ₁ + (d:ℝ)*Real.log 2
      ≤ (Real.log d + Real.log K + (d:ℝ)*Real.log 2) + Real.log P + ((d:ℝ)*K)*P := hmain1
    _ = ((Real.log d + Real.log K + (d:ℝ) * Real.log 2) + Real.log P) + ((d:ℝ)*K)*P := by ring
    _ ≤ A*P + ((d:ℝ)*K)*P := by linarith [hAP]
    _ = (A + (d:ℝ)*K) * P := by ring
    _ = BakerWustholz.C n d * max (Real.log B) (1/(d:ℝ)) * P := by rw [hA]; ring

end Work.BW
