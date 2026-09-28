import Mathlib

namespace Work.ClassCount

/-- **Real-power bookkeeping for the strong hypothesis.**
Raising `hstrong` to the `n`-th power and clearing the `n`-th roots in `cstar`:
`W ^ (2n+1) · α ^ ((m+1)n) · κ ^ n · (8·5^{n+1}·2^n) ≤ R^n · ccone · n`. -/
private lemma tail_const_le_rpow (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (W α R ccone cstar κ : ℝ)
    (hW : 0 < W) (hα : 0 < α) (hccone : 0 < ccone) (hκ : 0 < κ)
    (hcstar : cstar = ccone ^ (1 / (n : ℝ))
      * ((n : ℝ) / (8 * (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n)) ^ (1 / (n : ℝ)))
    (hstrong : W ^ ((2 * (n : ℝ) + 1) / n) * α ^ (m + 1) * κ ≤ R * cstar) :
    W ^ (2 * n + 1) * α ^ ((m + 1) * n) * κ ^ n * (8 * (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n)
      ≤ R ^ n * ccone * (n : ℝ) := by
  have hn1 : n ≠ 0 := by omega
  have hcast : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn1
  have hLpos : 0 < W ^ ((2 * (n : ℝ) + 1) / (n : ℝ)) * α ^ (m + 1) * κ := by positivity
  have hpow := pow_le_pow_left₀ hLpos.le hstrong n
  have hWpow : (W ^ ((2 * (n : ℝ) + 1) / (n : ℝ))) ^ n = W ^ (2 * n + 1) := by
    rw [← Real.rpow_natCast (W ^ ((2 * (n : ℝ) + 1) / (n : ℝ))) n,
        ← Real.rpow_mul hW.le ((2 * (n : ℝ) + 1) / (n : ℝ)) (n : ℝ)]
    have he : (2 * (n : ℝ) + 1) / (n : ℝ) * (n : ℝ) = ((2 * n + 1 : ℕ) : ℝ) := by
      rw [div_mul_cancel₀ _ hcast]; push_cast; ring
    rw [he, Real.rpow_natCast]
  have hαpow : (α ^ (m + 1)) ^ n = α ^ ((m + 1) * n) := by rw [pow_mul]
  have hL : (W ^ ((2 * (n : ℝ) + 1) / (n : ℝ)) * α ^ (m + 1) * κ) ^ n
      = W ^ (2 * n + 1) * α ^ ((m + 1) * n) * κ ^ n := by
    rw [mul_pow, mul_pow, hWpow, hαpow]
  have hbase : 0 ≤ (n : ℝ) / (8 * (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n) := by positivity
  have hcc : (ccone ^ (1 / (n : ℝ))) ^ n = ccone := by
    rw [one_div]; exact Real.rpow_inv_natCast_pow hccone.le hn1
  have hbb : (((n : ℝ) / (8 * (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n)) ^ (1 / (n : ℝ))) ^ n
      = (n : ℝ) / (8 * (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n) := by
    rw [one_div]; exact Real.rpow_inv_natCast_pow hbase hn1
  have hRhs : (R * cstar) ^ n
      = R ^ n * ccone * (n : ℝ) / (8 * (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n) := by
    rw [hcstar, mul_pow, mul_pow, hcc, hbb]; ring
  have hkey0 : W ^ (2 * n + 1) * α ^ ((m + 1) * n) * κ ^ n
      ≤ R ^ n * ccone * (n : ℝ) / (8 * (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n) := by
    rw [← hL, ← hRhs]; exact hpow
  have hDpos : (0 : ℝ) < 8 * (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n := by positivity
  have hkey := mul_le_mul_of_nonneg_right hkey0 hDpos.le
  rw [div_mul_cancel₀ _ hDpos.ne'] at hkey
  exact hkey

/-- **Arithmetic bookkeeping for the tail bound.**  From the cleared form of the strong
hypothesis, multiply by `R` and divide by `8 α^n W^{n+1} · n`. -/
private lemma tail_const_le_arith (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (W α R T₀ ccone κ : ℝ)
    (hW : 0 < W) (hα : 0 < α) (hR : 0 < R)
    (hT0eq : T₀ = W * α ^ m * κ)
    (hkey : W ^ (2 * n + 1) * α ^ ((m + 1) * n) * κ ^ n
        * (8 * (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n) ≤ R ^ n * ccone * (n : ℝ)) :
    (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n * R * T₀ ^ n / (n : ℝ)
      ≤ ccone * R ^ (n + 1) / (8 * α ^ n * W ^ (n + 1)) := by
  have e1 : T₀ ^ n = W ^ n * α ^ (m * n) * κ ^ n := by
    rw [hT0eq, mul_pow, mul_pow, ← pow_mul]
  have e2 : W ^ (2 * n + 1) = W ^ n * W ^ (n + 1) := by
    rw [show 2 * n + 1 = n + (n + 1) by ring, pow_add]
  have e3 : α ^ ((m + 1) * n) = α ^ (m * n) * α ^ n := by
    rw [show (m + 1) * n = m * n + n by ring, pow_add]
  have hm := mul_le_mul_of_nonneg_left hkey hR.le
  have hLHS_eq : R * (W ^ (2 * n + 1) * α ^ ((m + 1) * n) * κ ^ n
        * (8 * (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n))
      = 8 * α ^ n * W ^ (n + 1) * ((5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n * R * T₀ ^ n) := by
    rw [e1, e2, e3]; ring
  have hRHS_eq : R * (R ^ n * ccone * (n : ℝ)) = (n : ℝ) * ccone * R ^ (n + 1) := by
    rw [pow_succ]; ring
  rw [hLHS_eq, hRHS_eq] at hm
  have hpos : (0 : ℝ) < 8 * α ^ n * W ^ (n + 1) := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [div_le_iff₀ hnpos]
  rw [show ccone * R ^ (n + 1) / (8 * α ^ n * W ^ (n + 1)) * (n : ℝ)
        = (ccone * R ^ (n + 1) * (n : ℝ)) / (8 * α ^ n * W ^ (n + 1)) by ring]
  rw [le_div_iff₀ hpos]
  nlinarith [hm]

/-- **Constant bookkeeping for the tail bound.**  Suppose `T₀ = W α^m κ` with `κ > 0` and
`W^{(2n+1)/n} α^{m+1} κ ≤ R · cstar` with `cstar = ccone^{1/n} (n/(8·5^{n+1}·2^n))^{1/n}`.
Then `5^{n+1} 2^n R T₀^n / n ≤ ccone R^{n+1} / (8 α^n W^{n+1})`.

Route: raise `hstrong` to the `n`-th power (both sides are nonnegative, using `0 < κ`):
`W^{2n+1} α^{(m+1)n} κ^n ≤ R^n cstar^n = R^n ccone n/(8·5^{n+1}2^n)` using
`(x^{1/n})^n = x` (`Real.rpow_inv_natCast_pow`), `mul_pow`, `pow_mul`, `Real.rpow_mul`,
`Real.rpow_natCast`; multiply by `8·5^{n+1}2^n R/(n)` and rewrite `T₀^n = W^n α^{mn} κ^n`;
divide by `α^n W^{n+1}`. -/
theorem tail_const_le (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (W α R T₀ ccone cstar κ : ℝ)
    (hW : 0 < W) (hα : 0 < α) (hR : 0 < R) (hccone : 0 < ccone) (hκ : 0 < κ)
    (hT0eq : T₀ = W * α ^ m * κ)
    (hcstar : cstar = ccone ^ (1 / (n : ℝ))
      * ((n : ℝ) / (8 * (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n)) ^ (1 / (n : ℝ)))
    (hstrong : W ^ ((2 * (n : ℝ) + 1) / n) * α ^ (m + 1) * κ ≤ R * cstar) :
    (5 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n * R * T₀ ^ n / (n : ℝ)
      ≤ ccone * R ^ (n + 1) / (8 * α ^ n * W ^ (n + 1)) := by
  have hkey := tail_const_le_rpow n hn m W α R ccone cstar κ hW hα hccone hκ hcstar hstrong
  exact tail_const_le_arith n hn m W α R T₀ ccone κ hW hα hR hT0eq hkey

end Work.ClassCount
