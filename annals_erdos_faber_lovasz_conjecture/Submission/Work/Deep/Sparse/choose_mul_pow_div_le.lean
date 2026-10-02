import Submission.Work.Deep.Sparse.Prelude
/-!
# A binomial-power bound

For `0 < k` and `0 < K`,
`C(k,K) * (C(a,j)^K / k^(j*K)) ≤ (k * ((a/k)^j / j!))^K / K!`.

Both sides are `k^K a^(j*K) / (K! (j!)^K k^(j*K))` once the denominators are cleared,
so the inequality reduces to the two standard bounds `C(n,r) ≤ n^r / r!`
(`Nat.choose_le_pow_div`).
-/

namespace Work.Deep.Sparse

set_option linter.unusedVariables false in
theorem choose_mul_pow_div_le {k K j a : ℕ} (hk : 0 < k) (hK : 0 < K) : (k.choose K : ℝ) * (((a.choose j : ℝ)) ^ K / (k : ℝ) ^ (j * K)) ≤ ((k : ℝ) * (((a : ℝ) / (k : ℝ)) ^ j / (j.factorial : ℝ))) ^ K / (K.factorial : ℝ) := by
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hKf : (0:ℝ) < (K.factorial : ℝ) := by positivity
  have hjf : (0:ℝ) < (j.factorial : ℝ) := by positivity
  -- `C(k,K) * K! ≤ k^K`
  have h1 : (k.choose K : ℝ) * (K.factorial : ℝ) ≤ (k:ℝ)^K := by
    calc (k.choose K : ℝ) * (K.factorial : ℝ)
        ≤ ((k:ℝ)^K / (K.factorial:ℝ)) * (K.factorial:ℝ) :=
          mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div K k) hKf.le
      _ = (k:ℝ)^K := div_mul_cancel₀ _ (ne_of_gt hKf)
  -- `C(a,j) * j! ≤ a^j`
  have h2 : (a.choose j : ℝ) * (j.factorial : ℝ) ≤ (a:ℝ)^j := by
    calc (a.choose j : ℝ) * (j.factorial : ℝ)
        ≤ ((a:ℝ)^j / (j.factorial:ℝ)) * (j.factorial:ℝ) :=
          mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div j a) hjf.le
      _ = (a:ℝ)^j := div_mul_cancel₀ _ (ne_of_gt hjf)
  have h3 : ((a.choose j : ℝ) * (j.factorial:ℝ))^K ≤ ((a:ℝ)^j)^K :=
    pow_le_pow_left₀ (by positivity) h2 K
  -- after multiplying out the denominators, this is all that is needed
  have key : (k.choose K : ℝ) * ((a.choose j : ℝ)^K) * (K.factorial : ℝ) * ((j.factorial : ℝ)^K)
      ≤ (k:ℝ)^K * (a:ℝ)^(j*K) := by
    calc (k.choose K : ℝ) * ((a.choose j : ℝ)^K) * (K.factorial : ℝ) * ((j.factorial : ℝ)^K)
        = ((k.choose K : ℝ) * (K.factorial : ℝ)) * (((a.choose j : ℝ) * (j.factorial : ℝ))^K) := by
          rw [mul_pow]; ring
      _ ≤ ((k:ℝ)^K) * (((a.choose j : ℝ) * (j.factorial : ℝ))^K) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ ((k:ℝ)^K) * (((a:ℝ)^j)^K) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (k:ℝ)^K * (a:ℝ)^(j*K) := by rw [pow_mul]
  -- expand the right-hand side over a common denominator
  have hR : ((k:ℝ) * (((a:ℝ)/(k:ℝ))^j / (j.factorial:ℝ)))^K * (k:ℝ)^(j*K)
      = (k:ℝ)^K * (a:ℝ)^(j*K) / ((j.factorial:ℝ)^K) := by
    simp only [mul_pow, div_pow, ← pow_mul]
    field_simp
  conv_lhs => rw [← mul_div_assoc]
  rw [div_le_div_iff₀ (pow_pos hkR _) hKf, hR, le_div_iff₀ (pow_pos hjf K)]
  exact key

end Work.Deep.Sparse
