import Mathlib

namespace Work.BourgainPlan.Maximal

/-- The Weyl bracket `1/q + 1/N + 1/N^{d-1} + q/N^d` at `N = 2^n` is at most `5·n^{−γ}` whenever the Dirichlet denominator `q` satisfies `n^γ ≤ q`, `q ≤ 2 n^{−γ} 2^{nd}` and `2^{−n} ≤ n^{−γ}`; raising to the Weyl exponent `σ > 0` turns this into `5^σ · n^{−(γσ)}`. -/
lemma mst_bracket_rpow (d : ℕ) (hd : 2 ≤ d) (γ σ : ℝ) (hσ : 0 < σ) (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q)
    (hqγ : (n:ℝ)^γ ≤ (q:ℝ))
    (hqN : (q:ℝ) ≤ 2 * (n:ℝ)^(-γ) * (2:ℝ)^((n:ℝ) * (d:ℝ)))
    (hNγ : (2:ℝ)^(-(n:ℝ)) ≤ (n:ℝ)^(-γ)) :
    (1/(q:ℝ) + 1/(2:ℝ)^n + 1/((2:ℝ)^n)^(d-1) + (q:ℝ)/((2:ℝ)^n)^d)^σ
      ≤ 5^σ * (n:ℝ)^(-(γ*σ)) := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hnR0 : (0:ℝ) ≤ (n:ℝ) := le_of_lt hnR
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  -- `1/2^n = 2^{-n}`
  have hb_eq : 1/(2:ℝ)^n = (2:ℝ)^(-(n:ℝ)) := by
    rw [one_div, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
  -- first term: `1/q ≤ n^{-γ}`
  have h1q : 1/(q:ℝ) ≤ (n:ℝ)^(-γ) := by
    have hp : (0:ℝ) < (n:ℝ)^γ := Real.rpow_pos_of_pos hnR γ
    rw [one_div, Real.rpow_neg hnR0]
    exact inv_anti₀ hp hqγ
  -- second term: `1/2^n ≤ n^{-γ}`
  have hb : 1/(2:ℝ)^n ≤ (n:ℝ)^(-γ) := hb_eq.trans_le hNγ
  -- third term: `1/N^{d-1} ≤ 1/N ≤ n^{-γ}`
  have hc : 1/((2:ℝ)^n)^(d-1) ≤ (n:ℝ)^(-γ) := by
    have h2n1 : (1:ℝ) ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    have h2npos : (0:ℝ) < (2:ℝ)^n := by positivity
    have h2npow : (2:ℝ)^n ≤ ((2:ℝ)^n)^(d-1) := by
      calc (2:ℝ)^n = ((2:ℝ)^n)^1 := (pow_one _).symm
        _ ≤ ((2:ℝ)^n)^(d-1) := pow_le_pow_right₀ h2n1 (by omega)
    exact (one_div_le_one_div_of_le h2npos h2npow).trans hb
  -- `2^{n d} = (2^n)^d`
  have h2nd : (2:ℝ)^((n:ℝ)*(d:ℝ)) = ((2:ℝ)^n)^d := by
    rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast, Real.rpow_natCast]
  have hqN' : (q:ℝ) ≤ 2 * (n:ℝ)^(-γ) * ((2:ℝ)^n)^d := by
    rw [h2nd] at hqN; exact hqN
  -- fourth term: `q/N^d ≤ 2 n^{-γ}`
  have hqdiv : (q:ℝ)/((2:ℝ)^n)^d ≤ 2 * (n:ℝ)^(-γ) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ((2:ℝ)^n)^d)]
    exact hqN'
  have hsum : 1/(q:ℝ) + 1/(2:ℝ)^n + 1/((2:ℝ)^n)^(d-1) + (q:ℝ)/((2:ℝ)^n)^d
      ≤ 5 * (n:ℝ)^(-γ) := by
    linarith [h1q, hb, hc, hqdiv]
  have hbase_nonneg :
      (0:ℝ) ≤ 1/(q:ℝ) + 1/(2:ℝ)^n + 1/((2:ℝ)^n)^(d-1) + (q:ℝ)/((2:ℝ)^n)^d := by
    positivity
  calc (1/(q:ℝ) + 1/(2:ℝ)^n + 1/((2:ℝ)^n)^(d-1) + (q:ℝ)/((2:ℝ)^n)^d)^σ
      ≤ (5 * (n:ℝ)^(-γ))^σ := Real.rpow_le_rpow hbase_nonneg hsum (le_of_lt hσ)
    _ = 5^σ * ((n:ℝ)^(-γ))^σ := Real.mul_rpow (by norm_num) (Real.rpow_nonneg hnR0 (-γ))
    _ = 5^σ * (n:ℝ)^((-γ)*σ) := by rw [← Real.rpow_mul hnR0]
    _ = 5^σ * (n:ℝ)^(-(γ*σ)) := by rw [show (-γ)*σ = -(γ*σ) by ring]

end Work.BourgainPlan.Maximal
