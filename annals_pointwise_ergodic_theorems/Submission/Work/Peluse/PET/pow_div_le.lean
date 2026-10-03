import Mathlib

namespace Work.Peluse.PET

/-- Elementary arithmetic bound: since `γ/1000 · 2 = γ/500 ≤ γ/9 ≤ β` and
`2^(n-1) ≤ 2^n`, we get `(γ/1000)^n · 2^(n-1) ≤ (γ/1000)^n · 2^n
= ((γ/1000)·2)^n ≤ β^n`, which after dividing by `2^(n-1) > 0` is the claim. -/
theorem pow_div_le {γ β : ℝ} {n : ℕ} (hn : 1 ≤ n) (hγ : 0 ≤ γ) (hβ : γ / 9 ≤ β) :
    (γ / 1000) ^ n ≤ β ^ n / 2 ^ (n - 1) := by
  have h2pos : (0:ℝ) < 2 ^ (n - 1) := by positivity
  rw [le_div_iff₀ h2pos]
  have h2n : (2:ℝ) ^ (n - 1) ≤ 2 ^ n := by
    apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
    omega
  have ha : 0 ≤ (γ/1000)^n := by positivity
  have step1 : (γ/1000)^n * 2^(n-1) ≤ (γ/1000)^n * 2^n :=
    mul_le_mul_of_nonneg_left h2n ha
  have hγ9 : γ/500 ≤ β := by
    have h1 : γ/500 ≤ γ/9 := by
      apply div_le_div_of_nonneg_left hγ (by norm_num) (by norm_num)
    linarith
  have hcast : (γ/1000)*(2:ℝ) = γ/500 := by ring
  have step3 : ((γ/1000)*(2:ℝ))^n ≤ β^n := by
    rw [hcast]
    exact pow_le_pow_left₀ (by positivity) hγ9 n
  calc (γ/1000)^n * 2^(n-1)
      ≤ (γ/1000)^n * 2^n := step1
    _ = ((γ/1000)*(2:ℝ))^n := by rw [mul_pow]
    _ ≤ β^n := step3

end Work.Peluse.PET
