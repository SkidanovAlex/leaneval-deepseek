import Mathlib
import Submission.Work.Peluse.ladderA_defs

namespace Work.Peluse.LadderA

theorem branch2_impossible {γ γ' C₀ A c₁ : ℝ} {K Kh m : ℕ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hγ' : 0 < γ') (hC₀ : 1 ≤ C₀) (hc₁ : 0 < c₁) (hA : 0 < A)
    (hK : 2 ^ m * Kh + 1 ≤ K)
    (hi : C₀ * γ' ≤ γ ^ K) (hC : A / c₁ ^ Kh ≤ C₀) :
    γ' ≤ c₁ ^ Kh * γ ^ (2 ^ m * Kh) / A := by
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀
  have hKhpos : 0 < c₁ ^ Kh := pow_pos hc₁ Kh
  -- `A ≤ C₀ * c₁^Kh`, i.e. `A * c₁^{-Kh} ≤ C₀`
  have hAKh : A ≤ C₀ * c₁ ^ Kh := (div_le_iff₀ hKhpos).mp hC
  -- the exponent `2^m * Kh` is below `K`
  have hle : 2 ^ m * Kh ≤ K := by omega
  -- and since `0 < γ ≤ 1`, this makes `γ^K` smaller
  have hpow : γ ^ K ≤ γ ^ (2 ^ m * Kh) :=
    pow_le_pow_of_le_one (le_of_lt hγ) hγ1 hle
  have hgp : (0 : ℝ) < γ ^ (2 ^ m * Kh) := pow_pos hγ _
  -- `γ' ≤ γ^K / C₀`
  have h1 : γ' ≤ γ ^ K / C₀ := by
    rw [le_div_iff₀ hC₀pos]
    nlinarith [hi]
  -- monotonicity of the division by `C₀ > 0`
  have h2 : γ ^ K / C₀ ≤ γ ^ (2 ^ m * Kh) / C₀ :=
    div_le_div_of_nonneg_right hpow (le_of_lt hC₀pos)
  -- the constant swap: `1 / C₀ ≤ c₁^Kh / A`
  have h3 : γ ^ (2 ^ m * Kh) / C₀ ≤ c₁ ^ Kh * γ ^ (2 ^ m * Kh) / A := by
    rw [div_le_div_iff₀ hC₀pos hA]
    nlinarith [hAKh, hgp]
  linarith [h1, h2, h3]

end Work.Peluse.LadderA
