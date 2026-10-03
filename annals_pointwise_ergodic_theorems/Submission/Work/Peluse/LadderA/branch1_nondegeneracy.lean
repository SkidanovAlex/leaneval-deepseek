import Mathlib
import Submission.Work.Peluse.ladderA_defs

namespace Work.Peluse.LadderA

/-- **Non-degeneracy of the first ladder branch.**  From the two geometric inputs

* `hC : A / c₁^{Kh} ≤ C₀`, i.e. `A ≤ C₀ c₁^{Kh}` (`A` is produced from `C₀` by the trimming
  factor `c₁^{Kh} > 0`), and
* `hii : C₀ ≤ M₂ (γγ')^K`, i.e. `C₀` sits below the decayed mass `M₂ (γγ')^K`,

together with the index bookkeeping `K ≥ 2^m · Kh` and `Kh ≤ K` and the normalisations
`0 < γ ≤ 1`, `0 < γ' ≤ 1`, we may upgrade the exponent pair `(K, 1)` of the decay `(γγ')^K` to
the exponent pair `(2^m·Kh, Kh)` of `(γ^{2^m}γ')^{Kh}`:

`A ≤ M₂ (γγ')^K c₁^{Kh} ≤ M₂ (c₁ γ^{2^m} γ')^{Kh}`.

The monotonicity `γ^K ≤ γ^{2^m Kh}` and `γ'^K ≤ γ'^{Kh}` is exactly
`pow_le_pow_of_le_one` (`0 < γ ≤ 1` makes `γ ↦ γ^j` antitone), and it is legitimate because
`2^m ≥ 1` gives `K ≥ 2^m Kh ≥ Kh`; the two exponents `2^m·Kh` and `Kh` recombine into the single
power `(·)^{Kh}` by distributivity of the exponent over the product.

(Note `M₂ > 0` is needed to multiply the decay inequality by `M₂`; it is *derived*, not assumed:
`hii` and `1 ≤ C₀` give `M₂ (γγ')^K > 0`, and `(γγ')^K > 0`.) -/
theorem branch1_nondegeneracy {γ γ' M₂ C₀ A c₁ : ℝ} {K Kh m : ℕ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hγ' : 0 < γ') (hγ'1 : γ' ≤ 1) (hC₀ : 1 ≤ C₀) (hc₁ : 0 < c₁)
    (hA : 0 < A) (hK₁ : 2 ^ m * Kh ≤ K) (hK₂ : Kh ≤ K)
    (hii : C₀ ≤ M₂ * (γ * γ') ^ K) (hC : A / c₁ ^ Kh ≤ C₀) :
    A ≤ M₂ * (c₁ * γ ^ (2 ^ m) * γ') ^ Kh := by
  -- `hA` (positivity of `A`) belongs to the interface but is not needed numerically.
  have _hA := hA
  have hc1p : 0 < c₁ ^ Kh := pow_pos hc₁ Kh
  have hγγK : 0 < (γ * γ') ^ K := pow_pos (mul_pos hγ hγ') K
  -- `M₂ > 0`, derived from `hii` and `1 ≤ C₀`.
  have hM₂ : 0 < M₂ := by
    have h1 : 0 < C₀ := lt_of_lt_of_le (by norm_num) hC₀
    have h2 : 0 < M₂ * (γ * γ') ^ K := lt_of_lt_of_le h1 hii
    exact pos_of_mul_pos_left h2 (le_of_lt hγγK)
  -- `A ≤ C₀ c₁^{Kh}`, then `A ≤ M₂ (γγ')^K c₁^{Kh}`.
  have hA1 : A ≤ C₀ * c₁ ^ Kh := (div_le_iff₀ hc1p).mp hC
  have hA2 : A ≤ M₂ * (γ * γ') ^ K * c₁ ^ Kh := by
    calc A ≤ C₀ * c₁ ^ Kh := hA1
      _ ≤ M₂ * (γ * γ') ^ K * c₁ ^ Kh :=
          mul_le_mul_of_nonneg_right hii (le_of_lt hc1p)
  -- The power comparison `(γγ')^K ≤ γ^{2^m Kh} γ'^{Kh}`.
  have hpow' : (γ * γ') ^ K ≤ γ ^ (2 ^ m * Kh) * γ' ^ Kh := by
    rw [mul_pow]
    exact mul_le_mul
      (pow_le_pow_of_le_one (le_of_lt hγ) hγ1 hK₁)
      (pow_le_pow_of_le_one (le_of_lt hγ') hγ'1 hK₂)
      (by positivity) (by positivity)
  calc A ≤ M₂ * (γ * γ') ^ K * c₁ ^ Kh := hA2
    _ = M₂ * c₁ ^ Kh * ((γ * γ') ^ K) := by ring
    _ ≤ M₂ * c₁ ^ Kh * (γ ^ (2 ^ m * Kh) * γ' ^ Kh) :=
        mul_le_mul_of_nonneg_left hpow' (le_of_lt (mul_pos hM₂ hc1p))
    _ = M₂ * (c₁ * γ ^ (2 ^ m) * γ') ^ Kh := by
        rw [mul_pow, mul_pow, ← pow_mul]
        ring

end Work.Peluse.LadderA
