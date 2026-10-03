import Mathlib
import Submission.Work.Analysis.EndVar.Defs

namespace Work.KMTPlan.A6.MdlLpH

/-- **The lacunary logarithmic levels are unbounded.**

If `a : ℕ → ℝ≥0` is `Λ`-lacunary with `Λ > 1` and `a n ≥ 1` for all `n`, then the logarithmic level
`logN ⌊a n⌋` of `a` takes arbitrarily large values: for every integer `D` there is `n` with
`D ≤ logN ⌊a n⌋`.

Indeed `Λ`-lacunarity together with `a n ≥ 1` gives the multiplicative growth
`Λ * a n ≤ a (n+1)`, hence `Λ ^ n ≤ a n`, so `a n → ∞` geometrically and `⌊a n⌋` eventually exceeds
`2 ^ D`. -/
theorem exists_logN_floor_a_ge {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (D : ℤ) :
    ∃ n : ℕ, D ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
  by_cases hD : D ≤ 0
  · exact ⟨0, le_trans hD (Work.Analysis.EndVar.logN_nonneg _)⟩
  have hDpos : 0 < D := not_le.mp hD
  -- the multiplicative growth `Λ * a n ≤ a (n + 1)`
  have hgr : ∀ n, Λ * a n ≤ a (n + 1) := by
    intro n
    have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    exact le_of_lt ((lt_div_iff₀ hpos).mp (ha n))
  -- the iterated growth `Λ ^ n ≤ a n`
  have hpow : ∀ n : ℕ, Λ ^ n ≤ a n := by
    intro n
    induction n with
    | zero => simpa using ha1 0
    | succ n ih =>
      calc Λ ^ (n + 1) = Λ * Λ ^ n := by rw [pow_succ']
        _ ≤ Λ * a n := mul_le_mul_of_nonneg_left ih (le_of_lt (lt_of_lt_of_le zero_lt_one hΛ.le))
        _ ≤ a (n + 1) := hgr n
  -- the level `2 ^ D.toNat` is eventually exceeded (transported along `ℝ≥0 ⊆ ℝ`)
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((2 ^ D.toNat : ℕ) : ℝ) ≤ (Λ : ℝ) ^ n := by
    have htend := tendsto_pow_atTop_atTop_of_one_lt hΛR
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (htend.eventually (Filter.eventually_ge_atTop (((2 ^ D.toNat : ℕ) : ℝ))))
    exact ⟨N, hN N le_rfl⟩
  -- the same inequality in `ℝ≥0`, via the growth `Λ ^ n ≤ a n`
  have hpowR : (Λ : ℝ) ^ n ≤ (a n : ℝ) := by
    have h1 : (((Λ ^ n : NNReal)) : ℝ) ≤ ((a n : NNReal) : ℝ) := NNReal.coe_le_coe.mpr (hpow n)
    rwa [NNReal.coe_pow] at h1
  have hreal : ((2 ^ D.toNat : ℕ) : ℝ) ≤ (a n : ℝ) := le_trans hn hpowR
  have han : ((2 ^ D.toNat : ℕ) : NNReal) ≤ a n := by
    refine NNReal.coe_le_coe.mp ?_
    simpa using hreal
  have hfloor : 2 ^ D.toNat ≤ Nat.floor (a n) := Nat.le_floor han
  refine ⟨n, ?_⟩
  have hlog : D.toNat ≤ Nat.log 2 (max (Nat.floor (a n)) 2) :=
    Nat.le_log_of_pow_le (by norm_num) (le_trans hfloor (le_max_left _ _))
  have hD' : (D.toNat : ℤ) = D := Int.toNat_of_nonneg hDpos.le
  rw [Work.Analysis.EndVar.logN, ← hD']
  exact_mod_cast hlog

end Work.KMTPlan.A6.MdlLpH
