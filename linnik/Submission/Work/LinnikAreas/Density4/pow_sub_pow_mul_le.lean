import Mathlib

namespace Work.LinnikAreas.Density4

/-- Geometric lower bound: for `0 < q ≤ p` and any `n`,
`n * q^(n-1) * (p - q) ≤ p^n - q^n`.
This is the estimate `p^n - q^n = (p-q) G_n ≥ n (p-q) q^(n-1)` where
`G_n = Σ_{i<n} p^i q^(n-1-i)`, obtained from the geometric identity
`(p - q) G_n = p^n - q^n` and the termwise bound `p^i q^(n-1-i) ≥ q^(n-1)`. -/
private lemma pow_sub_pow_ge {p q : ℝ} (hq : 0 < q) (hqp : q ≤ p) (n : ℕ) :
    (n:ℝ) * q^(n-1) * (p - q) ≤ p^n - q^n := by
  have hq0 : (0:ℝ) ≤ q := hq.le
  have hpq0 : (0:ℝ) ≤ p - q := sub_nonneg.mpr hqp
  -- geometric identity: `(Σ_{i<n} p^i q^(n-1-i)) * (p - q) = p^n - q^n`
  have hgeom : (∑ i ∈ Finset.range n, p^i * q^(n-1-i)) * (p - q) = p^n - q^n := by
    rw [mul_comm, (Commute.all p q).mul_geom_sum₂ n]
  -- termwise bound on the geometric sum
  have hsum : (n:ℝ) * q^(n-1) ≤ ∑ i ∈ Finset.range n, p^i * q^(n-1-i) := by
    have hconst : (∑ _i ∈ Finset.range n, q^(n-1) : ℝ) = (n:ℝ) * q^(n-1) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← hconst]
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ n - 1 := by
      have : i < n := Finset.mem_range.mp hi
      omega
    have hpi : q^i ≤ p^i := pow_le_pow_left₀ hq0 hqp i
    have hqni0 : (0:ℝ) ≤ q^(n-1-i) := pow_nonneg hq0 _
    have hmul : q^i * q^(n-1-i) ≤ p^i * q^(n-1-i) := mul_le_mul_of_nonneg_right hpi hqni0
    have hpow : q^(n-1) = q^i * q^(n-1-i) := by
      rw [← pow_add]
      congr 1
      omega
    linarith [hmul, hpow]
  calc (n:ℝ) * q^(n-1) * (p-q) ≤ (∑ i ∈ Finset.range n, p^i * q^(n-1-i)) * (p-q) :=
        mul_le_mul_of_nonneg_right hsum hpq0
    _ = p^n - q^n := hgeom

/-- For `0 < q ≤ p ≤ 1` and `1 ≤ n`: `n (p^(n+1) - q^(n+1)) ≤ (n+1) (p^n - q^n)`
(equivalently `n ↦ (p^n - q^n)/n` is nonincreasing on `n ≥ 1`). Proof: with `G_n = Σ_{i<n} p^(n-1-i) q^i`
one has `p^n - q^n = (p-q) G_n ≥ n (p-q) q^(n-1)` and
`p^(n+1) - q^(n+1) = p (p^n - q^n) + q^n (p - q)`, whence
`(n+1)(p^n-q^n) - n(p^(n+1)-q^(n+1)) ≥ (p^n-q^n) - n q^n (p-q) ≥ n(p-q)q^(n-1)(1-q) ≥ 0`. -/
theorem pow_sub_pow_mul_le {p q : ℝ} (hq : 0 < q) (hqp : q ≤ p) (hp : p ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    (n:ℝ) * (p^(n+1) - q^(n+1)) ≤ ((n:ℝ) + 1) * (p^n - q^n) := by
  have hq0 : (0:ℝ) ≤ q := hq.le
  have hq1 : q ≤ 1 := le_trans hqp hp
  have hpq0 : (0:ℝ) ≤ p - q := sub_nonneg.mpr hqp
  have hn0 : (0:ℝ) ≤ (n:ℝ) := by
    have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  -- `A := p^n - q^n ≥ 0`
  have hA0 : (0:ℝ) ≤ p^n - q^n := sub_nonneg.mpr (pow_le_pow_left₀ hq0 hqp n)
  -- `n q^(n-1) (p-q) ≤ A`
  have hkey := pow_sub_pow_ge hq hqp n
  -- `q^n ≤ q^(n-1)`, hence `n q^n (p-q) ≤ n q^(n-1) (p-q)`
  have hqn : q^n ≤ q^(n-1) := pow_le_pow_of_le_one hq0 hq1 (Nat.sub_le n 1)
  have hstep2 : (n:ℝ) * q^n * (p-q) ≤ (n:ℝ) * q^(n-1) * (p-q) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqn hn0) hpq0
  -- `1 ≤ n + 1 - n p` since `p ≤ 1`
  have hp1 : (n:ℝ) * p ≤ (n:ℝ) := by
    calc (n:ℝ) * p ≤ (n:ℝ) * 1 := mul_le_mul_of_nonneg_left hp hn0
      _ = (n:ℝ) := mul_one _
  have hX1 : (1:ℝ) ≤ (n:ℝ) + 1 - (n:ℝ) * p := by linarith
  -- hence `A ≤ A * (n + 1 - n p)`
  have hstep1 : p^n - q^n ≤ (p^n - q^n) * ((n:ℝ) + 1 - (n:ℝ) * p) := by
    have h := mul_le_mul_of_nonneg_left hX1 hA0
    simpa using h
  -- key algebraic decomposition of the difference
  have hB : p^(n+1) - q^(n+1) = p * (p^n - q^n) + q^n * (p-q) := by
    rw [pow_succ, pow_succ]; ring
  have hmain : ((n:ℝ) + 1) * (p^n - q^n) - (n:ℝ) * (p * (p^n - q^n) + q^n * (p-q))
      = (p^n - q^n) * ((n:ℝ) + 1 - (n:ℝ) * p) - (n:ℝ) * q^n * (p-q) := by ring
  rw [hB]
  have hchain : (n:ℝ) * q^n * (p-q) ≤ (p^n - q^n) * ((n:ℝ) + 1 - (n:ℝ) * p) :=
    le_trans hstep2 (le_trans hkey hstep1)
  have hfin : (0:ℝ) ≤ (p^n - q^n) * ((n:ℝ) + 1 - (n:ℝ) * p) - (n:ℝ) * q^n * (p-q) :=
    sub_nonneg.mpr hchain
  linarith [hmain, hfin]

end Work.LinnikAreas.Density4
