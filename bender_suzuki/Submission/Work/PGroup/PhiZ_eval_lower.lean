import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A lower bound for `Φ_D(2 ^ k)`

`PhiZ_eval_lower` states that for `2 ≤ D` and `1 ≤ k`,

`2 ^ ((k - 1) * φ(D)) < Φ_D(2 ^ k)`.

The mathematical content is the classical inequality `(q - 1) ^ φ(n) < Φ_n(q)` for `2 ≤ n`,
`1 < q` (Mathlib's `Polynomial.sub_one_pow_totient_lt_cyclotomic_eval`, which is proved by
comparing `|q - ζ|` with `q - 1` over the primitive `n`-th roots of unity `ζ`), applied at
`q = 2 ^ k`, together with the elementary estimate `2 ^ (k - 1) ≤ 2 ^ k - 1` for `k ≥ 1`.
-/

namespace Work.PGroup

lemma PhiZ_eval_lower {D k : ℕ} (hD : 2 ≤ D) (hk : 1 ≤ k) :
    (2 : ℤ) ^ ((k - 1) * D.totient) < (Polynomial.cyclotomic D ℤ).eval ((2 : ℤ) ^ k) := by
  -- Work over `ℝ`, where the cyclotomic inequality is available.
  have hq : (1 : ℝ) < (2 : ℝ) ^ k := by
    calc (1 : ℝ) = (2 : ℝ) ^ 0 := (pow_zero 2).symm
      _ < (2 : ℝ) ^ k := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hmain := Polynomial.sub_one_pow_totient_lt_cyclotomic_eval (n := D) (q := (2 : ℝ) ^ k) hD hq
  -- The evaluation over `ℝ` is the cast of the evaluation over `ℤ`.
  have hcast : ((Polynomial.eval ((2 : ℤ) ^ k) (Polynomial.cyclotomic D ℤ) : ℤ) : ℝ)
      = (Polynomial.cyclotomic D ℝ).eval ((2 : ℝ) ^ k) := by
    have h := Polynomial.cyclotomic.eval_apply ((2 : ℤ) ^ k) D (Int.castRingHom ℝ)
    have hx : (Int.castRingHom ℝ) ((2 : ℤ) ^ k) = (2 : ℝ) ^ k := by norm_num [Int.cast_pow]
    rw [hx] at h
    exact h.symm
  -- `2 ^ (k - 1) ≤ 2 ^ k - 1` for `k ≥ 1`.
  have hbase : (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ k - 1 := by
    have hks : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have h2k : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by rw [← pow_succ, hks]
    have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k - 1) := one_le_pow₀ (by norm_num)
    rw [h2k]; linarith
  have hpow : ((2 : ℝ) ^ (k - 1)) ^ D.totient ≤ ((2 : ℝ) ^ k - 1) ^ D.totient :=
    pow_le_pow_left₀ (by positivity) hbase _
  have hAeq : ((2 : ℤ) ^ ((k - 1) * D.totient) : ℝ) = ((2 : ℝ) ^ (k - 1)) ^ D.totient := by
    rw [← pow_mul]; push_cast; ring
  have hchain : ((2 : ℤ) ^ ((k - 1) * D.totient) : ℝ)
      < ((Polynomial.eval ((2 : ℤ) ^ k) (Polynomial.cyclotomic D ℤ) : ℤ) : ℝ) := by
    calc ((2 : ℤ) ^ ((k - 1) * D.totient) : ℝ)
        = ((2 : ℝ) ^ (k - 1)) ^ D.totient := hAeq
      _ ≤ ((2 : ℝ) ^ k - 1) ^ D.totient := hpow
      _ < (Polynomial.cyclotomic D ℝ).eval ((2 : ℝ) ^ k) := hmain
      _ = ((Polynomial.eval ((2 : ℤ) ^ k) (Polynomial.cyclotomic D ℤ) : ℤ) : ℝ) := hcast.symm
  exact_mod_cast hchain

end Work.PGroup
