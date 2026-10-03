import Mathlib

namespace Work.BourgainPlan.IonescuWainger

/-- Elementary arithmetic identity used to normalise the constants in the Ionescu–Wainger
decoupling bookkeeping: the `(card (S → Fin k))^(2r-1) · card (S → Fin k)` factor equals
`(k^|S|)^(2r)`, and `k^k / (k! · k^|S|) · k^|S| = k^k / k!`. -/
theorem const_arith {α : Type*} [DecidableEq α] (S : Finset α) (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r)
    {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ENNReal.ofReal (((k ^ k : ℕ) : ℝ) / ((k.factorial * k ^ S.card : ℕ) : ℝ)) ^ (2 * r)
        * ((Fintype.card (S → Fin k) : ENNReal) ^ (2 * r - 1) * (Fintype.card (S → Fin k) : ENNReal))
        * ENNReal.ofReal (C₀ ^ (r * k))
      = ENNReal.ofReal (C₀ ^ (r * k) * ((k : ℝ) ^ k / (k.factorial : ℝ)) ^ (2 * r)) := by
  -- abbreviations for the three real constants appearing in the identity
  set a : ℝ := ((k ^ k : ℕ) : ℝ) / ((k.factorial * k ^ S.card : ℕ) : ℝ) with ha
  set b : ℝ := ((k ^ S.card : ℕ) : ℝ) with hb
  set c : ℝ := C₀ ^ (r * k) with hc
  have ha_nn : 0 ≤ a := by rw [ha]; positivity
  have hb_nn : 0 ≤ b := by rw [hb]; positivity
  have hc_nn : 0 ≤ c := by rw [hc]; positivity
  -- the cardinality of `S → Fin k`
  have hcard : Fintype.card (S → Fin k) = k ^ S.card := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have hK : (Fintype.card (S → Fin k) : ENNReal) = ENNReal.ofReal b := by
    rw [hcard, hb]
    exact (ENNReal.ofReal_natCast _).symm
  -- `x^(2r-1) * x = x^(2r)` since `1 ≤ r`
  have hpow : ENNReal.ofReal b ^ (2 * r - 1) * ENNReal.ofReal b = ENNReal.ofReal b ^ (2 * r) := by
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ 2 * r by omega)]
  -- the two real `k`-factors combine
  have hab : a * b = (k : ℝ) ^ k / (k.factorial : ℝ) := by
    rw [ha, hb]
    push_cast
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hfac : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp
  have hreal : a ^ (2 * r) * b ^ (2 * r) * c = c * ((k : ℝ) ^ k / (k.factorial : ℝ)) ^ (2 * r) := by
    rw [← mul_pow, hab, mul_comm]
  -- move everything inside a single `ENNReal.ofReal`
  have hLHS : ENNReal.ofReal a ^ (2 * r)
        * ((Fintype.card (S → Fin k) : ENNReal) ^ (2 * r - 1) * (Fintype.card (S → Fin k) : ENNReal))
        * ENNReal.ofReal c = ENNReal.ofReal (a ^ (2 * r) * b ^ (2 * r) * c) := by
    rw [hK, hpow, ← ENNReal.ofReal_pow ha_nn, ← ENNReal.ofReal_pow hb_nn,
      ← ENNReal.ofReal_mul (pow_nonneg ha_nn _),
      ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg ha_nn _) (pow_nonneg hb_nn _))]
  rw [hLHS, hreal]

end Work.BourgainPlan.IonescuWainger
