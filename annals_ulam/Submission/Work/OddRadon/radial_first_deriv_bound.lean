import Mathlib

/-!
# Bound on the first radial derivative `R'`

Sibling of `radial_second_deriv_bound`.  We solve the (linear) equation for `R'`

```
((2n+2)(2n+1) (R^{2n+1} r^{2n} + R^{2n} r^{2n+1})) R'
   = (2n+1) r^{2n} a + (2n+2) r^{2n+1} b
```

with `R, r ∈ [7/8, 9/8]` and `|a|, |b| < ε`, and show that `|R'| ≤ C ε` for a
constant `C = C(n) > 0` depending only on `n`.

The denominator is bounded below by `(2n+2)(2n+1) · 2 · (7/8)^{4n+1}`, while the
numerator is bounded above by `(4n+3) (9/8)^{2n+1} ε`.
-/

namespace Work.OddRadon

/-- The first product `R^{2n+1} r^{2n}` dominates `(7/8)^{4n+1}` on the box. -/
private lemma pow_prod_lower_left (n : ℕ) {R r : ℝ} (hR1 : 7/8 ≤ R) (hr1 : 7/8 ≤ r) :
    (7/8 : ℝ) ^ (4 * n + 1) ≤ R ^ (2 * n + 1) * r ^ (2 * n) := by
  have h1 : (7/8 : ℝ) ^ (2 * n + 1) ≤ R ^ (2 * n + 1) :=
    pow_le_pow_left₀ (by norm_num) hR1 _
  have h2 : (7/8 : ℝ) ^ (2 * n) ≤ r ^ (2 * n) :=
    pow_le_pow_left₀ (by norm_num) hr1 _
  have key : (7/8 : ℝ) ^ (2 * n + 1) * (7/8 : ℝ) ^ (2 * n) = (7/8 : ℝ) ^ (4 * n + 1) := by
    rw [← pow_add]; congr 1; ring
  calc (7/8 : ℝ) ^ (4 * n + 1)
      = (7/8 : ℝ) ^ (2 * n + 1) * (7/8 : ℝ) ^ (2 * n) := key.symm
    _ ≤ R ^ (2 * n + 1) * r ^ (2 * n) := mul_le_mul h1 h2 (by positivity) (by positivity)

/-- The second product `R^{2n} r^{2n+1}` dominates `(7/8)^{4n+1}` on the box. -/
private lemma pow_prod_lower_right (n : ℕ) {R r : ℝ} (hR1 : 7/8 ≤ R) (hr1 : 7/8 ≤ r) :
    (7/8 : ℝ) ^ (4 * n + 1) ≤ R ^ (2 * n) * r ^ (2 * n + 1) := by
  have h1 : (7/8 : ℝ) ^ (2 * n) ≤ R ^ (2 * n) :=
    pow_le_pow_left₀ (by norm_num) hR1 _
  have h2 : (7/8 : ℝ) ^ (2 * n + 1) ≤ r ^ (2 * n + 1) :=
    pow_le_pow_left₀ (by norm_num) hr1 _
  have key : (7/8 : ℝ) ^ (2 * n) * (7/8 : ℝ) ^ (2 * n + 1) = (7/8 : ℝ) ^ (4 * n + 1) := by
    rw [← pow_add]; congr 1; ring
  calc (7/8 : ℝ) ^ (4 * n + 1)
      = (7/8 : ℝ) ^ (2 * n) * (7/8 : ℝ) ^ (2 * n + 1) := key.symm
    _ ≤ R ^ (2 * n) * r ^ (2 * n + 1) := mul_le_mul h1 h2 (by positivity) (by positivity)

/-- Lower bound for the denominator on the box. -/
private lemma denom_lower (n : ℕ) {R r : ℝ} (hR1 : 7/8 ≤ R) (hr1 : 7/8 ≤ r) :
    (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ)) * (2 * (7/8 : ℝ) ^ (4 * n + 1))
      ≤ ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ)
          * (R ^ (2 * n + 1) * r ^ (2 * n) + R ^ (2 * n) * r ^ (2 * n + 1)) := by
  have h1 := pow_prod_lower_left n hR1 hr1
  have h2 := pow_prod_lower_right n hR1 hr1
  have hsum : 2 * (7/8 : ℝ) ^ (4 * n + 1)
      ≤ R ^ (2 * n + 1) * r ^ (2 * n) + R ^ (2 * n) * r ^ (2 * n + 1) := by linarith
  have hc : (0 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left hsum hc

/-- Upper bound for the numerator, linear in `ε`. -/
private lemma num_upper (n : ℕ) {r a b ε : ℝ} (hr1 : 7/8 ≤ r) (hr2 : r ≤ 9/8)
    (ha : |a| < ε) (hb : |b| < ε) :
    |((2 * n + 1 : ℕ) : ℝ) * r ^ (2 * n) * a + ((2 * n + 2 : ℕ) : ℝ) * r ^ (2 * n + 1) * b|
      ≤ (((4 * n + 3 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2 * n + 1)) * ε := by
  have hr2n : r ^ (2 * n) ≤ (9/8 : ℝ) ^ (2 * n + 1) := by
    have h : r ^ (2 * n) ≤ (9/8 : ℝ) ^ (2 * n) := pow_le_pow_left₀ (by linarith) hr2 _
    have h' : (9/8 : ℝ) ^ (2 * n) ≤ (9/8 : ℝ) ^ (2 * n + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
    linarith
  have hr2n1 : r ^ (2 * n + 1) ≤ (9/8 : ℝ) ^ (2 * n + 1) :=
    pow_le_pow_left₀ (by linarith) hr2 _
  have h1 : |((2 * n + 1 : ℕ) : ℝ) * r ^ (2 * n) * a|
      ≤ ((2 * n + 1 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2 * n + 1) * ε := by
    have hc : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by positivity
    have hr2n_nonneg : (0 : ℝ) ≤ r ^ (2 * n) := by positivity
    have hA : (0 : ℝ) < (9/8 : ℝ) ^ (2 * n + 1) := by positivity
    rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hr2n_nonneg]
    have step1 : r ^ (2 * n) * |a| ≤ (9/8 : ℝ) ^ (2 * n + 1) * |a| :=
      mul_le_mul_of_nonneg_right hr2n (abs_nonneg a)
    have step2 : (9/8 : ℝ) ^ (2 * n + 1) * |a| < (9/8 : ℝ) ^ (2 * n + 1) * ε :=
      mul_lt_mul_of_pos_left ha hA
    have step3 : r ^ (2 * n) * |a| ≤ (9/8 : ℝ) ^ (2 * n + 1) * ε :=
      le_of_lt (lt_of_le_of_lt step1 step2)
    calc ((2 * n + 1 : ℕ) : ℝ) * r ^ (2 * n) * |a|
        = ((2 * n + 1 : ℕ) : ℝ) * (r ^ (2 * n) * |a|) := by ring
      _ ≤ ((2 * n + 1 : ℕ) : ℝ) * ((9/8 : ℝ) ^ (2 * n + 1) * ε) :=
            mul_le_mul_of_nonneg_left step3 hc
      _ = ((2 * n + 1 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2 * n + 1) * ε := by ring
  have h2 : |((2 * n + 2 : ℕ) : ℝ) * r ^ (2 * n + 1) * b|
      ≤ ((2 * n + 2 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2 * n + 1) * ε := by
    have hc : (0 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) := by positivity
    have hr_nonneg : (0 : ℝ) ≤ r ^ (2 * n + 1) := by positivity
    have hA : (0 : ℝ) < (9/8 : ℝ) ^ (2 * n + 1) := by positivity
    rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hr_nonneg]
    have step1 : r ^ (2 * n + 1) * |b| ≤ (9/8 : ℝ) ^ (2 * n + 1) * |b| :=
      mul_le_mul_of_nonneg_right hr2n1 (abs_nonneg b)
    have step2 : (9/8 : ℝ) ^ (2 * n + 1) * |b| < (9/8 : ℝ) ^ (2 * n + 1) * ε :=
      mul_lt_mul_of_pos_left hb hA
    have step3 : r ^ (2 * n + 1) * |b| ≤ (9/8 : ℝ) ^ (2 * n + 1) * ε :=
      le_of_lt (lt_of_le_of_lt step1 step2)
    calc ((2 * n + 2 : ℕ) : ℝ) * r ^ (2 * n + 1) * |b|
        = ((2 * n + 2 : ℕ) : ℝ) * (r ^ (2 * n + 1) * |b|) := by ring
      _ ≤ ((2 * n + 2 : ℕ) : ℝ) * ((9/8 : ℝ) ^ (2 * n + 1) * ε) :=
            mul_le_mul_of_nonneg_left step3 hc
      _ = ((2 * n + 2 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2 * n + 1) * ε := by ring
  calc |((2 * n + 1 : ℕ) : ℝ) * r ^ (2 * n) * a + ((2 * n + 2 : ℕ) : ℝ) * r ^ (2 * n + 1) * b|
      ≤ |((2 * n + 1 : ℕ) : ℝ) * r ^ (2 * n) * a|
          + |((2 * n + 2 : ℕ) : ℝ) * r ^ (2 * n + 1) * b| := abs_add_le _ _
    _ ≤ ((2 * n + 1 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2 * n + 1) * ε
          + ((2 * n + 2 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2 * n + 1) * ε := add_le_add h1 h2
    _ = (((4 * n + 3 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2 * n + 1)) * ε := by push_cast; ring

theorem radial_first_deriv_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {R r R' a b ε : ℝ},
      7/8 ≤ R → R ≤ 9/8 → 7/8 ≤ r → r ≤ 9/8 → |a| < ε → |b| < ε →
      (((2*n+2 : ℕ) : ℝ) * ((2*n+1 : ℕ) : ℝ) * (R ^ (2*n+1) * r ^ (2*n) + R ^ (2*n) * r ^ (2*n+1))) * R'
        = ((2*n+1 : ℕ) : ℝ) * r ^ (2*n) * a + ((2*n+2 : ℕ) : ℝ) * r ^ (2*n+1) * b →
      |R'| ≤ C * ε := by
  refine ⟨((4 * n + 3 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2 * n + 1)
            / ((((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ)) * (2 * (7/8 : ℝ) ^ (4 * n + 1))), ?_, ?_⟩
  · positivity
  · intro R r R' a b ε hR1 hR2 hr1 hr2 ha hb hEq
    set D : ℝ := ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ)
        * (R ^ (2 * n + 1) * r ^ (2 * n) + R ^ (2 * n) * r ^ (2 * n + 1)) with hD
    set N : ℝ := ((2 * n + 1 : ℕ) : ℝ) * r ^ (2 * n) * a
        + ((2 * n + 2 : ℕ) : ℝ) * r ^ (2 * n + 1) * b with hN
    set d0 : ℝ := (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ)) * (2 * (7/8 : ℝ) ^ (4 * n + 1))
      with hd0
    set K : ℝ := ((4 * n + 3 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2 * n + 1) with hK
    have hd0pos : 0 < d0 := by rw [hd0]; positivity
    have hDge : d0 ≤ D := by rw [hd0, hD]; exact denom_lower n hR1 hr1
    have hnum : |N| ≤ K * ε := by rw [hN, hK]; exact num_upper n hr1 hr2 ha hb
    have hDnn : 0 ≤ D := le_trans (le_of_lt hd0pos) hDge
    have hDabs : D * |R'| = |N| := by
      have h1 : |D * R'| = |N| := by rw [hEq]
      have h2 : |D * R'| = D * |R'| := by rw [abs_mul, abs_of_nonneg hDnn]
      rw [← h2, h1]
    have hchain : d0 * |R'| ≤ K * ε := by
      calc d0 * |R'| ≤ D * |R'| := mul_le_mul_of_nonneg_right hDge (abs_nonneg R')
        _ = |N| := hDabs
        _ ≤ K * ε := hnum
    have hfinal : |R'| ≤ (K / d0) * ε := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd0pos, mul_comm |R'| d0]
      exact hchain
    exact hfinal

end Work.OddRadon
