import Mathlib
import Submission.Work.GM.S2.pair_sum_defs
import Submission.Work.GM.S2.geom_two_sums

/-!
# Arithmetic estimate for the level sum of `S₂` (Guth–Maynard §6)

The `S₂` pair sum of Guth–Maynard §6 is split into dyadic levels `kk = 0, …, K-1`
of the frequency `|t| = 2^kk`.  On level `kk` the truncation length of the reflected
`m`-sum is `Y_kk = (1 + 2^{kk+1}) · M^η / N` (with `M = M N = N^{6/5}` the length of
the interval `[0,T]`), the weight carries `(1/2)^kk`, and the Heath–Brown input gives
the three terms with exponents `2`, `7/4` and `29/16`.

The point of this lemma is that the geometric weights beat the number `K` of levels:
writing `c_kk = 1 + 2^{kk+1}` one has `(1/2)^kk c_kk = (1/2)^kk + 2`, and
`(1/2)^kk c_kk^2 = (1/2)^kk + 4 + 4·2^kk`, so

* `∑_{kk<K} (1/2)^kk c_kk ≤ 2 + 2K`, and
* `∑_{kk<K} (1/2)^kk c_kk^2 ≤ 2 + 4K + 4·2^K`,

and `K ≤ 2^K ≤ 4 M` converts the middle `K` into a factor `M`, which the hypothesis
`M^{2η} ≤ N^{δ/2}` (i.e. `(M^η)^2 ≤ N^{δ/2}`) absorbs against the `M` on the right
hand side.  Hypothesis `K M^η ≤ N^{δ/2}` handles the first and third terms.

The constants are deliberately crude: the three terms are bounded by
`4`, `34` and `4` times `N^{δ/2}·(…)`, and `4 + 34 + 4 < 256`.
-/

namespace Work.GM.S2

/-- `(1/2)^kk · 2^{kk+1} = 2`. -/
lemma half_mul_two_pow_succ (kk : ℕ) : ((1 / 2 : ℝ)) ^ kk * (2 : ℝ) ^ (kk + 1) = 2 := by
  rw [pow_succ, ← mul_assoc, ← mul_pow]
  norm_num

/-- `(1/2)^kk (1 + 2^{kk+1})^2 = (1/2)^kk + 4 + 4·2^kk`. -/
lemma half_sq_expand (kk : ℕ) :
    ((1 / 2 : ℝ)) ^ kk * (1 + (2 : ℝ) ^ (kk + 1)) ^ 2 =
      ((1 / 2 : ℝ)) ^ kk + 4 + 4 * (2 : ℝ) ^ kk := by
  have h3 : ((1 / 2 : ℝ)) ^ kk * ((2 : ℝ) ^ (kk + 1)) ^ 2 = 4 * (2 : ℝ) ^ kk := by
    rw [pow_two, ← mul_assoc, half_mul_two_pow_succ, pow_succ]; ring
  calc ((1 / 2 : ℝ)) ^ kk * (1 + (2 : ℝ) ^ (kk + 1)) ^ 2
      = ((1 / 2 : ℝ)) ^ kk * (1 + 2 * (2 : ℝ) ^ (kk + 1) + ((2 : ℝ) ^ (kk + 1)) ^ 2) := by
        ring
    _ = ((1 / 2 : ℝ)) ^ kk + 2 * (((1 / 2 : ℝ)) ^ kk * (2 : ℝ) ^ (kk + 1))
          + ((1 / 2 : ℝ)) ^ kk * ((2 : ℝ) ^ (kk + 1)) ^ 2 := by ring
    _ = ((1 / 2 : ℝ)) ^ kk + 4 + 4 * (2 : ℝ) ^ kk := by
        rw [half_mul_two_pow_succ, h3]; ring

/-- `∑_{kk<K} (1/2)^kk (1 + 2^{kk+1}) ≤ 2 + 2K`. -/
lemma sum_half_c_le (K : ℕ) :
    (∑ kk ∈ Finset.range K, ((1 / 2 : ℝ)) ^ kk * (1 + (2 : ℝ) ^ (kk + 1)))
      ≤ 2 + 2 * (K : ℝ) := by
  have hsplit : (∑ kk ∈ Finset.range K, ((1 / 2 : ℝ)) ^ kk * (1 + (2 : ℝ) ^ (kk + 1)))
      = (∑ kk ∈ Finset.range K, ((1 / 2 : ℝ)) ^ kk) + 2 * (K : ℝ) := by
    rw [show (∑ kk ∈ Finset.range K, ((1 / 2 : ℝ)) ^ kk * (1 + (2 : ℝ) ^ (kk + 1)))
        = (∑ kk ∈ Finset.range K, (((1 / 2 : ℝ)) ^ kk + 2)) from
        Finset.sum_congr rfl (fun kk _ => by rw [mul_add, mul_one, half_mul_two_pow_succ])]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hsplit]
  linarith [(geom_two_sums K).1]

/-- `∑_{kk<K} (1/2)^kk (1 + 2^{kk+1})^2 ≤ 2 + 4K + 4·2^K`. -/
lemma sum_half_c_sq_le (K : ℕ) :
    (∑ kk ∈ Finset.range K, ((1 / 2 : ℝ)) ^ kk * (1 + (2 : ℝ) ^ (kk + 1)) ^ 2)
      ≤ 2 + 4 * (K : ℝ) + 4 * (2 : ℝ) ^ K := by
  have hsplit : (∑ kk ∈ Finset.range K, ((1 / 2 : ℝ)) ^ kk * (1 + (2 : ℝ) ^ (kk + 1)) ^ 2)
      = (∑ kk ∈ Finset.range K, ((1 / 2 : ℝ)) ^ kk) + 4 * (K : ℝ)
        + 4 * (∑ kk ∈ Finset.range K, (2 : ℝ) ^ kk) := by
    rw [show (∑ kk ∈ Finset.range K, ((1 / 2 : ℝ)) ^ kk * (1 + (2 : ℝ) ^ (kk + 1)) ^ 2)
        = (∑ kk ∈ Finset.range K, (((1 / 2 : ℝ)) ^ kk + 4 + 4 * (2 : ℝ) ^ kk)) from
        Finset.sum_congr rfl (fun kk _ => half_sq_expand kk)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [hsplit]
  linarith [(geom_two_sums K).1, (geom_two_sums K).2]

/-- The level-sum arithmetic of Guth–Maynard §6: the three Heath–Brown terms, summed
over the dyadic levels `kk < K` with geometric weights `(1/2)^kk`, are bounded by
`256 · N^{δ/2}` times the bracket appearing in the challenge statement. -/
theorem level_sum_arith
    (N K : ℕ) (R δ η : ℝ) (hR : 0 ≤ R) (hN : 1 ≤ N) (hδ : 0 < δ) (hη : 0 < η)
    (h2K : (2 : ℝ) ^ K ≤ 4 * Submission.LargeValues.M N)
    (hKT : (K : ℝ) * (Submission.LargeValues.M N) ^ η ≤ (N : ℝ) ^ (δ / 2))
    (hT2η : (Submission.LargeValues.M N) ^ (2 * η) ≤ (N : ℝ) ^ (δ / 2)) :
    (∑ kk ∈ Finset.range K, ((1 / 2 : ℝ) ^ kk) *
        (R ^ 2 * (((1 : ℝ) + (2 : ℝ) ^ (kk + 1)) * (Submission.LargeValues.M N) ^ η / (N : ℝ))
          + R ^ ((7 : ℝ) / 4) * ((((1 : ℝ) + (2 : ℝ) ^ (kk + 1)) * (Submission.LargeValues.M N) ^ η / (N : ℝ)) ^ 2)
          + R ^ ((29 : ℝ) / 16) * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 8)
            * (((1 : ℝ) + (2 : ℝ) ^ (kk + 1)) * (Submission.LargeValues.M N) ^ η / (N : ℝ))))
      ≤ 256 * (N : ℝ) ^ (δ / 2) * (R ^ 2 / (N : ℝ)
          + Submission.LargeValues.M N * R ^ ((7 : ℝ) / 4) / (N : ℝ) ^ 2
          + (Submission.LargeValues.M N) ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / (N : ℝ)) := by
  -- abbreviation for `M N`, for `N` and for `N^{δ/2}`
  set m : ℝ := Submission.LargeValues.M N with hm
  set A : ℝ := (N : ℝ) with hA
  set w : ℝ := A ^ (δ / 2) with hw
  have hA1 : 1 ≤ A := by rw [hA]; exact_mod_cast hN
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hm1 : 1 ≤ m := by rw [hm]; exact Submission.LargeValues.M_ge_one hN
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  have hw0 : 0 ≤ w := by rw [hw]; exact Real.rpow_nonneg (le_of_lt hA0) _
  -- `M^η ≤ N^{δ/2}`, since `M ≥ 1` and `M^{2η} ≤ N^{δ/2}`
  have hmη : m ^ η ≤ w :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)) hT2η
  -- `(M^η)² = M^{2η}`
  have hm2eq : (m ^ η) ^ 2 = m ^ (2 * η) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hm0) η 2]
    congr 1; ring
  -- `K ≤ 2^K`
  have hKle2 : (K : ℝ) ≤ (2 : ℝ) ^ K := by
    have h := Nat.lt_two_pow_self (n := K); exact_mod_cast le_of_lt h
  -- the summand factors into three products with constants `R²M^η/N`, `R^{7/4}(M^η)²/N²`
  -- and `R^{29/16}M^{1/8}M^η/N`
  have hterm : ∀ kk : ℕ,
      (1 / 2 : ℝ) ^ kk * (R ^ 2 * ((1 + (2 : ℝ) ^ (kk + 1)) * m ^ η / A)
        + R ^ ((7 : ℝ) / 4) * (((1 + (2 : ℝ) ^ (kk + 1)) * m ^ η / A) ^ 2)
        + R ^ ((29 : ℝ) / 16) * m ^ ((1 : ℝ) / 8) * ((1 + (2 : ℝ) ^ (kk + 1)) * m ^ η / A))
      = (R ^ 2 * m ^ η / A) * ((1 / 2 : ℝ) ^ kk * (1 + (2 : ℝ) ^ (kk + 1)))
        + (R ^ ((7 : ℝ) / 4) * (m ^ η) ^ 2 / A ^ 2)
          * ((1 / 2 : ℝ) ^ kk * (1 + (2 : ℝ) ^ (kk + 1)) ^ 2)
        + (R ^ ((29 : ℝ) / 16) * m ^ ((1 : ℝ) / 8) * m ^ η / A)
          * ((1 / 2 : ℝ) ^ kk * (1 + (2 : ℝ) ^ (kk + 1))) := by
    intro kk; ring
  have hsplit : (∑ kk ∈ Finset.range K,
        ((1 / 2 : ℝ) ^ kk) * (R ^ 2 * ((1 + (2 : ℝ) ^ (kk + 1)) * m ^ η / A)
          + R ^ ((7 : ℝ) / 4) * (((1 + (2 : ℝ) ^ (kk + 1)) * m ^ η / A) ^ 2)
          + R ^ ((29 : ℝ) / 16) * m ^ ((1 : ℝ) / 8) * ((1 + (2 : ℝ) ^ (kk + 1)) * m ^ η / A)))
      = (R ^ 2 * m ^ η / A)
          * (∑ kk ∈ Finset.range K, ((1 / 2 : ℝ) ^ kk) * (1 + (2 : ℝ) ^ (kk + 1)))
        + (R ^ ((7 : ℝ) / 4) * (m ^ η) ^ 2 / A ^ 2)
          * (∑ kk ∈ Finset.range K, ((1 / 2 : ℝ) ^ kk) * (1 + (2 : ℝ) ^ (kk + 1)) ^ 2)
        + (R ^ ((29 : ℝ) / 16) * m ^ ((1 : ℝ) / 8) * m ^ η / A)
          * (∑ kk ∈ Finset.range K, ((1 / 2 : ℝ) ^ kk) * (1 + (2 : ℝ) ^ (kk + 1))) := by
    rw [Finset.sum_congr rfl (fun kk _ => hterm kk), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsplit]
  have hS1 : (∑ kk ∈ Finset.range K, ((1 / 2 : ℝ) ^ kk) * (1 + (2 : ℝ) ^ (kk + 1)))
      ≤ 2 + 2 * (K : ℝ) := sum_half_c_le K
  have hS2 : (∑ kk ∈ Finset.range K, ((1 / 2 : ℝ) ^ kk) * (1 + (2 : ℝ) ^ (kk + 1)) ^ 2)
      ≤ 2 + 4 * (K : ℝ) + 4 * (2 : ℝ) ^ K := sum_half_c_sq_le K
  have hR2 : (0 : ℝ) ≤ R ^ 2 := sq_nonneg R
  have hmη0 : 0 ≤ m ^ η := Real.rpow_nonneg (le_of_lt hm0) η
  have hc1n : 0 ≤ R ^ 2 * m ^ η / A := div_nonneg (mul_nonneg hR2 hmη0) (le_of_lt hA0)
  have hc2n : 0 ≤ R ^ ((7 : ℝ) / 4) * (m ^ η) ^ 2 / A ^ 2 :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg hR _) (sq_nonneg _)) (by positivity)
  have hc3n : 0 ≤ R ^ ((29 : ℝ) / 16) * m ^ ((1 : ℝ) / 8) * m ^ η / A :=
    div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hR _)
      (Real.rpow_nonneg (le_of_lt hm0) _)) hmη0) (le_of_lt hA0)
  have hb1 := mul_le_mul_of_nonneg_left hS1 hc1n
  have hb2 := mul_le_mul_of_nonneg_left hS2 hc2n
  have hb3 := mul_le_mul_of_nonneg_left hS1 hc3n
  -- the two factors `M^η` and `K M^η` are both at most `N^{δ/2}`
  have hk0 : 2 * m ^ η + 2 * ((K : ℝ) * m ^ η) ≤ 4 * w := by linarith [hmη, hKT]
  have hc1b : (R ^ 2 * m ^ η / A) * (2 + 2 * (K : ℝ)) ≤ 4 * (w * R ^ 2 / A) := by
    have hfac : 0 ≤ R ^ 2 / A := div_nonneg hR2 (le_of_lt hA0)
    calc (R ^ 2 * m ^ η / A) * (2 + 2 * (K : ℝ))
        = (R ^ 2 / A) * (2 * m ^ η + 2 * ((K : ℝ) * m ^ η)) := by ring
      _ ≤ (R ^ 2 / A) * (4 * w) := mul_le_mul_of_nonneg_left hk0 hfac
      _ = 4 * (w * R ^ 2 / A) := by ring
  have hc3b : (R ^ ((29 : ℝ) / 16) * m ^ ((1 : ℝ) / 8) * m ^ η / A) * (2 + 2 * (K : ℝ))
      ≤ 4 * (w * m ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / A) := by
    have hfac : 0 ≤ R ^ ((29 : ℝ) / 16) * m ^ ((1 : ℝ) / 8) / A :=
      div_nonneg (mul_nonneg (Real.rpow_nonneg hR _)
        (Real.rpow_nonneg (le_of_lt hm0) _)) (le_of_lt hA0)
    calc (R ^ ((29 : ℝ) / 16) * m ^ ((1 : ℝ) / 8) * m ^ η / A) * (2 + 2 * (K : ℝ))
        = (R ^ ((29 : ℝ) / 16) * m ^ ((1 : ℝ) / 8) / A)
            * (2 * m ^ η + 2 * ((K : ℝ) * m ^ η)) := by ring
      _ ≤ (R ^ ((29 : ℝ) / 16) * m ^ ((1 : ℝ) / 8) / A) * (4 * w) :=
          mul_le_mul_of_nonneg_left hk0 hfac
      _ = 4 * (w * m ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / A) := by ring
  -- `2 + 4K + 4·2^K ≤ 34 M`, using `K ≤ 2^K ≤ 4M` and `M ≥ 1`
  have h34 : 2 + 4 * (K : ℝ) + 4 * (2 : ℝ) ^ K ≤ 34 * m := by
    nlinarith [hKle2, h2K, hm1]
  have h2η : (m ^ η) ^ 2 ≤ w := by rw [hm2eq]; exact hT2η
  have hc2b : (R ^ ((7 : ℝ) / 4) * (m ^ η) ^ 2 / A ^ 2) * (2 + 4 * (K : ℝ) + 4 * (2 : ℝ) ^ K)
      ≤ 34 * (w * m * R ^ ((7 : ℝ) / 4) / A ^ 2) := by
    calc (R ^ ((7 : ℝ) / 4) * (m ^ η) ^ 2 / A ^ 2) * (2 + 4 * (K : ℝ) + 4 * (2 : ℝ) ^ K)
        ≤ (R ^ ((7 : ℝ) / 4) * (m ^ η) ^ 2 / A ^ 2) * (34 * m) :=
          mul_le_mul_of_nonneg_left h34 hc2n
      _ = (R ^ ((7 : ℝ) / 4) / A ^ 2) * (34 * m * (m ^ η) ^ 2) := by ring
      _ ≤ (R ^ ((7 : ℝ) / 4) / A ^ 2) * (34 * m * w) := by
            apply mul_le_mul_of_nonneg_left _ (div_nonneg (Real.rpow_nonneg hR _) (by positivity))
            exact mul_le_mul_of_nonneg_left h2η (by positivity)
      _ = 34 * (w * m * R ^ ((7 : ℝ) / 4) / A ^ 2) := by ring
  -- the three bounds sum to at most `42 ≤ 256` times the bracket
  have hfin : 4 * (w * R ^ 2 / A) + 34 * (w * m * R ^ ((7 : ℝ) / 4) / A ^ 2)
        + 4 * (w * m ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / A)
      ≤ 256 * w * (R ^ 2 / A + m * R ^ ((7 : ℝ) / 4) / A ^ 2
          + m ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / A) := by
    have hW1 : 0 ≤ w * R ^ 2 / A := div_nonneg (mul_nonneg hw0 hR2) (le_of_lt hA0)
    have hW2 : 0 ≤ w * m * R ^ ((7 : ℝ) / 4) / A ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg hw0 (le_of_lt hm0)) (Real.rpow_nonneg hR _))
        (by positivity)
    have hW3 : 0 ≤ w * m ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / A :=
      div_nonneg (mul_nonneg (mul_nonneg hw0 (Real.rpow_nonneg (le_of_lt hm0) _))
        (Real.rpow_nonneg hR _)) (le_of_lt hA0)
    have hexp : 256 * w * (R ^ 2 / A + m * R ^ ((7 : ℝ) / 4) / A ^ 2
          + m ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / A)
        = 256 * (w * R ^ 2 / A) + 256 * (w * m * R ^ ((7 : ℝ) / 4) / A ^ 2)
          + 256 * (w * m ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / A) := by ring
    have e1 : 4 * (w * R ^ 2 / A) ≤ 256 * (w * R ^ 2 / A) := by linarith
    have e2 : 34 * (w * m * R ^ ((7 : ℝ) / 4) / A ^ 2)
        ≤ 256 * (w * m * R ^ ((7 : ℝ) / 4) / A ^ 2) := by linarith
    have e3 : 4 * (w * m ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / A)
        ≤ 256 * (w * m ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / A) := by linarith
    rw [hexp]
    linarith
  linarith [hb1, hb2, hb3, hc1b, hc2b, hc3b, hfin]

end Work.GM.S2
