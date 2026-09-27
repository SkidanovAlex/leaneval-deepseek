import Mathlib

/-!
# Shearer/Shannon entropy bound for the sum of `Real.negMulLog`

For a nonempty finite family `x` of nonnegative reals with total mass `S = ∑ i ∈ s, x i`
and `n = s.card`, the sum of the entropy summands `Real.negMulLog (x i) = - x i * log (x i)`
is at most `S * log (n / S)`:

  `∑ i ∈ s, Real.negMulLog (x i) ≤ (∑ i ∈ s, x i) * Real.log ((s.card : ℝ) / (∑ i ∈ s, x i))`.

This is the Shannon/Shearer inequality `∑ p i * log (1 / p i) ≤ log n` for the probability
vector `p i = x i / S`, rescaled by `S`.

## Proof outline

* **Tangent line of the concave function `negMulLog` at the point `1 / a`.**  For `0 < a`
  and `0 ≤ y` we have (`negMulLog_le_affine`)

    `Real.negMulLog y ≤ y * (Real.log a - 1) + 1 / a`,

  which after multiplying by `a` (and using `log (a * y) = log a + log y`) is exactly the
  standard logarithm estimate `log z ≥ 1 - 1 / z` at `z = a * y`
  (`mul_one_sub_log_le_one`, itself a direct consequence of `Real.negMulLog_le_one_sub_self`).
* **Summation.**  Take `a = n / S`.  Summing the tangent bound over `s` gives

    `∑ i ∈ s, negMulLog (x i) ≤ S * (log a - 1) + n * (1 / a) = S * log a - S + S = S * log a`,

  using `∑ i ∈ s, x i = S` and `n * (S / n) = S`.
* The degenerate case `S = 0` forces `x i = 0` for all `i ∈ s` and both sides vanish.

## Main results

* `Work.EKLComp.mul_one_sub_log_le_one`
* `Work.EKLComp.negMulLog_le_affine`
* `Work.EKLComp.negMulLog_sum_le_card_mul_log` : the target inequality.
-/

namespace Work.EKLComp

/-- For `0 ≤ z`, `z * (1 - log z) ≤ 1`; equivalently `log z ≥ 1 - 1 / z`.
Immediate from `Real.negMulLog_le_one_sub_self`. -/
lemma mul_one_sub_log_le_one {z : ℝ} (hz : 0 ≤ z) : z * (1 - Real.log z) ≤ 1 := by
  have h := Real.negMulLog_le_one_sub_self hz
  rw [Real.negMulLog] at h
  linarith

/-- Tangent-line bound for the concave function `Real.negMulLog` at the point `1 / a`:
for `0 < a` and `0 ≤ y`,

  `Real.negMulLog y ≤ y * (log a - 1) + 1 / a`. -/
lemma negMulLog_le_affine {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    Real.negMulLog y ≤ y * (Real.log a - 1) + 1 / a := by
  rcases eq_or_lt_of_le hy with h | h
  · subst h
    simp only [Real.negMulLog_zero, zero_mul, zero_add]
    positivity
  · have h1 : (a * y) * (1 - Real.log (a * y)) ≤ 1 :=
      mul_one_sub_log_le_one (mul_nonneg ha.le hy)
    have h2 : y * (1 - Real.log (a * y)) ≤ 1 / a := by
      have h3 : (1 / a) * ((a * y) * (1 - Real.log (a * y))) ≤ (1 / a) * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h4 : (1 / a) * ((a * y) * (1 - Real.log (a * y))) = y * (1 - Real.log (a * y)) := by
        field_simp
      linarith [h3, h4]
    have h5 : Real.log (a * y) = Real.log a + Real.log y := Real.log_mul ha.ne' h.ne'
    rw [h5] at h2
    rw [Real.negMulLog]
    linarith

theorem negMulLog_sum_le_card_mul_log {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∑ i ∈ s, Real.negMulLog (x i) ≤ (∑ i ∈ s, x i) * Real.log ((s.card : ℝ) / (∑ i ∈ s, x i)) := by
  rcases eq_or_lt_of_le (Finset.sum_nonneg (fun i hi => hx i hi)) with hS | hS
  · -- degenerate case: total mass zero, hence all entries vanish
    have hS0 : ∑ i ∈ s, x i = 0 := hS.symm
    have hx0 : ∀ i ∈ s, x i = 0 := by
      intro i hi
      have h1 : x i ≤ ∑ j ∈ s, x j := Finset.single_le_sum (fun j hj => hx j hj) hi
      linarith [hx i hi, h1, hS0]
    rw [Finset.sum_eq_zero (fun i hi => by rw [hx0 i hi, Real.negMulLog_zero]), hS0]
    simp
  · -- positive total mass: sum the tangent-line bounds at `a = card / S`
    have hn : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
    have hS' : (∑ i ∈ s, x i) ≠ 0 := hS.ne'
    have ha : 0 < (s.card : ℝ) / (∑ i ∈ s, x i) :=
      div_pos hn hS
    have h1a : (s.card : ℝ) * (1 / ((s.card : ℝ) / (∑ i ∈ s, x i))) = ∑ i ∈ s, x i := by
      rw [one_div, inv_div]
      field_simp
    calc ∑ i ∈ s, Real.negMulLog (x i)
        ≤ ∑ i ∈ s, (x i * (Real.log ((s.card : ℝ) / (∑ i ∈ s, x i)) - 1)
              + 1 / ((s.card : ℝ) / (∑ i ∈ s, x i))) :=
            Finset.sum_le_sum (fun i hi => negMulLog_le_affine ha (hx i hi))
      _ = (∑ i ∈ s, x i) * Real.log ((s.card : ℝ) / (∑ i ∈ s, x i)) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul, h1a]
            ring

end Work.EKLComp
