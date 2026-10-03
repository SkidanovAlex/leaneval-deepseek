import Mathlib

/-!
# A tail bound for `∑ (1 + log (2 + a + i)) / ((a + i)^2 + η^2)`

We prove that for `a ≥ 1` the sum
`∑_{i<N} (1 + log (2 + a + i)) / ((a + i)^2 + η^2)`
is at most `3 * (1 + log (3 + a)) / a`, uniformly in `N` and in `η`.

The estimate is a discrete analogue of the integral
`∫_a^∞ (1 + log (2 + x)) / x^2 dx ≍ log a / a`.  Concretely, with

* `h x = (1 + log (2 + x)) / x^2`  (the summand, decreasing in `x`),
* `g x = (2 + log (2 + x)) / x`,

the key **telescoping step** is `h (x+1) ≤ g x - g (x+1)` for `x > 0`, which follows from
`log ((3+x)/(2+x)) ≤ 1/(x+2)`.  Summing it gives
`∑_{i<N} h (a+i) ≤ h a + g a`, and the elementary bound `h a + g a ≤ 3 (1 + log (3+a)) / a`
finishes the proof.  The extra `η^2` in the denominator only makes the terms smaller.
-/

namespace Work.Parab.coordData

/-- The telescoping step: with `g x = (2 + log (2 + x)) / x`, one has
`h (x+1) ≤ g x - g (x+1)` where `h y = (1 + log (2 + y)) / y^2`.

Indeed, writing `u = log (2+x)` and `v = log ((3+x)/(2+x)) ≤ 1/(x+2)`, the difference
`g x - g (x+1) - h (x+1)` equals `(x + 2 + u - v * x * (x+2)) / (x * (x+1)^2)`, whose
numerator is `≥ x + 2 + u - x = 2 + u ≥ 0`. -/
private lemma log_telescoping (x : ℝ) (hx : 0 < x) :
    (1 + Real.log (2 + (x + 1))) / (x + 1) ^ 2
      ≤ (2 + Real.log (2 + x)) / x - (2 + Real.log (2 + (x + 1))) / (x + 1) := by
  have hx1 : 0 < x + 1 := by linarith
  have hv : Real.log (2 + (x + 1)) - Real.log (2 + x) ≤ 1 / (x + 2) := by
    have hdiv : Real.log ((2 + (x + 1)) / (2 + x))
        = Real.log (2 + (x + 1)) - Real.log (2 + x) := by
      rw [Real.log_div (by positivity) (by positivity)]
    have heq : (2 + (x + 1)) / (2 + x) = 1 + 1 / (x + 2) := by
      field_simp
      ring
    rw [← hdiv, heq]
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (x + 2) by positivity)
    have hsimp : 1 + 1 / (x + 2) - 1 = 1 / (x + 2) := by ring
    linarith [h, hsimp]
  have hkey : (1 + Real.log (2 + (x + 1))) / (x + 1) ^ 2
      = (2 + Real.log (2 + x)) / x - (2 + Real.log (2 + (x + 1))) / (x + 1)
        - ((x + 2 + Real.log (2 + x)
            - (Real.log (2 + (x + 1)) - Real.log (2 + x)) * (x * (x + 2)))
           / (x * (x + 1) ^ 2)) := by
    field_simp
    ring
  have hnum : 0 ≤ x + 2 + Real.log (2 + x)
      - (Real.log (2 + (x + 1)) - Real.log (2 + x)) * (x * (x + 2)) := by
    have hmul := mul_le_mul_of_nonneg_right hv (by positivity : (0 : ℝ) ≤ x * (x + 2))
    have hval : (1 / (x + 2)) * (x * (x + 2)) = x := by field_simp
    rw [hval] at hmul
    have : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
    linarith
  have hnn : 0 ≤ (x + 2 + Real.log (2 + x)
      - (Real.log (2 + (x + 1)) - Real.log (2 + x)) * (x * (x + 2)))
      / (x * (x + 1) ^ 2) := div_nonneg hnum (by positivity)
  linarith [hkey, hnn]

/-- Pointwise domination of the `(i+1)`-st term of the sum by the `i`-th telescoping increment
of `g`.  The additional `η^2` in the denominator is harmless. -/
private lemma term_step {a η : ℝ} (ha : 0 < a) (i : ℕ) :
    (1 + Real.log (2 + (a + ((i + 1 : ℕ) : ℝ)))) / ((a + ((i + 1 : ℕ) : ℝ)) ^ 2 + η ^ 2)
      ≤ (2 + Real.log (2 + (a + (i : ℝ)))) / (a + (i : ℝ))
        - (2 + Real.log (2 + (a + ((i + 1 : ℕ) : ℝ)))) / (a + ((i + 1 : ℕ) : ℝ)) := by
  have hai : 0 < a + (i : ℝ) := by positivity
  have hcast : a + ((i + 1 : ℕ) : ℝ) = (a + (i : ℝ)) + 1 := by push_cast; ring
  have hpos : 0 < a + ((i + 1 : ℕ) : ℝ) := by rw [hcast]; linarith
  have hnum : 0 ≤ 1 + Real.log (2 + (a + ((i + 1 : ℕ) : ℝ))) := by
    have h1 : (1 : ℝ) ≤ 2 + (a + ((i + 1 : ℕ) : ℝ)) := by push_cast; linarith
    have := Real.log_nonneg h1
    linarith
  have hden : (a + ((i + 1 : ℕ) : ℝ)) ^ 2 ≤ (a + ((i + 1 : ℕ) : ℝ)) ^ 2 + η ^ 2 := by
    nlinarith [sq_nonneg η]
  have hstep : (1 + Real.log (2 + (a + ((i + 1 : ℕ) : ℝ))))
        / ((a + ((i + 1 : ℕ) : ℝ)) ^ 2 + η ^ 2)
      ≤ (1 + Real.log (2 + (a + ((i + 1 : ℕ) : ℝ))))
        / (a + ((i + 1 : ℕ) : ℝ)) ^ 2 :=
    div_le_div_of_nonneg_left hnum (pow_pos hpos 2) hden
  have ht := log_telescoping (a + (i : ℝ)) hai
  simp only [hcast] at hstep ht ⊢
  linarith [hstep, ht]

theorem tail_log_sum_bound {a η : ℝ} {N : ℕ} (ha : 1 ≤ a) :
    ∑ i ∈ Finset.range N,
        (1 + Real.log (2 + (a + (i : ℝ)))) / ((a + (i : ℝ)) ^ 2 + η ^ 2)
      ≤ 3 * (1 + Real.log (3 + a)) / a := by
  have ha0 : 0 < a := by linarith
  have hL0 : 0 ≤ 1 + Real.log (2 + a) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + a)
    linarith
  -- the elementary final arithmetic
  have hfinal : (1 + Real.log (2 + a)) / a ^ 2 + (2 + Real.log (2 + a)) / a
      ≤ 3 * (1 + Real.log (3 + a)) / a := by
    have hlog : Real.log (2 + a) ≤ Real.log (3 + a) :=
      Real.log_le_log (by linarith) (by linarith)
    have hL : 0 ≤ Real.log (3 + a) := Real.log_nonneg (by linarith)
    have h1 : (1 + Real.log (2 + a)) / a ^ 2 ≤ (1 + Real.log (3 + a)) / a := by
      have hnum : 1 + Real.log (2 + a) ≤ 1 + Real.log (3 + a) := by linarith
      calc (1 + Real.log (2 + a)) / a ^ 2
          ≤ (1 + Real.log (3 + a)) / a ^ 2 :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ (1 + Real.log (3 + a)) / a :=
            div_le_div_of_nonneg_left (by linarith) ha0 (by nlinarith)
    have h2 : (2 + Real.log (2 + a)) / a ≤ 2 * (1 + Real.log (3 + a)) / a := by
      apply div_le_div_of_nonneg_right _ ha0.le
      linarith
    calc (1 + Real.log (2 + a)) / a ^ 2 + (2 + Real.log (2 + a)) / a
        ≤ (1 + Real.log (3 + a)) / a + 2 * (1 + Real.log (3 + a)) / a := by linarith
      _ = 3 * (1 + Real.log (3 + a)) / a := by ring
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [Finset.range_zero, Finset.sum_empty]
    have h : 0 ≤ 3 * (1 + Real.log (3 + a)) / a := by
      have hL : 0 ≤ Real.log (3 + a) := Real.log_nonneg (by linarith)
      positivity
    linarith
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hN)
    rw [Finset.sum_range_succ']
    -- bound the shifted part by a telescoping sum
    have htail : ∑ i ∈ Finset.range k,
          (1 + Real.log (2 + (a + ((i + 1 : ℕ) : ℝ))))
            / ((a + ((i + 1 : ℕ) : ℝ)) ^ 2 + η ^ 2)
        ≤ (2 + Real.log (2 + a)) / a := by
      calc ∑ i ∈ Finset.range k,
              (1 + Real.log (2 + (a + ((i + 1 : ℕ) : ℝ))))
                / ((a + ((i + 1 : ℕ) : ℝ)) ^ 2 + η ^ 2)
          ≤ ∑ i ∈ Finset.range k,
              ((2 + Real.log (2 + (a + (i : ℝ)))) / (a + (i : ℝ))
                - (2 + Real.log (2 + (a + ((i + 1 : ℕ) : ℝ))))
                    / (a + ((i + 1 : ℕ) : ℝ))) :=
            Finset.sum_le_sum (fun i _ => term_step ha0 i)
        _ = (2 + Real.log (2 + (a + ((0 : ℕ) : ℝ)))) / (a + ((0 : ℕ) : ℝ))
              - (2 + Real.log (2 + (a + ((k : ℕ) : ℝ)))) / (a + ((k : ℕ) : ℝ)) :=
            Finset.sum_range_sub'
              (fun i : ℕ => (2 + Real.log (2 + (a + (i : ℝ)))) / (a + (i : ℝ))) k
        _ ≤ (2 + Real.log (2 + a)) / a := by
            have h0 : (2 + Real.log (2 + (a + ((0 : ℕ) : ℝ)))) / (a + ((0 : ℕ) : ℝ))
                = (2 + Real.log (2 + a)) / a := by norm_num
            have hk : 0 ≤ (2 + Real.log (2 + (a + ((k : ℕ) : ℝ)))) / (a + ((k : ℕ) : ℝ)) := by
              apply div_nonneg
              · have : (0 : ℝ) ≤ Real.log (2 + (a + ((k : ℕ) : ℝ))) :=
                  Real.log_nonneg (by linarith)
                linarith
              · positivity
            linarith [h0, hk]
    -- bound the `i = 0` term
    have hf0 : (1 + Real.log (2 + (a + ((0 : ℕ) : ℝ)))) / ((a + ((0 : ℕ) : ℝ)) ^ 2 + η ^ 2)
        ≤ (1 + Real.log (2 + a)) / a ^ 2 := by
      have he : (1 + Real.log (2 + (a + ((0 : ℕ) : ℝ))))
            / ((a + ((0 : ℕ) : ℝ)) ^ 2 + η ^ 2)
          = (1 + Real.log (2 + a)) / (a ^ 2 + η ^ 2) := by norm_num
      rw [he]
      refine div_le_div_of_nonneg_left hL0 (pow_pos ha0 2) ?_
      nlinarith [sq_nonneg η]
    linarith [htail, hf0, hfinal]

end Work.Parab.coordData
