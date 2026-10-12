import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- Pointwise split of the lattice-shell profile against `m²j³`:
`(24 j² + 2)/((1+mj)²j³) ≤ 24/((1+mj)j) + 2/j³` for `j ≥ 1`. -/
lemma latSumOneDTwoCube_aux_term (m y : ℝ) (hm : 0 < m) (hy : 1 ≤ y) :
    (24 * y ^ 2 + 2) * (1 / ((1 + m * y) ^ 2 * y ^ 3))
      ≤ 24 * (1 / ((1 + m * y) * y)) + 2 / y ^ 3 := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hA : 0 < 1 + m * y := by nlinarith
  have hA1 : 1 ≤ 1 + m * y := by nlinarith
  have hD : 0 < (1 + m * y) ^ 2 * y ^ 3 := mul_pos (pow_pos hA 2) (pow_pos hy0 3)
  rw [mul_one_div, div_le_iff₀ hD]
  have h2 : (24 * (1 / ((1 + m * y) * y)) + 2 / y ^ 3) * ((1 + m * y) ^ 2 * y ^ 3)
      = 24 * (1 + m * y) * y ^ 2 + 2 * (1 + m * y) ^ 2 := by
    field_simp
  rw [h2]
  nlinarith [hA1, sq_nonneg y, sq_nonneg (1 + m * y),
    mul_nonneg (sub_nonneg.mpr hA1) (sq_nonneg y),
    mul_nonneg (sub_nonneg.mpr hA1) (sub_nonneg.mpr hA1)]

/-- `x ↦ 1/(x(1+mx))` is antitone on `[1,∞)`. -/
lemma latSumOneDTwoCube_aux_antitone (m : ℝ) (hm : 0 < m) :
    AntitoneOn (fun y : ℝ => 1 / (y * (1 + m * y))) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hAx : 0 < 1 + m * x := by nlinarith
  have hAy : 0 < 1 + m * y := by nlinarith
  have hxy' : x * (1 + m * x) ≤ y * (1 + m * y) :=
    mul_le_mul hxy (by nlinarith) (le_of_lt hAx) (le_of_lt hy0)
  exact one_div_le_one_div_of_le (mul_pos hx0 hAx) hxy'

/-- `∫_1^b dx/(x(1+mx)) ≤ log (1 + 1/m)` for `b ≥ 1` (the exact value is
`log b - log (1+mb) + log (1+m)`, bounded by `log (1/m) + log (1+m)`). -/
lemma latSumOneDTwoCube_aux_integral (m : ℝ) (hm : 0 < m) {b : ℝ} (hb : 1 ≤ b) :
    (∫ x in (1 : ℝ)..b, 1 / (x * (1 + m * x))) ≤ Real.log (1 + 1 / m) := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hmb : 0 < 1 + m * b := by nlinarith
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) b,
      HasDerivAt (fun z : ℝ => Real.log z - Real.log (1 + m * z))
        (1 / (x * (1 + m * x))) x := by
    intro x hx
    rw [Set.uIcc_of_le hb] at hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
    have hA : 1 + m * x ≠ 0 := by
      have : 0 < 1 + m * x := by nlinarith
      exact ne_of_gt this
    have h1 : HasDerivAt (fun z : ℝ => Real.log z) x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx0)
    have hlin : HasDerivAt (fun z : ℝ => 1 + m * z) m x := by
      have h : HasDerivAt (fun z : ℝ => m * z) m x := by
        simpa using (hasDerivAt_id (𝕜 := ℝ) x).const_mul m
      exact h.const_add 1
    have h2 : HasDerivAt (fun z : ℝ => Real.log (1 + m * z)) (m / (1 + m * x)) x :=
      hlin.log hA
    have h3 := h1.sub h2
    have hval : x⁻¹ - m / (1 + m * x) = 1 / (x * (1 + m * x)) := by
      field_simp
      ring
    rwa [hval] at h3
  have hintg : IntervalIntegrable (fun x : ℝ => 1 / (x * (1 + m * x)))
      MeasureTheory.volume (1 : ℝ) b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hb]
    have hcont : ContinuousOn (fun x : ℝ => x * (1 + m * x)) (Set.Icc (1 : ℝ) b) := by fun_prop
    have hne : ∀ x ∈ Set.Icc (1 : ℝ) b, x * (1 + m * x) ≠ 0 := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
      exact ne_of_gt (mul_pos hx0 (by nlinarith))
    refine ContinuousOn.div continuousOn_const hcont hne
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintg
  rw [hmain]
  have hle : b / (1 + m * b) ≤ 1 / m := by
    rw [div_le_iff₀ hmb]
    have h : (1 / m) * (1 + m * b) = 1 / m + b := by field_simp
    rw [h]
    have : 0 < 1 / m := one_div_pos.mpr hm
    linarith
  have hlog1 : Real.log (b / (1 + m * b)) ≤ Real.log (1 / m) :=
    Real.log_le_log (div_pos hb0 hmb) hle
  have hlog2 : Real.log (b / (1 + m * b)) = Real.log b - Real.log (1 + m * b) :=
    Real.log_div (ne_of_gt hb0) (ne_of_gt hmb)
  have hsum : Real.log (1 / m) + Real.log (1 + m) = Real.log (1 + 1 / m) := by
    rw [← Real.log_mul (ne_of_gt (one_div_pos.mpr hm)) (ne_of_gt (by linarith : (0 : ℝ) < 1 + m))]
    congr 1
    field_simp
    ring
  rw [Real.log_one]
  simp only [mul_one]
  linarith [hlog1, hlog2, hsum]

/-- `Σ_{j=1}^{N} 1/((1+mj)j) ≤ 1 + log (1 + 1/m)`: peel the `j = 1` term (bounded by `1`) and
compare the rest with the integral of the antitone function `x ↦ 1/(x(1+mx))`. -/
lemma latSumOneDTwoCube_aux_sumG (m : ℝ) (hm : 0 < m) (N : ℕ) :
    (∑ j ∈ Finset.range N, 1 / ((1 + m * ((j : ℝ) + 1)) * ((j : ℝ) + 1)))
      ≤ 1 + Real.log (1 + 1 / m) := by
  have hlog_nn : 0 ≤ Real.log (1 + 1 / m) :=
    Real.log_nonneg (by linarith [one_div_pos.mpr hm])
  have hanti := latSumOneDTwoCube_aux_antitone m hm
  induction N with
  | zero => simp only [Finset.sum_range_zero]; linarith
  | succ k ih =>
    rw [Finset.sum_range_succ']
    have ht0le : (1 : ℝ) / ((1 + m * (((0 : ℕ) : ℝ) + 1)) * (((0 : ℕ) : ℝ) + 1)) ≤ 1 := by
      have ht0 : (1 : ℝ) / ((1 + m * (((0 : ℕ) : ℝ) + 1)) * (((0 : ℕ) : ℝ) + 1))
          = 1 / (1 + m) := by norm_num
      rw [ht0, div_le_iff₀ (by linarith : (0 : ℝ) < 1 + m)]
      linarith
    have hsum_le :
        (∑ j ∈ Finset.range k, 1 / ((1 + m * (((j + 1 : ℕ) : ℝ) + 1)) * (((j + 1 : ℕ) : ℝ) + 1)))
          ≤ Real.log (1 + 1 / m) := by
      calc (∑ j ∈ Finset.range k,
              1 / ((1 + m * (((j + 1 : ℕ) : ℝ) + 1)) * (((j + 1 : ℕ) : ℝ) + 1)))
          = ∑ j ∈ Finset.range k,
              (fun y : ℝ => 1 / (y * (1 + m * y))) (1 + (((j + 1 : ℕ) : ℝ))) := by
            apply Finset.sum_congr rfl
            intro j _
            ring_nf
        _ ≤ ∫ x in (1 : ℝ)..(1 + (k : ℝ)), 1 / (x * (1 + m * x)) :=
            AntitoneOn.sum_le_integral (x₀ := (1 : ℝ)) (a := k)
              (hanti.mono Set.Icc_subset_Ici_self)
        _ ≤ Real.log (1 + 1 / m) :=
            latSumOneDTwoCube_aux_integral m hm (by
              have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
              linarith)
    linarith

/-- `Σ_{j≤N} 1/(j+1)³ ≤ 2` (telescoping with `1/(j+2) - 1/(j+3)`). -/
lemma latSumOneDTwoCube_aux_sumCube (N : ℕ) :
    (∑ j ∈ Finset.range N, 1 / ((j : ℝ) + 1) ^ 3) ≤ 2 := by
  have htel : ∀ k : ℕ,
      (∑ j ∈ Finset.range k, (1 / ((j : ℝ) + 2) - 1 / ((j : ℝ) + 3)))
        = 1 / 2 - 1 / ((k : ℝ) + 2) := by
    intro k
    induction k with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  induction N with
  | zero => simp
  | succ k _ =>
    rw [Finset.sum_range_succ']
    have h0 : (1 : ℝ) / ((((0 : ℕ) : ℝ) + 1)) ^ 3 = 1 := by norm_num
    rw [h0]
    have hshift : (∑ j ∈ Finset.range k, 1 / ((((j + 1 : ℕ) : ℝ)) + 1) ^ 3)
        = ∑ j ∈ Finset.range k, 1 / ((j : ℝ) + 2) ^ 3 := by
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    rw [hshift]
    have hkey : (∑ j ∈ Finset.range k, 1 / ((j : ℝ) + 2) ^ 3) ≤ 1 := by
      calc (∑ j ∈ Finset.range k, 1 / ((j : ℝ) + 2) ^ 3)
          ≤ ∑ j ∈ Finset.range k, (1 / ((j : ℝ) + 2) - 1 / ((j : ℝ) + 3)) := by
            apply Finset.sum_le_sum
            intro j _
            have hy : (2 : ℝ) ≤ (j : ℝ) + 2 := by
              have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
              linarith
            have hy0 : 0 < (j : ℝ) + 2 := by linarith
            have hy3 : 0 < (j : ℝ) + 3 := by linarith
            have hprod : 0 < ((j : ℝ) + 2) * ((j : ℝ) + 3) := mul_pos hy0 hy3
            have hle : ((j : ℝ) + 2) * ((j : ℝ) + 3) ≤ ((j : ℝ) + 2) ^ 3 := by nlinarith
            have hstep : 1 / (((j : ℝ) + 2) ^ 3) ≤ 1 / (((j : ℝ) + 2) * ((j : ℝ) + 3)) :=
              one_div_le_one_div_of_le hprod hle
            have hdist : 1 / (((j : ℝ) + 2) * ((j : ℝ) + 3))
                = 1 / ((j : ℝ) + 2) - 1 / ((j : ℝ) + 3) := by
              field_simp
              ring
            linarith [hstep, hdist]
        _ = 1 / 2 - 1 / ((k : ℝ) + 2) := htel k
        _ ≤ 1 := by
            have hk : 0 < (k : ℝ) + 2 := by
              have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
              linarith
            have hpos : 0 < 1 / ((k : ℝ) + 2) := one_div_pos.mpr hk
            linarith
    linarith

/-- One-dimensional profile sum, `(2,3)` case: the lattice-shell profile `24 j² + 2` against
`1 / ((1 + m j)² j³)`.  True value of the full series is `≤ 27 (1 + log (2 + 1/m))` for all `m > 0`;
the constant `100` is deliberately generous.  Used to bound the `ℤ³` lattice sum
`Σ_n 1/((1+m‖n‖)² ‖n‖³)`. -/
theorem latSumOneDTwoCube (m : ℝ) (hm : 0 < m) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1),
        (24 * (j : ℝ) ^ 2 + 2) * (1 / ((1 + m * (j : ℝ)) ^ 2 * (j : ℝ) ^ 3)))
      ≤ 100 * (1 + Real.log (2 + 1 / m)) := by
  have hterm : ∀ k : ℕ,
      (24 * ((k + 1 : ℕ) : ℝ) ^ 2 + 2)
          * (1 / ((1 + m * ((k + 1 : ℕ) : ℝ)) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 3))
        ≤ 24 * (1 / ((1 + m * ((k : ℝ) + 1)) * ((k : ℝ) + 1)))
          + 2 / ((k : ℝ) + 1) ^ 3 := by
    intro k
    have hy : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hp := latSumOneDTwoCube_aux_term m ((k : ℝ) + 1) hm hy
    simpa using hp
  rw [Finset.sum_range_succ']
  have hf0 : (24 * (((0 : ℕ) : ℝ)) ^ 2 + 2)
      * (1 / ((1 + m * (((0 : ℕ) : ℝ))) ^ 2 * (((0 : ℕ) : ℝ)) ^ 3)) = 0 := by norm_num
  rw [hf0, add_zero]
  calc (∑ k ∈ Finset.range J,
        (24 * ((k + 1 : ℕ) : ℝ) ^ 2 + 2)
          * (1 / ((1 + m * ((k + 1 : ℕ) : ℝ)) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 3)))
      ≤ ∑ k ∈ Finset.range J,
          (24 * (1 / ((1 + m * ((k : ℝ) + 1)) * ((k : ℝ) + 1))) + 2 / ((k : ℝ) + 1) ^ 3) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = 24 * (∑ k ∈ Finset.range J, 1 / ((1 + m * ((k : ℝ) + 1)) * ((k : ℝ) + 1)))
          + 2 * (∑ k ∈ Finset.range J, 1 / ((k : ℝ) + 1) ^ 3) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        simp only [mul_one_div]
    _ ≤ 24 * (1 + Real.log (1 + 1 / m)) + 2 * 2 := by
        have h1 := latSumOneDTwoCube_aux_sumG m hm J
        have h2 := latSumOneDTwoCube_aux_sumCube J
        linarith
    _ ≤ 100 * (1 + Real.log (2 + 1 / m)) := by
        have hlog_nn : 0 ≤ Real.log (1 + 1 / m) :=
          Real.log_nonneg (by linarith [one_div_pos.mpr hm])
        have hlog_le : Real.log (1 + 1 / m) ≤ Real.log (2 + 1 / m) :=
          Real.log_le_log (by linarith [one_div_pos.mpr hm]) (by linarith)
        linarith

end Work.BoseBogFS
