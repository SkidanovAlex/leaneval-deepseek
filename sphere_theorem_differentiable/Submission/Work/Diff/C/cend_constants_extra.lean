import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

/-- Cube-root form of the smallness hypothesis: from `η ≤ 10⁻¹⁸ (n+2)⁻⁶` we get
`η^{1/3} ≤ 10⁻⁶ (n+2)⁻²`.  This is the sixth-power analogue of `delta_basics`; the key point is
that `(10⁶ (n+2)²)³ = 10¹⁸ (n+2)⁶`. -/
lemma delta_basics_extra {n : ℕ} {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / (10 ^ 18 * ((n : ℝ) + 2) ^ 6)) :
    η ^ (1 / 3 : ℝ) ≤ 1 / (10 ^ 6 * ((n : ℝ) + 2) ^ 2) := by
  have hδ0 : 0 < η ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hη0 _
  have hδ3 : (η ^ (1 / 3 : ℝ)) ^ 3 = η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη0.le]; norm_num
  have hkey : η ≤ (1 / (10 ^ 6 * ((n : ℝ) + 2) ^ 2)) ^ 3 := by
    have heq : (1 / (10 ^ 6 * ((n : ℝ) + 2) ^ 2)) ^ 3
        = 1 / (10 ^ 18 * ((n : ℝ) + 2) ^ 6) := by
      rw [div_pow, one_pow]; congr 1; ring
    rw [heq]; exact hη
  rw [← hδ3] at hkey
  exact (pow_le_pow_iff_left₀ hδ0.le (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp hkey

-- Pure real arithmetic.  With `δ = η^(1/3)`, `c = 100δ²`, `ε₁ = δ²`, `α = 1000δ` and the
-- smallness hypothesis `η ≤ 10⁻¹⁸ (n+2)⁻⁶` (note the SIXTH power: this gives `δ ≤ 10⁻⁶ (n+2)⁻²`,
-- not merely `10⁻⁶ (n+2)⁻¹`), one has `X := 100(n+2)(ε₁π + α + √c) ≥ 0` and
-- `(n+1) X < 1`.  Sketch: `ε₁π + α + √c = δ(δπ + 1010)`, and `δ ≤ 1/(10⁶(n+2)²)`,
-- `δ ≤ 10⁻⁶`, so `X ≤ (1/(10⁴(n+2)))(1010 + tiny) < 0.102/(n+2)` and
-- `(n+1)X < 0.102(n+1)/(n+2) < 1`.  (`delta_basics` in `Submission/Work/Diff/C/cend_constants.lean`
-- proves the analogue from the cube-power hypothesis; here we need the sixth power, so redo it
-- using `(10⁶(n+2)²)³ = 10¹⁸(n+2)⁶`.)
theorem cend_constants_extra {n : ℕ} (hn : 2 ≤ n) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / (10 ^ 18 * ((n : ℝ) + 2) ^ 6)) :
    let δ : ℝ := η ^ (1 / 3 : ℝ)
    let c : ℝ := 100 * δ ^ 2
    let ε₁ : ℝ := δ ^ 2
    let α : ℝ := 1000 * δ
    0 ≤ 100 * ((n : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) ∧
      ((n : ℝ) + 1) * (100 * ((n : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c)) < 1 := by
  dsimp only
  set δ : ℝ := η ^ (1 / 3 : ℝ) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; exact Real.rpow_pos_of_pos hη0 _
  -- `δ ≤ 10⁻⁶ (n+2)⁻²`
  have hδle : δ ≤ 1 / (10 ^ 6 * ((n : ℝ) + 2) ^ 2) := by
    rw [hδdef]; exact delta_basics_extra hη0 hη
  have hApos : (0 : ℝ) < (n : ℝ) + 2 := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- `√c = 10 δ`
  have hsqrt : Real.sqrt (100 * δ ^ 2) = 10 * δ := by
    rw [show (100 : ℝ) * δ ^ 2 = (10 * δ) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  -- `δ ≤ 10⁻⁶`
  have hδ1 : δ ≤ 1 / 10 ^ 6 := by
    have h16 : (1 : ℝ) ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith only [hApos]
    calc δ ≤ 1 / (10 ^ 6 * ((n : ℝ) + 2) ^ 2) := hδle
      _ ≤ 1 / (10 ^ 6 * 1) := one_div_le_one_div_of_le (by norm_num) (by nlinarith only [h16])
      _ = 1 / 10 ^ 6 := by norm_num
  -- `δ π + 1010 < 1011`
  have hπδ : δ * Real.pi ≤ 4 / 10 ^ 6 := by
    calc δ * Real.pi ≤ (1 / 10 ^ 6) * Real.pi := mul_le_mul_of_nonneg_right hδ1 Real.pi_pos.le
      _ ≤ (1 / 10 ^ 6) * 4 := mul_le_mul_of_nonneg_left Real.pi_lt_four.le (by norm_num)
      _ = 4 / 10 ^ 6 := by norm_num
  have hw : δ * Real.pi + 1010 < 1011 := by linarith only [hπδ]
  -- `(n+1)((n+2)δ) < 10⁻⁶`
  have hu : ((n : ℝ) + 1) * (((n : ℝ) + 2) * δ) < 1 / 10 ^ 6 := by
    have h1 : ((n : ℝ) + 2) * δ ≤ 1 / (10 ^ 6 * ((n : ℝ) + 2)) := by
      have h := mul_le_mul_of_nonneg_left hδle hApos.le
      have h2 : ((n : ℝ) + 2) * (1 / (10 ^ 6 * ((n : ℝ) + 2) ^ 2))
          = 1 / (10 ^ 6 * ((n : ℝ) + 2)) := by field_simp
      rwa [h2] at h
    have h2 : ((n : ℝ) + 1) / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one hApos]; linarith only
    calc ((n : ℝ) + 1) * (((n : ℝ) + 2) * δ)
        ≤ ((n : ℝ) + 1) * (1 / (10 ^ 6 * ((n : ℝ) + 2))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (1 / 10 ^ 6) * (((n : ℝ) + 1) / ((n : ℝ) + 2)) := by field_simp
      _ < (1 / 10 ^ 6) * 1 := mul_lt_mul_of_pos_left h2 (by norm_num)
      _ = 1 / 10 ^ 6 := by norm_num
  refine ⟨?_, ?_⟩
  · -- nonnegativity of `X`
    rw [hsqrt]
    have h1 : 0 ≤ δ ^ 2 * Real.pi := by positivity
    have h2 : 0 ≤ 1000 * δ := by linarith only [hδ0]
    have h3 : 0 ≤ 10 * δ := by linarith only [hδ0]
    have h4 : 0 ≤ δ ^ 2 * Real.pi + 1000 * δ + 10 * δ := by linarith only [h1, h2, h3]
    positivity
  · -- `(n+1) X < 1`
    rw [hsqrt]
    set u : ℝ := ((n : ℝ) + 1) * (((n : ℝ) + 2) * δ) with hudef
    set w : ℝ := δ * Real.pi + 1010 with hwdef
    have hu' : 0 < u := by rw [hudef]; positivity
    have hw' : 0 < w := by
      rw [hwdef]
      have : 0 ≤ δ * Real.pi := mul_nonneg hδ0.le Real.pi_pos.le
      linarith only [this]
    have key : ((n : ℝ) + 1) * (100 * ((n : ℝ) + 2) * (δ ^ 2 * Real.pi + 1000 * δ + 10 * δ))
        = 100 * u * w := by
      rw [hudef, hwdef]; ring
    rw [key]
    have hA : 100 * u * w < 100 * (1 / 10 ^ 6) * w := by
      have h := mul_lt_mul_of_pos_left hu (by positivity : (0 : ℝ) < 100 * w)
      rw [show (100 : ℝ) * w * u = 100 * u * w by ring,
          show (100 : ℝ) * w * (1 / 10 ^ 6) = 100 * (1 / 10 ^ 6) * w by ring] at h
      exact h
    have hB : 100 * (1 / 10 ^ 6) * w < 100 * (1 / 10 ^ 6) * 1011 :=
      mul_lt_mul_of_pos_left hw (by norm_num : (0 : ℝ) < 100 * (1 / 10 ^ 6))
    have hC : (100 : ℝ) * (1 / 10 ^ 6) * 1011 < 1 := by norm_num
    linarith only [hA, hB, hC]

end Work.Diff.C
