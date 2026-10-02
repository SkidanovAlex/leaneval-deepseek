import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.r2_setup
import Submission.Work.Deep.Nibble.r2_num_basic

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The dense-regime numerical bounds of round 2

In the dense regime (`nThresh r θ δ D > n`) we must produce, for all large `D ≤ n`,
the three numerical bounds

* `8 * qV r ε' θ D * n ≤ log 2`,
* `2 r / (δ² θ n) ≤ exp (-(8 qV n)) / 12`,
* `64 r / (δ² θ³ n) ≤ exp (-(8 qV n)) / 12`.

All the asymptotic content is already in `r2_num_basic` (in particular
`qV r ε' θ D * nThresh r θ δ D ≤ 1/16` together with `48 r ≤ δ² θ D` and
`1536 r ≤ δ² θ³ D`); the only extra numerical input is `1/2 ≤ log 2`.
-/

namespace Work.Deep.Nibble

/-- A weak explicit lower bound for `Real.log 2`: `1 / 2 ≤ log 2`. -/
lemma half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  linarith [Real.log_two_gt_d9]

theorem r2_num_dense {r : ℕ} (hr : 2 ≤ r) {θ δ ε' ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100) (hδ0 : 0 < δ) (hδ1 : δ ≤ θ / 100)
    (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1 / 2) (hε'2 : 100 * (ε + ε * (r : ℝ) * θ) ≤ ε')
    (hε0 : 0 < ε) (hε1 : ε ≤ θ / 100) (hεδ : 4 * ε ≤ δ) :
    ∃ N : ℕ, ∀ (D n : ℕ), N ≤ D → D ≤ n → ¬ (Work.Deep.Nibble.nThresh r θ δ D ≤ (n:ℝ)) →
      (8 * Work.Deep.Nibble.qV r ε' θ D * (n:ℝ) ≤ Real.log 2)
      ∧ (2 * (r:ℝ) / (δ^2 * θ * (n:ℝ)) ≤ Real.exp (-(8 * Work.Deep.Nibble.qV r ε' θ D * (n:ℝ))) / 12)
      ∧ (64 * (r:ℝ) / (δ^2 * θ^3 * (n:ℝ)) ≤ Real.exp (-(8 * Work.Deep.Nibble.qV r ε' θ D * (n:ℝ))) / 12) := by
  obtain ⟨N, hN⟩ := r2_num_basic hr hθ0 hθ1 hδ0 hδ1 hε'0 hε'1 hε'2 hε0 hε1 hεδ
  refine ⟨N, fun D n hND hDn hn => ?_⟩
  obtain ⟨hD1, _, _, _, _, _, _, _, _, hqVnT, h48, h1536, _, _⟩ := hN D hND
  have hnlt : (n : ℝ) < nThresh r θ δ D := not_le.mp hn
  have hn1 : 1 ≤ n := le_trans hD1 hDn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hDnR : (D : ℝ) ≤ (n : ℝ) := by exact_mod_cast hDn
  have hqVpos : 0 < qV r ε' θ D := by
    rw [qV]; positivity
  -- The first bound: `8 qV n ≤ log 2`, a consequence of `qV * nThresh ≤ 1/16`
  -- together with `n < nThresh`.
  have hgoal1 : 8 * qV r ε' θ D * (n : ℝ) ≤ Real.log 2 := by
    have hlt : qV r ε' θ D * (n : ℝ) < qV r ε' θ D * nThresh r θ δ D :=
      mul_lt_mul_of_pos_left hnlt hqVpos
    have h2 : 8 * (qV r ε' θ D * (n : ℝ)) < 8 * (qV r ε' θ D * nThresh r θ δ D) :=
      mul_lt_mul_of_pos_left hlt (by norm_num)
    have h3 : 8 * (qV r ε' θ D * nThresh r θ δ D) ≤ 1 / 2 := by
      have h4 := mul_le_mul_of_nonneg_left hqVnT (by norm_num : (0:ℝ) ≤ 8)
      linarith
    have h5 : 8 * qV r ε' θ D * (n : ℝ) = 8 * (qV r ε' θ D * (n : ℝ)) := by ring
    rw [h5]
    exact le_of_lt (lt_of_lt_of_le h2 (le_trans h3 half_le_log_two))
  -- Consequently `exp (-(8 qV n)) ≥ exp (-log 2) = 1/2`.
  have hexplb : (1 : ℝ) / 2 ≤ Real.exp (-(8 * qV r ε' θ D * (n : ℝ))) := by
    have hneg : -(Real.log 2) ≤ -(8 * qV r ε' θ D * (n : ℝ)) := by linarith
    calc (1 : ℝ) / 2 = Real.exp (-(Real.log 2)) := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
          norm_num
      _ ≤ Real.exp (-(8 * qV r ε' θ D * (n : ℝ))) := Real.exp_le_exp.mpr hneg
  have hRHS : (1 : ℝ) / 24 ≤ Real.exp (-(8 * qV r ε' θ D * (n : ℝ))) / 12 := by
    calc (1 : ℝ) / 24 = (1 / 12) * ((1 : ℝ) / 2) := by norm_num
      _ ≤ (1 / 12) * Real.exp (-(8 * qV r ε' θ D * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hexplb (by norm_num)
      _ = Real.exp (-(8 * qV r ε' θ D * (n : ℝ))) / 12 := by ring
  refine ⟨hgoal1, ?_, ?_⟩
  · -- `2 r / (δ² θ n) ≤ 1/24 ≤ exp (-(8 qV n)) / 12`
    refine le_trans ?_ hRHS
    have hDnθ : δ^2 * θ * (D : ℝ) ≤ δ^2 * θ * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hDnR (by positivity)
    have h48n : 48 * (r : ℝ) ≤ δ^2 * θ * (n : ℝ) := le_trans h48 hDnθ
    have hpos : (0 : ℝ) < δ^2 * θ * (n : ℝ) :=
      mul_pos (mul_pos (pow_pos hδ0 2) hθ0) hnR
    rw [div_le_iff₀ hpos]
    calc 2 * (r : ℝ) = (1 / 24) * (48 * (r : ℝ)) := by ring
      _ ≤ (1 / 24) * (δ^2 * θ * (n : ℝ)) := mul_le_mul_of_nonneg_left h48n (by norm_num)
  · -- `64 r / (δ² θ³ n) ≤ 1/24 ≤ exp (-(8 qV n)) / 12`
    refine le_trans ?_ hRHS
    have hDnθ : δ^2 * θ^3 * (D : ℝ) ≤ δ^2 * θ^3 * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hDnR (by positivity)
    have h1536n : 1536 * (r : ℝ) ≤ δ^2 * θ^3 * (n : ℝ) := le_trans h1536 hDnθ
    have hpos : (0 : ℝ) < δ^2 * θ^3 * (n : ℝ) :=
      mul_pos (mul_pos (pow_pos hδ0 2) (pow_pos hθ0 3)) hnR
    rw [div_le_iff₀ hpos]
    calc 64 * (r : ℝ) = (1 / 24) * (1536 * (r : ℝ)) := by ring
      _ ≤ (1 / 24) * (δ^2 * θ^3 * (n : ℝ)) := mul_le_mul_of_nonneg_left h1536n (by norm_num)

end Work.Deep.Nibble
