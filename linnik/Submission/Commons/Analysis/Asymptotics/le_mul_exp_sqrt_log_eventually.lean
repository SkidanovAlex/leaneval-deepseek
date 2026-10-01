import Mathlib
import Submission.Commons.Analysis.Asymptotics.eventually_polylog_le_exp_sub_sqrt

namespace Commons.Analysis.Asymptotics

/-- For any real `P`, `x₀` and any `δ > 0`, the quantity
`P * exp (x₀ * sqrt (log L)) * (1 + log L)^5` is eventually bounded by `δ * L`.
The factor `exp (x₀ * sqrt (log L)) * (1 + log L)^5` grows subpolynomially in `L`. -/
theorem le_mul_exp_sqrt_log_eventually {P x₀ δ : ℝ} (hδ : 0 < δ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      P * Real.exp (x₀ * Real.sqrt (Real.log L)) * (1 + Real.log L) ^ 5 ≤ δ * L := by
  by_cases hP : P ≤ 0
  · -- Case `P ≤ 0`: for `L ≥ 1` the left-hand side is `≤ 0 ≤ δ * L`.
    refine ⟨1, le_refl 1, ?_⟩
    intro L hL
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
    have hpow : 0 ≤ (1 + Real.log L) ^ 5 := pow_nonneg (by linarith) 5
    have hleft : P * Real.exp (x₀ * Real.sqrt (Real.log L)) * (1 + Real.log L) ^ 5 ≤ 0 := by
      have hexpnn : 0 ≤ Real.exp (x₀ * Real.sqrt (Real.log L)) := Real.exp_nonneg _
      have h1 : P * Real.exp (x₀ * Real.sqrt (Real.log L)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hP hexpnn
      exact mul_nonpos_of_nonpos_of_nonneg h1 hpow
    have hright : 0 ≤ δ * L := mul_nonneg (le_of_lt hδ) (by linarith)
    linarith
  · -- Case `P > 0`.
    have hPpos : 0 < P := not_le.mp hP
    set A : ℝ := max x₀ 1 with hAdef
    have hA1 : 1 ≤ A := le_max_right _ _
    have hApos : 0 < A := lt_of_lt_of_le one_pos hA1
    have hxA : x₀ ≤ A := le_max_left _ _
    set C : ℝ := 32 * P / δ with hCdef
    have hCpos : 0 < C := by rw [hCdef]; positivity
    have hCnonneg : 0 ≤ C := le_of_lt hCpos
    obtain ⟨X, hX⟩ := eventually_polylog_le_exp_sub_sqrt A hApos 5 C hCnonneg
    refine ⟨max X (Real.exp 1), ?_, ?_⟩
    · -- `1 ≤ max X (exp 1)`
      have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      exact le_trans h1e (le_max_right _ _)
    · intro L hL
      have hLX : X ≤ L := le_trans (le_max_left _ _) hL
      have hLe : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
      have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
      have hlogL1 : 1 ≤ Real.log L := by
        have h := Real.log_le_log (Real.exp_pos 1) hLe
        rwa [Real.log_exp] at h
      set s : ℝ := Real.sqrt (Real.log L) with hsdef
      have hsnn : 0 ≤ s := Real.sqrt_nonneg _
      -- (a) `exp (x₀ s) ≤ exp (A s)` since `x₀ ≤ A` and `s ≥ 0`.
      have hxa : x₀ * s ≤ A * s := mul_le_mul_of_nonneg_right hxA hsnn
      have hexp_le : Real.exp (x₀ * s) ≤ Real.exp (A * s) := Real.exp_le_exp.mpr hxa
      -- (b) `(1 + log L)^5 ≤ 32 (log L)^5`.
      have hpow_le : (1 + Real.log L) ^ 5 ≤ 32 * (Real.log L) ^ 5 := by
        have htwo : 1 + Real.log L ≤ 2 * Real.log L := by linarith
        have h1 : (1 + Real.log L) ^ 5 ≤ (2 * Real.log L) ^ 5 :=
          pow_le_pow_left₀ (by linarith) htwo 5
        have h2 : (2 * Real.log L) ^ 5 = 32 * (Real.log L) ^ 5 := by ring
        linarith [h1, h2]
      -- (c) The polylog-domination lemma.
      have hcu : C * (Real.log L) ^ 5 ≤ Real.exp (Real.log L - A * s) := by
        have h := hX L hLX
        rwa [← hsdef] at h
      -- Multiply by `exp (A s) > 0` and use `exp (log L) = L`.
      have hmult : C * (Real.log L) ^ 5 * Real.exp (A * s) ≤ L := by
        have hpos : 0 < Real.exp (A * s) := Real.exp_pos _
        have h1 := mul_le_mul_of_nonneg_right hcu (le_of_lt hpos)
        have heq : Real.exp (Real.log L - A * s) * Real.exp (A * s) = L := by
          rw [← Real.exp_add, show Real.log L - A * s + A * s = Real.log L by ring]
          exact Real.exp_log hLpos
        linarith [h1, heq]
      -- Turn `C = 32 P / δ` into `32 P (log L)^5 exp (A s) ≤ δ L`.
      have hmain : 32 * P * ((Real.log L) ^ 5 * Real.exp (A * s)) ≤ δ * L := by
        rw [hCdef] at hmult
        have h1 : δ * ((32 * P / δ) * (Real.log L) ^ 5 * Real.exp (A * s)) ≤ δ * L :=
          mul_le_mul_of_nonneg_left hmult (le_of_lt hδ)
        have hsimp : δ * ((32 * P / δ) * (Real.log L) ^ 5 * Real.exp (A * s))
            = 32 * P * ((Real.log L) ^ 5 * Real.exp (A * s)) := by
          have hδne : δ ≠ 0 := ne_of_gt hδ
          field_simp
        linarith [h1, hsimp]
      -- Chain the two bounds.
      have hstep : P * Real.exp (x₀ * s) * (1 + Real.log L) ^ 5
          ≤ 32 * P * ((Real.log L) ^ 5 * Real.exp (A * s)) := by
        have h1 : Real.exp (x₀ * s) * (1 + Real.log L) ^ 5
            ≤ Real.exp (A * s) * (32 * (Real.log L) ^ 5) :=
          mul_le_mul hexp_le hpow_le (by positivity) (Real.exp_nonneg _)
        have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hPpos)
        calc P * Real.exp (x₀ * s) * (1 + Real.log L) ^ 5
            = P * (Real.exp (x₀ * s) * (1 + Real.log L) ^ 5) := by ring
          _ ≤ P * (Real.exp (A * s) * (32 * (Real.log L) ^ 5)) := h2
          _ = 32 * P * ((Real.log L) ^ 5 * Real.exp (A * s)) := by ring
      linarith [hstep, hmain]

end Commons.Analysis.Asymptotics
