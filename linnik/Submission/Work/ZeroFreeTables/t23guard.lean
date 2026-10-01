import Mathlib

namespace Work.ZeroFreeTables

/-- For `q` large (in terms of a fixed `δ > 0`) and a real `β < 1` with
`(1 - β) · log q ≤ 2/5`, the point `β` is within `δ` of `1` in the real part and within
HB's §6 point range: `|1 - β| ≤ √(log log q)/log q`.

(Proof: `λ(β) = (1-β)log q ≤ 2/5` and `β < 1` give `0 < 1 - β ≤ (2/5)/log q`; take
`q₀ ≥ max 4 (exp (2/(5δ)))`: then `log q > 0`, `log log q ≥ log log 4 > 4/25` so that
`√(log log q) ≥ 2/5`, and `(2/5)/log q ≤ δ`.) -/
theorem t23guard (δ : ℝ) (hδ : 0 < δ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ β : ℝ,
      β < 1 → (1 - β) * Real.log (q : ℝ) ≤ 2 / 5 →
      |1 - β| ≤ δ ∧
        |1 - β| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
  refine ⟨max (Nat.ceil (Real.exp (2 / (5 * δ)))) (Nat.ceil (Real.exp (Real.exp 1))), ?_⟩
  intro q hq β hβ h
  -- bounds on `q`
  have hq1 : Nat.ceil (Real.exp (2 / (5 * δ))) ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : Nat.ceil (Real.exp (Real.exp 1)) ≤ q := le_trans (le_max_right _ _) hq
  have hexp1 : Real.exp (2 / (5 * δ)) ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hq1)
  have hexp2 : Real.exp (Real.exp 1) ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hq2)
  -- `log q > 0`
  have hqgt1 : 1 < (q : ℝ) := by
    have hone : (1 : ℝ) < Real.exp (Real.exp 1) :=
      Real.one_lt_exp_iff.mpr (Real.exp_pos 1)
    linarith
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos hqgt1
  -- `exp 1 ≤ log q`
  have hlog1 : Real.exp 1 ≤ Real.log (q : ℝ) := by
    have := Real.log_le_log (Real.exp_pos (Real.exp 1)) hexp2
    rwa [Real.log_exp] at this
  -- `1 ≤ log log q`
  have hloglog1 : 1 ≤ Real.log (Real.log (q : ℝ)) := by
    have := Real.log_le_log (Real.exp_pos 1) hlog1
    rwa [Real.log_exp] at this
  -- `2/(5δ) ≤ log q`
  have hlog2 : 2 / (5 * δ) ≤ Real.log (q : ℝ) := by
    have := Real.log_le_log (Real.exp_pos (2 / (5 * δ))) hexp1
    rwa [Real.log_exp] at this
  -- `0 < 1 - β` and `|1 - β| = 1 - β`
  have hLpos : 0 < 1 - β := by linarith
  have habs : |1 - β| = 1 - β := abs_of_pos hLpos
  -- `1 - β ≤ (2/5)/log q`
  have hLle : 1 - β ≤ (2 / 5) / Real.log (q : ℝ) := by
    rw [le_div_iff₀ hlogpos]
    linarith
  -- `(2/5)/log q ≤ δ`
  have hδlog : (2 : ℝ) / 5 ≤ δ * Real.log (q : ℝ) := by
    have hmul : δ * (2 / (5 * δ)) = 2 / 5 := by field_simp
    calc (2 : ℝ) / 5 = δ * (2 / (5 * δ)) := hmul.symm
      _ ≤ δ * Real.log (q : ℝ) := mul_le_mul_of_nonneg_left hlog2 hδ.le
  have hLleδ : (2 / 5) / Real.log (q : ℝ) ≤ δ := (div_le_iff₀ hlogpos).mpr hδlog
  -- `2/5 ≤ sqrt (log log q)`
  have hsqrt : (2 : ℝ) / 5 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    have h45 : (4 : ℝ) / 25 ≤ Real.log (Real.log (q : ℝ)) :=
      le_trans (by norm_num) hloglog1
    have hs := Real.sqrt_le_sqrt h45
    have hsqrt45 : Real.sqrt ((4 : ℝ) / 25) = 2 / 5 := by
      rw [show (4 : ℝ) / 25 = ((2 : ℝ) / 5) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rwa [hsqrt45] at hs
  have hLleSqrt : (2 / 5) / Real.log (q : ℝ) ≤
      Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) :=
    div_le_div_of_nonneg_right hsqrt hlogpos.le
  exact ⟨by rw [habs]; exact le_trans hLle hLleδ,
         by rw [habs]; exact le_trans hLle hLleSqrt⟩

end Work.ZeroFreeTables
