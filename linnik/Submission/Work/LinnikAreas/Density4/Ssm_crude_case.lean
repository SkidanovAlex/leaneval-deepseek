import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup
import Submission.Work.LinnikAreas.Density4.Ssm_crude_bound
import Submission.Work.LinnikAreas.Density4.zeroDetAux

namespace Work.LinnikAreas.Density4

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-- Squaring the divisor bound `τ(n) ≤ C·n^{1/2}` gives `τ(n)² ≤ C²·n`. -/
lemma card_divisors_sq_le {C : ℝ} (n : ℕ)
    (h : ((n.divisors.card : ℕ) : ℝ) ≤ C * (n : ℝ) ^ (1/2 : ℝ)) :
    ((n.divisors.card : ℕ) : ℝ) ^ 2 ≤ C ^ 2 * (n : ℝ) := by
  have hs : ((n : ℝ) ^ (1/2 : ℝ)) ^ 2 = (n : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hnn : (0 : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((n.divisors.card : ℕ) : ℝ) ^ 2 ≤ (C * (n : ℝ) ^ (1/2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hnn h 2
    _ = C ^ 2 * (n : ℝ) := by rw [mul_pow, hs]

theorem Ssm_crude_case (u v w x : ℝ) (hw : 0 < w) (huv : u < v) (hvx : v < x) (hx : 0 < x) (Q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 2 ≤ q → q < Q → ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      0 ≤ ρ.re →
      ‖Work.LinnikAreas.Density4.Ssm q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) ((q:ℝ)^x) χ ρ‖
        ≤ C / Real.log q := by
  -- Absolute constant from the divisor bound with exponent `1/2`.
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (1/2) (by norm_num)
  set B : ℝ := C0 ^ 2 with hBdef
  have hBpos : 0 < B := by rw [hBdef]; positivity
  by_cases hQle : Q ≤ 2
  · -- Empty range of levels.
    refine ⟨1, one_pos, ?_⟩
    intro q _ hq2 hqQ
    exfalso
    omega
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    have : 2 < Q := lt_of_not_ge hQle
    exact_mod_cast (by omega : 0 < Q)
  -- Uniform bound at the top level `Q`.
  set M : ℝ := B * ((Q : ℝ) ^ x + 1) ^ 3 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  refine ⟨M * max (Real.log (Q : ℝ)) 1 + 1, by positivity, ?_⟩
  intro q _ hq2 hqQ χ ρ hβ
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hqQ' : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (le_of_lt hqQ)
  have hU : (0 : ℝ) < (q : ℝ) ^ u := Real.rpow_pos_of_pos hqpos u
  have hX1 : (1 : ℝ) ≤ (q : ℝ) ^ x := Real.one_le_rpow (by linarith) hx.le
  -- The pointwise bound `‖mollCoeff‖ ≤ B·n` for the crude bound.
  have hbound : ∀ n : ℕ, ‖mollCoeff q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) χ n‖ ≤ B * (n : ℝ) := by
    intro n
    calc ‖mollCoeff q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) χ n‖
        ≤ ((n.divisors.card : ℕ) : ℝ) ^ 2 := norm_mollCoeff_le q hU χ n
      _ ≤ B * (n : ℝ) := by
            rw [hBdef]
            exact card_divisors_sq_le n (hC0 n)
  have hcrude := Ssm_crude_bound q (U := (q:ℝ)^u) (V := (q:ℝ)^v) (W := (q:ℝ)^w)
    (X := (q:ℝ)^x) hU hX1 χ hβ hBpos hbound
  have hXQ : (q : ℝ) ^ x ≤ (Q : ℝ) ^ x := Real.rpow_le_rpow hqpos.le hqQ' hx.le
  have hle : ‖Ssm q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) ((q:ℝ)^x) χ ρ‖ ≤ M := by
    refine le_trans hcrude ?_
    rw [hMdef]
    apply mul_le_mul_of_nonneg_left _ hBpos.le
    exact pow_le_pow_left₀ (by linarith [Real.rpow_nonneg hqpos.le x]) (by linarith) 3
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  have hlogq_le : Real.log (q : ℝ) ≤ Real.log (Q : ℝ) := Real.log_le_log hqpos hqQ'
  have hmax : Real.log (q : ℝ) ≤ max (Real.log (Q : ℝ)) 1 :=
    le_trans hlogq_le (le_max_left _ _)
  rw [le_div_iff₀ hlogq_pos]
  calc ‖Ssm q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) ((q:ℝ)^x) χ ρ‖ * Real.log (q : ℝ)
      ≤ M * Real.log (q : ℝ) := mul_le_mul_of_nonneg_right hle hlogq_pos.le
    _ ≤ M * max (Real.log (Q : ℝ)) 1 := mul_le_mul_of_nonneg_left hmax hMpos.le
    _ ≤ M * max (Real.log (Q : ℝ)) 1 + 1 := le_add_of_nonneg_right zero_le_one

end
end Work.LinnikAreas.Density4
