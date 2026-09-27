import Mathlib
import Submission.Work.EKLC7.TentDef

/-!
# Pointwise convergence of the tent functions to the indicator of `Ioc a b`

For rationals `a b` and real `t`, the tent functions

`tentFormula a b n t = max 0 (min 1 (min (n * (t - a)) (1 + n * (b - t))))`

converge, as `n → ∞`, to the indicator of the half open interval `Ioc a b`:
for large `n` the function equals `1` inside `Ioc a b` and `0` outside it.

This is the pointwise convergence used in the argument that the tent functions
determine a locally finite measure on `ℝ`.
-/

namespace Work.EKLC7

/-! ## Elementary evaluations of the tent function -/

/-- If `t ≤ a` then the tent function vanishes (the left slope has not started yet). -/
lemma ttf_eq_zero_of_le (a b : ℚ) (n : ℕ) (t : ℝ) (ht : t ≤ (a : ℝ)) :
    tentFormula a b n t = 0 := by
  have hA : (n : ℝ) * (t - (a : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (by linarith)
  have h1 : min ((n : ℝ) * (t - (a : ℝ))) (1 + (n : ℝ) * ((b : ℝ) - t)) ≤ 0 :=
    le_trans (min_le_left _ _) hA
  have h2 : min 1 (min ((n : ℝ) * (t - (a : ℝ))) (1 + (n : ℝ) * ((b : ℝ) - t))) ≤ 0 :=
    le_trans (min_le_right _ _) h1
  rw [tentFormula]
  exact max_eq_left h2

/-- If `n * (t - a) ≥ 1` and `t ≤ b` then the tent function equals `1`. -/
lemma ttf_eq_one_of (a b : ℚ) (n : ℕ) (t : ℝ)
    (h1 : 1 ≤ (n : ℝ) * (t - (a : ℝ))) (h2 : t ≤ (b : ℝ)) :
    tentFormula a b n t = 1 := by
  have hB : 1 ≤ 1 + (n : ℝ) * ((b : ℝ) - t) := by
    have : 0 ≤ (n : ℝ) * ((b : ℝ) - t) :=
      mul_nonneg (Nat.cast_nonneg n) (by linarith)
    linarith
  have hX : 1 ≤ min ((n : ℝ) * (t - (a : ℝ))) (1 + (n : ℝ) * ((b : ℝ) - t)) :=
    le_min h1 hB
  rw [tentFormula, min_eq_left hX]
  simp

/-- If `n * (t - b) ≥ 1` then the tent function vanishes (the right slope has died out). -/
lemma ttf_eq_zero_of_gt (a b : ℚ) (n : ℕ) (t : ℝ)
    (h : 1 ≤ (n : ℝ) * (t - (b : ℝ))) : tentFormula a b n t = 0 := by
  have hB : 1 + (n : ℝ) * ((b : ℝ) - t) ≤ 0 := by
    have : (n : ℝ) * ((b : ℝ) - t) = -((n : ℝ) * (t - (b : ℝ))) := by ring
    rw [this]; linarith
  have h1 : min ((n : ℝ) * (t - (a : ℝ))) (1 + (n : ℝ) * ((b : ℝ) - t)) ≤ 0 :=
    le_trans (min_le_right _ _) hB
  have h2 : min 1 (min ((n : ℝ) * (t - (a : ℝ))) (1 + (n : ℝ) * ((b : ℝ) - t))) ≤ 0 :=
    le_trans (min_le_right _ _) h1
  rw [tentFormula]
  exact max_eq_left h2

/-! ## The limit -/

theorem tendsto_tent_formula (a b : ℚ) (hab : a < b) (t : ℝ) :
    Filter.Tendsto (fun n : ℕ => tentFormula a b n t) Filter.atTop
      (nhds ((Set.Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => (1 : ℝ)) t)) := by
  have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  by_cases hmem : t ∈ Set.Ioc (a : ℝ) (b : ℝ)
  · -- inside `Ioc a b`: the value is eventually `1`
    obtain ⟨hat, htb⟩ := Set.mem_Ioc.mp hmem
    rw [Set.indicator_of_mem hmem]
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / (t - (a : ℝ)))
    have hNN : ∀ n ≥ N, tentFormula a b n t = 1 := by
      intro n hn
      refine ttf_eq_one_of a b n t ?_ htb
      have hpos : 0 < t - (a : ℝ) := by linarith
      have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h1 : 1 / (t - (a : ℝ)) ≤ (n : ℝ) := le_trans hN hn'
      rwa [div_le_iff₀ hpos] at h1
    refine (tendsto_const_nhds (x := (1 : ℝ))).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact (hNN n hn).symm
  · -- outside `Ioc a b`: the value is eventually `0`
    rw [Set.indicator_of_notMem hmem]
    rcases le_or_gt t (a : ℝ) with h | h
    · rw [show (fun n : ℕ => tentFormula a b n t) = fun _ => (0 : ℝ) from
        funext fun n => ttf_eq_zero_of_le a b n t h]
      exact tendsto_const_nhds
    · have hbt : (b : ℝ) < t := by
        rcases le_or_gt t (b : ℝ) with h2 | h2
        · exact absurd (Set.mem_Ioc.mpr ⟨h, h2⟩) hmem
        · exact h2
      obtain ⟨N, hN⟩ := exists_nat_ge (1 / (t - (b : ℝ)))
      have hNN : ∀ n ≥ N, tentFormula a b n t = 0 := by
        intro n hn
        refine ttf_eq_zero_of_gt a b n t ?_
        have hpos : 0 < t - (b : ℝ) := by linarith
        have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have h1 : 1 / (t - (b : ℝ)) ≤ (n : ℝ) := le_trans hN hn'
        rwa [div_le_iff₀ hpos] at h1
      refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      exact (hNN n hn).symm

end Work.EKLC7
