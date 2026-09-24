import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_intervalIntegrable

/-!
# Antitonicity of the delay family `profC`

`profC j` is non-increasing on `[1,∞)`: each recursion step is either `(1/s)·∫_{max(s,3)}^{j+2}`
or `(1/s)·∫_s^{j+2}`, so the value at the larger argument involves a *shorter* integral of a
nonnegative function and a *smaller* prefactor `1/s`.  Consequently
`q ↦ profC j (max (log D / log q − 1) c)` is monotone on the primes `q ≥ 3`, which is the
monotonicity hypothesis consumed by `Commons.NumberTheory.Chen.Vsieve_abel_integral` in the
transport step of the sharp linear sieve.
-/

namespace Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

open MeasureTheory

/-- Integrability of the shifted profile `x ↦ profC n (x - 1)`. -/
private lemma intervalIntegrable_shift (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => profC n (x - 1)) volume a b := by
  have h := (profC_intervalIntegrable n (a - 1) (b - 1)).comp_sub_right 1
  rwa [show a - 1 + 1 = a by ring, show b - 1 + 1 = b by ring] at h

/-- The integral over the larger lower limit is at most the one over the smaller. -/
private lemma integral_mono_lower (n : ℕ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ x in b..c, profC n (x - 1)) ≤ ∫ x in a..c, profC n (x - 1) :=
  intervalIntegral.integral_mono_interval hab hbc le_rfl
    (Filter.Eventually.of_forall (fun _ => profC_nonneg n _)) (intervalIntegrable_shift n a c)

private lemma inn_nonneg (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    (0:ℝ) ≤ ∫ x in a..b, profC n (x - 1) :=
  intervalIntegral.integral_nonneg_of_forall hab (fun u => profC_nonneg n (u - 1))

theorem profC_antitone_aux : ∀ j : ℕ, ∀ {s t : ℝ}, 1 ≤ s → (j % 2 = 0 ∨ 2 ≤ s) → s ≤ t →
    profC j t ≤ profC j s := by
  intro j
  induction j with
  | zero =>
    intro s t hs h2 hst
    rw [profC_zero, profC_zero]
    by_cases ht : 1 ≤ t ∧ t ≤ 3
    · rw [if_pos ht]
      by_cases hs3 : 1 ≤ s ∧ s ≤ 3
      · rw [if_pos hs3]
        have hs0 : 0 < s := by linarith [hs3.1]
        have ht0 : 0 < t := by linarith [ht.1]
        rw [div_le_div_iff₀ ht0 hs0]
        nlinarith [ht.2, hst, hs3.1]
      · exfalso
        rcases not_and_or.mp hs3 with h | h
        · linarith
        · linarith [hst, ht.2]
    · rw [if_neg ht]
      exact le_of_eq_of_le rfl (profC_nonneg 0 s)
  | succ n ih =>
    intro s t hs h2 hst
    by_cases hpar : (n + 1) % 2 = 0
    · by_cases ht : 1 ≤ t ∧ t < (n:ℝ) + 4
      · have hL : profC (n + 1) t
            = (∫ x in max t 3..((n:ℝ) + 4), profC n (x - 1)) / t := by
          rw [profC_succ]; rw [if_pos hpar, if_pos ht]
        rw [hL]
        by_cases hs' : 1 ≤ s ∧ s < (n:ℝ) + 4
        · have hR : profC (n + 1) s
              = (∫ x in max s 3..((n:ℝ) + 4), profC n (x - 1)) / s := by
            rw [profC_succ]; rw [if_pos hpar, if_pos hs']
          rw [hR]
          have hs0 : 0 < s := by linarith [hs'.1]
          have ht0 : 0 < t := by linarith [ht.1]
          have hms : max s 3 ≤ max t 3 := max_le_max hst le_rfl
          have hmt : max t 3 ≤ (n:ℝ) + 4 :=
            max_le (le_of_lt ht.2) (by push_cast; linarith [ht.1])
          have hle := integral_mono_lower n hms hmt
          have hIs := inn_nonneg n (le_trans hms hmt)
          have h3 : (∫ x in max t 3..((n:ℝ) + 4), profC n (x - 1)) / t
              ≤ (∫ x in max s 3..((n:ℝ) + 4), profC n (x - 1)) / t :=
            div_le_div_of_nonneg_right hle ht0.le
          have h4 : (∫ x in max s 3..((n:ℝ) + 4), profC n (x - 1)) / t
              ≤ (∫ x in max s 3..((n:ℝ) + 4), profC n (x - 1)) / s :=
            div_le_div_of_nonneg_left hIs hs0 hst
          linarith [h3, h4]
        · exfalso
          rcases not_and_or.mp hs' with h | h
          · linarith
          · linarith [h, hst, ht.2]
      · have hL : profC (n + 1) t = 0 := by
          rw [profC_succ]; rw [if_pos hpar, if_neg ht]
        rw [hL]
        exact profC_nonneg (n + 1) s
    · have h2s : 2 ≤ s := by
        rcases h2 with h | h
        · exact absurd (by simpa using h : (n + 1) % 2 = 0) hpar
        · exact h
      by_cases ht : 2 ≤ t ∧ t < (n:ℝ) + 4
      · have hL : profC (n + 1) t = (∫ x in t..((n:ℝ) + 4), profC n (x - 1)) / t := by
          rw [profC_succ]; rw [if_neg hpar, if_pos ht]
        rw [hL]
        by_cases hs' : 2 ≤ s ∧ s < (n:ℝ) + 4
        · have hR : profC (n + 1) s = (∫ x in s..((n:ℝ) + 4), profC n (x - 1)) / s := by
            rw [profC_succ]; rw [if_neg hpar, if_pos hs']
          rw [hR]
          have hs0 : 0 < s := by linarith [hs'.1]
          have ht0 : 0 < t := by linarith [ht.1]
          have hle := integral_mono_lower n hst (le_of_lt ht.2)
          have hIs := inn_nonneg n (le_trans hst (le_of_lt ht.2))
          have h3 : (∫ x in t..((n:ℝ) + 4), profC n (x - 1)) / t
              ≤ (∫ x in s..((n:ℝ) + 4), profC n (x - 1)) / t :=
            div_le_div_of_nonneg_right hle ht0.le
          have h4 : (∫ x in s..((n:ℝ) + 4), profC n (x - 1)) / t
              ≤ (∫ x in s..((n:ℝ) + 4), profC n (x - 1)) / s :=
            div_le_div_of_nonneg_left hIs hs0 hst
          linarith [h3, h4]
        · exfalso
          rcases not_and_or.mp hs' with h | h
          · exact absurd h2s h
          · linarith [h, hst, ht.2]
      · have hL : profC (n + 1) t = 0 := by
          rw [profC_succ]; rw [if_neg hpar, if_neg ht]
        rw [hL]
        exact profC_nonneg (n + 1) s

/-- `profC j` is non-increasing on `[2,∞)` (all `j`). -/
theorem profC_antitone (j : ℕ) : AntitoneOn (profC j) (Set.Ici (2:ℝ)) :=
  fun s hs t _ hst =>
    profC_antitone_aux j (le_trans (by norm_num : (1:ℝ) ≤ 2) hs) (Or.inr hs) hst

/-- `profC j` is non-increasing on `[1,∞)` for even `j`. -/
theorem profC_antitone_even (j : ℕ) (hj : j % 2 = 0) : AntitoneOn (profC j) (Set.Ici (1:ℝ)) :=
  fun _s hs _t _ hst => profC_antitone_aux j hs (Or.inl hj) hst

end

end Work.NumberTheory.Chen.APSwitchUpper
