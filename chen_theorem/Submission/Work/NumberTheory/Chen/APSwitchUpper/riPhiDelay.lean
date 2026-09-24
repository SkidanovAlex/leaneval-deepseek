/-
# `APSwitchUpper.riPhiDelay` — the delay calculus of the `profC` family

Vocabulary for the summed (delay) identities of the Rosser–Iwaniec profile family
`profC j = f_{j+1}` (see `APSwitchUpper/prof.lean`).  With

* `evenSum j = A_j := Σ_{i≤j} profC (2i)`   (the partial sums of `riPhi`),
* `oddSum  j = B_j := Σ_{i≤j} profC (2i+1)` (the partial sums of `riPsi`),
* `profTail m x = ∫_x^{m+4} profC m`        (the tail of the `m`-th profile),

the pointwise recursions of `profC` sum to

* `s·A_j(s) = (3−s)·1_{[1,3]}(s) + ∫_{max(s−1,2)}^∞ B_{j−1}(u) du`,
* `s·B_j(s) = ∫_{s−1}^∞ A_j(u) du`  (`s ≥ 2`),
* `A_{j+1}(s) = (1/s)·∫_{s−2}^∞ A_j(w)·log((w+1)/(s−1)) dw`  (`s ≥ 3`),

and these are the identities from which the majorant `riPhiEnv` is derived.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The tail integral of the `m`-th delay profile: `profTail m x = ∫_x^{m+4} profC m`.
(The upper limit `m+4` is beyond the support edge `m+3`, so this is `∫_x^∞ profC m`.) -/
noncomputable def profTail (m : ℕ) (x : ℝ) : ℝ := ∫ u in x..((m : ℝ) + 3), profC m u

/-- The `j`-th even partial sum `A_j = Σ_{i≤j} profC (2i)`. -/
noncomputable def evenSum (j : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), profC (2 * i) s

/-- The `j`-th odd partial sum `B_j = Σ_{i≤j} profC (2i+1)`. -/
noncomputable def oddSum (j : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), profC (2 * i + 1) s

/-- The odd partial sum with `j` terms (i.e. `B'_j = B_{j-1}`): the tail sum of the
even-index tails. -/
noncomputable def oddSumShift (j : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range j, profC (2 * i + 1) s

theorem oddSumShift_eq_oddSum_pred (j : ℕ) (s : ℝ) :
    oddSumShift (j + 1) s = oddSum j s := by
  rfl

theorem evenSum_succ (j : ℕ) (s : ℝ) :
    evenSum (j + 1) s = evenSum j s + profC (2 * (j + 1)) s := by
  rw [evenSum, evenSum, Finset.sum_range_succ]

theorem oddSum_succ (j : ℕ) (s : ℝ) :
    oddSum (j + 1) s = oddSum j s + profC (2 * (j + 1) + 1) s := by
  rw [oddSum, oddSum, Finset.sum_range_succ]

/-! ## The pointwise recursions in tail form -/

/-- `profC m` integrates to zero on `[m+3, m+4]` (the support edge). -/
theorem integral_profC_support_edge (m : ℕ) :
    (∫ u in ((m : ℝ) + 3)..((m : ℝ) + 4), profC m u) = 0 := by
  have h : ∀ u ∈ Set.uIcc ((m : ℝ) + 3) ((m : ℝ) + 4), profC m u = 0 := by
    intro u hu
    rw [Set.mem_uIcc] at hu
    exact profC_support m u (by rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith)
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_zero]

/-- `profTail m x = 0` once `x` is beyond the support edge `m+3`. -/
theorem profTail_eq_zero {m : ℕ} {x : ℝ} (hx : (m : ℝ) + 3 ≤ x) : profTail m x = 0 := by
  rw [profTail]
  have h2 : ∀ u ∈ Set.uIcc x ((m : ℝ) + 3), profC m u = 0 := by
    intro u hu
    rw [Set.mem_uIcc] at hu
    exact profC_support m u (by rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith)
  rw [intervalIntegral.integral_congr h2, intervalIntegral.integral_zero]

/-- `profTail m` unfolded as an interval integral (definitional). -/
theorem profTail_eq_integral (m : ℕ) (x : ℝ) :
    profTail m x = ∫ u in x..((m : ℝ) + 3), profC m u := rfl

theorem two_mul_add_one_mod (i : ℕ) : (2 * i + 1 + 1) % 2 = 0 := by omega

theorem two_mul_mod_one (i : ℕ) : ¬ ((2 * i + 1) % 2 = 0) := by omega

/-- The even-index recursion: `s·profC (2(i+1))(s) = profTail (2i+1)(max (s−1) 2)` for `s ≥ 1`. -/
theorem profC_even_mul (i : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    s * profC (2 * (i + 1)) s = profTail (2 * i + 1) (max (s - 1) 2) := by
  by_cases hlt : s < ((2 * i + 1 : ℕ) : ℝ) + 4
  · have h1 : profC (2 * (i + 1)) s
        = (∫ t in max s 3..((2 * i + 1 : ℕ) : ℝ) + 4, profC (2 * i + 1) (t - 1)) / s := by
      rw [show (2 * (i + 1)) = (2 * i + 1) + 1 from by ring, profC_succ]
      rw [if_pos (two_mul_add_one_mod i), if_pos ⟨hs, hlt⟩]
    rw [h1, mul_comm s ((∫ t in max s 3..((2 * i + 1 : ℕ) : ℝ) + 4,
      profC (2 * i + 1) (t - 1)) / s), div_mul_cancel₀ _ (by linarith : s ≠ 0)]
    rw [profTail_eq_integral, intervalIntegral.integral_comp_sub_right (fun u => profC (2 * i + 1) u) 1]
    have hmax : max s 3 - 1 = max (s - 1) 2 := by
      rcases le_total s 3 with h | h
      · rw [max_eq_right h, max_eq_right (by linarith : s - 1 ≤ 2)]
        norm_num
      · rw [max_eq_left h, max_eq_left (by linarith : 2 ≤ s - 1)]
    rw [hmax, show ((2 * i + 1 : ℕ) : ℝ) + 4 - 1 = ((2 * i + 1 : ℕ) : ℝ) + 3 from by ring]
  · have h1 : profC (2 * (i + 1)) s = 0 := by
      rw [show (2 * (i + 1)) = (2 * i + 1) + 1 from by ring, profC_succ]
      rw [if_pos (two_mul_add_one_mod i), if_neg (fun hc => hlt hc.2)]
    rw [h1, mul_zero]
    refine (profTail_eq_zero ?_).symm
    have hs' : ((2 * i + 1 : ℕ) : ℝ) + 4 ≤ s := not_lt.mp hlt
    refine le_max_of_le_left ?_
    push_cast at hs' ⊢
    linarith

/-- The odd-index recursion: `s·profC (2i+1)(s) = profTail (2i)(s−1)` for `s ≥ 2`. -/
theorem profC_odd_mul (i : ℕ) (s : ℝ) (hs : 2 ≤ s) :
    s * profC (2 * i + 1) s = profTail (2 * i) (s - 1) := by
  by_cases hlt : s < ((2 * i : ℕ) : ℝ) + 4
  · have h1 : profC (2 * i + 1) s
        = (∫ t in s..((2 * i : ℕ) : ℝ) + 4, profC (2 * i) (t - 1)) / s := by
      rw [profC_succ]
      rw [if_neg (two_mul_mod_one i), if_pos ⟨hs, hlt⟩]
    rw [h1, mul_comm s ((∫ t in s..((2 * i : ℕ) : ℝ) + 4, profC (2 * i) (t - 1)) / s),
      div_mul_cancel₀ _ (by linarith : s ≠ 0)]
    rw [profTail_eq_integral, intervalIntegral.integral_comp_sub_right (fun u => profC (2 * i) u) 1,
      show ((2 * i : ℕ) : ℝ) + 4 - 1 = ((2 * i : ℕ) : ℝ) + 3 from by ring]
  · have h1 : profC (2 * i + 1) s = 0 := by
      rw [profC_succ]
      rw [if_neg (two_mul_mod_one i), if_neg (fun hc => hlt hc.2)]
    rw [h1, mul_zero]
    refine (profTail_eq_zero ?_).symm
    have hs' : ((2 * i : ℕ) : ℝ) + 4 ≤ s := not_lt.mp hlt
    push_cast at hs' ⊢
    linarith

theorem evenSum_nonneg (j : ℕ) (s : ℝ) : 0 ≤ evenSum j s :=
  Finset.sum_nonneg (fun i _ => profC_nonneg (2 * i) s)

theorem oddSum_nonneg (j : ℕ) (s : ℝ) : 0 ≤ oddSum j s :=
  Finset.sum_nonneg (fun i _ => profC_nonneg (2 * i + 1) s)

theorem evenSum_mono {j j' : ℕ} (h : j ≤ j') (s : ℝ) : evenSum j s ≤ evenSum j' s := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => profC_nonneg (2 * i) s)
  intro i hi
  rw [Finset.mem_range] at hi ⊢
  omega

theorem oddSum_mono {j j' : ℕ} (h : j ≤ j') (s : ℝ) : oddSum j s ≤ oddSum j' s := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => profC_nonneg (2 * i + 1) s)
  intro i hi
  rw [Finset.mem_range] at hi ⊢
  omega

end

end Work.NumberTheory.Chen.APSwitchUpper
