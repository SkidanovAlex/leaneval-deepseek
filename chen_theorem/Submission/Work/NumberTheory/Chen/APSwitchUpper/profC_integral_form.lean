import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_intervalIntegrable

/-!
# The delay recursion of `profC` in the `u`-variable

The transport step of the sharp upper-bound linear sieve identifies the integral that the Abel
staircase produces, `(1/s)∫ Φ(u) du` over the effective `u`-range, with the profile
`profC (k+1) s`.  The two forms of `profC_succ` (with the clamp at `3` for the even class and
without it for the odd class) become, under `u = t − 1`,

* `profC (k+1) s = (1/s)·∫_{max(s−1,2)}^{k+3} profC k u du`  (`k` odd, `s ≥ 1`);
* `profC (k+1) s = (1/s)·∫_{s−1}^{k+3} profC k u du`          (`k` even, `s ≥ 2`).

Because `profC k` is supported on `u < k+3` (`profC_support`), the upper limit `k+3` may be
replaced by anything larger; in particular the transport's `u`-range, which is contained in
`[max(s−1,2), k+3]`, produces the *same* integral — with equality for `s ≥ 3` and strict
containment (a genuine margin) for `8/5 ≤ s < 3`.
-/

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory

noncomputable section

/-- Shifted integrability of `profC k`. -/
private lemma int_shift (k : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => profC k (x - 1)) volume a b := by
  have h := (profC_intervalIntegrable k (a - 1) (b - 1)).comp_sub_right 1
  rwa [show a - 1 + 1 = a by ring, show b - 1 + 1 = b by ring] at h

/-- `max s 3 - 1 = max (s - 1) 2`. -/
private lemma max_sub_one (s : ℝ) : max s 3 - 1 = max (s - 1) 2 := by
  rcases le_total s 3 with h | h
  · rw [max_eq_right h, max_eq_right (by linarith : s - 1 ≤ (2:ℝ))]
    norm_num
  · rw [max_eq_left h, max_eq_left (by linarith : (2:ℝ) ≤ s - 1)]

/-- The even-class recursion in `u`-form: `profC (k+1) s = (1/s)∫_{max(s−1,2)}^{k+3} profC k`. -/
theorem profC_eq_integral_even (k : ℕ) (hk : k % 2 = 1) (s : ℝ) (hs : 1 ≤ s) :
    profC (k + 1) s = (∫ u in max (s - 1) 2..((k:ℝ) + 3), profC k u) / s := by
  rw [profC_succ]
  rw [if_pos (by omega : (k + 1) % 2 = 0)]
  by_cases h : 1 ≤ s ∧ s < (k:ℝ) + 4
  · rw [if_pos h]
    rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ => profC k u) 1]
    congr 2
    · rw [max_sub_one]
    · ring
  · rw [if_neg h]
    have hge : (k:ℝ) + 3 ≤ max (s - 1) 2 := by
      rcases not_and_or.mp h with h1 | h1
      · linarith
      · have h1' : (k:ℝ) + 4 ≤ s := not_lt.mp h1
        exact le_trans (by linarith : (k:ℝ) + 3 ≤ s - 1) (le_max_left _ _)
    have hzero : ∀ u ∈ Set.uIcc (max (s - 1) 2) ((k:ℝ) + 3), profC k u = 0 := by
      intro u hu
      rw [Set.mem_uIcc] at hu
      refine profC_support k u ?_
      rcases hu with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩
      · linarith
      · linarith
    rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero]
    ring

/-- The odd-class recursion in `u`-form: `profC (k+1) s = (1/s)∫_{s−1}^{k+3} profC k`. -/
theorem profC_eq_integral_odd (k : ℕ) (hk : k % 2 = 0) (s : ℝ) (hs : 2 ≤ s) :
    profC (k + 1) s = (∫ u in (s - 1)..((k:ℝ) + 3), profC k u) / s := by
  rw [profC_succ]
  rw [if_neg (by omega : ¬ ((k + 1) % 2 = 0))]
  by_cases h : 2 ≤ s ∧ s < (k:ℝ) + 4
  · rw [if_pos h]
    rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ => profC k u) 1]
    congr 2 <;> ring
  · rw [if_neg h]
    have hge : (k:ℝ) + 3 ≤ s - 1 := by
      rcases not_and_or.mp h with h1 | h1
      · linarith
      · have h1' : (k:ℝ) + 4 ≤ s := not_lt.mp h1
        linarith
    have hzero : ∀ u ∈ Set.uIcc (s - 1) ((k:ℝ) + 3), profC k u = 0 := by
      intro u hu
      rw [Set.mem_uIcc] at hu
      refine profC_support k u ?_
      rcases hu with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩
      · linarith
      · linarith
    rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero]
    ring

end

end Work.NumberTheory.Chen.APSwitchUpper
