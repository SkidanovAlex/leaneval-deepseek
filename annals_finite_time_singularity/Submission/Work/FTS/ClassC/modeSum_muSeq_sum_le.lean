import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

/-- The explicit form of the mode weight: `λ_m = 2m(2m+5) = 4m² + 10m`. -/
private lemma lamR_eq (m : ℕ) :
    Work.FTS.PhiStar.Radial.lamR m = 4 * (m : ℝ) ^ 2 + 10 * (m : ℝ) := by
  simp only [Work.FTS.PhiStar.Radial.lamR]
  ring

/-- The correction `3α² + 3α(5+α)/2` is at most `69/32` for `0 < α ≤ 1/4`
(the value at `α = 1/4`, where the quadratic `(9/2)α² + (15/2)α` is increasing). -/
private lemma correction_le (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    3 * α ^ 2 + 3 * α * (5 + α) / 2 ≤ 69 / 32 := by
  have hα_nn : 0 ≤ α := le_of_lt hα
  have hkey : α ^ 2 ≤ α / 4 := by
    nlinarith [mul_nonneg hα_nn (sub_nonneg.mpr hα4)]
  nlinarith [hkey, hα4, hα_nn]

/-- The harmonic tail `∑_{m ≤ N} (if m = 0 then 1 else 1/(4m²)) ≤ 2`.  The `m = 0` term is `1`
and the rest is dominated by `∑_{m ≥ 1} (1/m - 1/(m+1)) ≤ 1`. -/
private lemma harm_tail_le (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), (if m = 0 then (1 : ℝ) else 1 / (4 * (m : ℝ) ^ 2))) ≤ 2 := by
  have key : ∀ n : ℕ,
      (∑ m ∈ Finset.range (n + 1), (if m = 0 then (1 : ℝ) else 1 / (4 * (m : ℝ) ^ 2)))
        ≤ 2 - 1 / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hf : (if k + 1 = 0 then (1 : ℝ) else 1 / (4 * ((k + 1 : ℕ) : ℝ) ^ 2))
          = 1 / (4 * ((k : ℝ) + 1) ^ 2) := by
        simp
      rw [hf]
      have hstep : (1 : ℝ) / (4 * ((k : ℝ) + 1) ^ 2) ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) := by
        have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        have h : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) = 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
          rw [div_sub_div _ _ (ne_of_gt hk) (ne_of_gt hk2)]
          ring
        rw [h, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hcast : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      linarith
  have h := key N
  have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  linarith

/-- Per-mode bound: for `m ≥ 1` the denominator `λ_m - 3α² - 3α(5+α)/2` is at least `4m²`, while
the numerator `m+1` is at most `2m`; hence the squared quotient is at most `1/(4m²)`.  For `m = 0`
the quotient is `1`.  (`0 < α ≤ 1/4` makes the denominator bigger than `4m²` since
`3α² + 3α(5+α)/2 ≤ 69/32 < 10m` for `m ≥ 1`.) -/
private lemma mode_term_le (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) :
    (((m : ℝ) + 1) / (if m = 0 then 1 else
        Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2)) ^ 2
      ≤ (if m = 0 then (1 : ℝ) else 1 / (4 * (m : ℝ) ^ 2)) := by
  by_cases hm : m = 0
  · subst hm; norm_num
  · rw [ite_eq_right hm, ite_eq_right hm]
    have hcorr := correction_le α hα hα4
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      exact_mod_cast this
    have hmpos : 0 < (m : ℝ) := by linarith
    have hlam := lamR_eq m
    have hden_ge : 4 * (m : ℝ) ^ 2 ≤
        Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2 := by
      rw [hlam]; nlinarith [hcorr, hm1]
    have hden_pos : 0 <
        Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2 := by
      have : (0 : ℝ) < 4 * (m : ℝ) ^ 2 := by positivity
      linarith
    have hnum : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
    have hstep : ((m : ℝ) + 1) /
        (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2)
          ≤ 1 / (2 * (m : ℝ)) := by
      rw [div_le_div_iff₀ hden_pos (by positivity)]
      nlinarith [hden_ge, hnum, hmpos]
    have h1 : 0 ≤ ((m : ℝ) + 1) /
        (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2) := by
      positivity
    calc (((m : ℝ) + 1) /
            (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2)) ^ 2
        ≤ (1 / (2 * (m : ℝ))) ^ 2 := pow_le_pow_left₀ h1 hstep 2
      _ = 1 / (4 * (m : ℝ) ^ 2) := by field_simp; ring

theorem modeSum_muSeq_sum_le (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1),
        (((m : ℝ) + 1) / (if m = 0 then 1 else
          Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2)) ^ 2) ≤ 8 := by
  calc (∑ m ∈ Finset.range (N + 1),
        (((m : ℝ) + 1) / (if m = 0 then 1 else
          Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2)) ^ 2)
      ≤ ∑ m ∈ Finset.range (N + 1), (if m = 0 then (1 : ℝ) else 1 / (4 * (m : ℝ) ^ 2)) :=
        Finset.sum_le_sum (fun m _ => mode_term_le α hα hα4 m)
    _ ≤ 2 := harm_tail_le N
    _ ≤ 8 := by norm_num

end Work.FTS.ClassC
