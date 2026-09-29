import Mathlib
import Submission.Work.CPull.sympSym_radius

/-!
# Area C17I — the sharp binomial coefficient bound for `Sym⁺`

The crude estimate `Submission.Work.CPull.sympSym_coeff_bound` gives
`|coeffₙ (Sym⁺P)| ≤ 3C·(8(1+R)²)ⁿ`, which is far too lossy for the §6
holonomy argument.  Here we derive the *sharp* bound from the two
hypotheses the caller controls:

* `hdeg` : `P_m` has degree `< m`, i.e. `coeff n (P_m) = 0` for `n > m`
  (the `y`-valuation `⌈m/2⌉` plus the explicit recurrence), so that the
  defining sum `Sym⁺P = Σ_m coeff_m(P)·P_m(y)` truncates to `m ≥ n`;
* `hch`  : `|coeffₙ (P_{n+j})| ≤ 2·C(n,j)`.

Then, writing `m = n+j` and using `Σ_j C(n,j)ρ^j = (1+ρ)ⁿ`,

`|coeffₙ (Sym⁺P)| ≤ Σ_{j≤n} C₀ρ^{n+j}·2C(n,j) = 2C₀(ρ(1+ρ))ⁿ`.
-/

open scoped BigOperators

namespace Work.C17I

open PowerSeries

/-- The defining sum for `Sym⁺P` truncates to the terms `m ≥ n`; with `m = n+j`
this is the exact finite coefficient formula used for the sharp estimate. -/
lemma sympSym_coeff_eq_sum_of
    (hdeg : ∀ m n : ℕ, m < n → PowerSeries.coeff n (Work.CPull.sympQ m) = 0)
    (P : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (Submission.CDT.sympSym P)
      = ∑ j ∈ Finset.range (n + 1),
          PowerSeries.coeff (n + j) P * PowerSeries.coeff n (Work.CPull.sympQ (n + j)) := by
  rw [Work.CPull.sympSym_eq_sympRep, Work.CPull.sympRep, PowerSeries.coeff_mk]
  have hsubset : Finset.Ico n (2 * n + 1) ⊆ Finset.range (2 * n + 1) := by
    intro x hx; simp only [Finset.mem_Ico] at hx; simp only [Finset.mem_range]; omega
  have hzero : ∀ x ∈ Finset.range (2 * n + 1), x ∉ Finset.Ico n (2 * n + 1) →
      PowerSeries.coeff x P * PowerSeries.coeff n (Work.CPull.sympQ x) = 0 := by
    intro x hx hxn
    simp only [Finset.mem_range] at hx
    simp only [Finset.mem_Ico, not_and] at hxn
    have hxn' : x < n := by
      by_contra h; push Not at h; exact hxn h (by omega)
    rw [hdeg x n hxn', mul_zero]
  rw [← Finset.sum_subset hsubset hzero]
  rw [Finset.sum_Ico_eq_sum_range]
  rw [show 2 * n + 1 - n = n + 1 from by omega]

theorem sympSym_coeff_bound_of
    (hdeg : ∀ m n : ℕ, m < n → PowerSeries.coeff n (Work.CPull.sympQ m) = 0)
    (hch : ∀ n j : ℕ, |(((PowerSeries.coeff n (Work.CPull.sympQ (n + j)) : ℚ)) : ℝ)|
        ≤ 2 * (Nat.choose n j : ℝ))
    {P : PowerSeries ℚ} {C₀ ρ₀ : ℝ} (hC₀ : 0 < C₀) (hρ₀ : 0 < ρ₀)
    (hP : ∀ m : ℕ, |(((PowerSeries.coeff m P : ℚ)) : ℝ)| ≤ C₀ * ρ₀ ^ m) (n : ℕ) :
    |(((PowerSeries.coeff n (Submission.CDT.sympSym P) : ℚ)) : ℝ)|
      ≤ 2 * C₀ * (ρ₀ * (1 + ρ₀)) ^ n := by
  have hcoe := sympSym_coeff_eq_sum_of hdeg P n
  have hcast : (((∑ j ∈ Finset.range (n + 1),
        PowerSeries.coeff (n + j) P * PowerSeries.coeff n (Work.CPull.sympQ (n + j)) : ℚ)) : ℝ)
      = ∑ j ∈ Finset.range (n + 1),
          ((PowerSeries.coeff (n + j) P : ℚ) : ℝ)
            * ((PowerSeries.coeff n (Work.CPull.sympQ (n + j)) : ℚ) : ℝ) := by
    push_cast
    ring
  have hbin : (1 + ρ₀) ^ n = ∑ j ∈ Finset.range (n + 1), ρ₀ ^ j * (n.choose j : ℝ) := by
    have h := add_pow ρ₀ 1 n
    simp only [one_pow, mul_one] at h
    rw [add_comm ρ₀ 1] at h
    exact h
  rw [hcoe, hcast]
  calc |∑ j ∈ Finset.range (n + 1),
          ((PowerSeries.coeff (n + j) P : ℚ) : ℝ)
            * ((PowerSeries.coeff n (Work.CPull.sympQ (n + j)) : ℚ) : ℝ)|
      ≤ ∑ j ∈ Finset.range (n + 1),
          |((PowerSeries.coeff (n + j) P : ℚ) : ℝ)|
            * |((PowerSeries.coeff n (Work.CPull.sympQ (n + j)) : ℚ) : ℝ)| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        exact Finset.sum_le_sum (fun j _ => le_of_eq (abs_mul _ _))
    _ ≤ ∑ j ∈ Finset.range (n + 1), (C₀ * ρ₀ ^ (n + j)) * (2 * (n.choose j : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul (hP (n + j)) (hch n j) (abs_nonneg _)
          (mul_nonneg (le_of_lt hC₀) (pow_nonneg (le_of_lt hρ₀) _))
    _ = ∑ j ∈ Finset.range (n + 1), 2 * C₀ * ρ₀ ^ n * (ρ₀ ^ j * (n.choose j : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_add]; ring
    _ = 2 * C₀ * ρ₀ ^ n * (∑ j ∈ Finset.range (n + 1), ρ₀ ^ j * (n.choose j : ℝ)) := by
        rw [Finset.mul_sum]
    _ = 2 * C₀ * ρ₀ ^ n * (1 + ρ₀) ^ n := by rw [hbin]
    _ = 2 * C₀ * (ρ₀ * (1 + ρ₀)) ^ n := by rw [mul_pow]; ring

end Work.C17I
