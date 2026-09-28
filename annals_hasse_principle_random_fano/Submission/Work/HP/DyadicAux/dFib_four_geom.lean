import Mathlib
import Submission.Work.HP.DyadicR2Defs

/-!
# The fibre sum of powers of four over `dFib`

`dFib s X Y` is the set of `a ≤ s - a` with `2 ^ a ≤ 2 * X` and `2 ^ (s - a) ≤ 2 * Y`.

The constraint `a ≤ s - a` alone forces `2 * a ≤ s`, hence `a ≤ s / 2`, so every term
`4 ^ a = 2 ^ (2 * a)` is bounded by `2 ^ s` and the whole fibre is contained in the
initial segment `{0, …, s / 2}`.  Summing the geometric series of ratio `4` over that
initial segment gives at most `(4 / 3) * 4 ^ (s / 2) ≤ (4 / 3) * 2 ^ s`.

The two elementary inputs are the geometric bound `∑_{a ≤ m} 4 ^ a ≤ (4 / 3) * 4 ^ m`
and the fact that `4 ^ (s / 2) ≤ 2 ^ s`.
-/

namespace Work.HP.DyadicAux

/-- Geometric bound with ratio `4`: the partial sum `∑_{a = 0}^{m} 4 ^ a` is at most
`(4 / 3) * 4 ^ m`, since three times a partial sum of ratio `4` is at most the next term. -/
lemma sum_range_four_le (m : ℕ) :
    ∑ a ∈ Finset.range (m + 1), (4 : ℝ) ^ a ≤ (4 / 3) * (4 : ℝ) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h4 : (4 : ℝ) ^ (m + 1) = 4 * (4 : ℝ) ^ m := by rw [pow_succ]; ring
    have hrhs : (4 / 3) * (4 : ℝ) ^ (m + 1) = (4 / 3) * (4 : ℝ) ^ m + (4 : ℝ) ^ (m + 1) := by
      rw [h4]; ring
    rw [hrhs]
    linarith

/-- The fibre `dFib s X Y` is contained in the initial segment `{0, …, s / 2}`: the
condition `a ≤ s - a` is equivalent to `2 * a ≤ s`. -/
lemma dFib_subset_range_half (s : ℕ) (X Y : ℝ) :
    dFib s X Y ⊆ Finset.range (s / 2 + 1) := by
  intro a ha
  simp only [dFib, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨hs, hle, -⟩ := ha
  have h2a : 2 * a ≤ s := by omega
  have hdiv : a ≤ s / 2 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by omega)
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hdiv)

theorem dFib_four_geom (s : ℕ) (X Y : ℝ) :
    ∑ a ∈ dFib s X Y, (4 : ℝ) ^ a ≤ (4 / 3) * (2 : ℝ) ^ s := by
  have h1 : ∑ a ∈ dFib s X Y, (4 : ℝ) ^ a ≤ ∑ a ∈ Finset.range (s / 2 + 1), (4 : ℝ) ^ a :=
    Finset.sum_le_sum_of_subset_of_nonneg (dFib_subset_range_half s X Y)
      (fun a _ _ => by positivity)
  have h2 : ∑ a ∈ Finset.range (s / 2 + 1), (4 : ℝ) ^ a ≤ (4 / 3) * (4 : ℝ) ^ (s / 2) :=
    sum_range_four_le (s / 2)
  have h3 : (4 : ℝ) ^ (s / 2) ≤ (2 : ℝ) ^ s := by
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h3' : (4 / 3) * (4 : ℝ) ^ (s / 2) ≤ (4 / 3) * (2 : ℝ) ^ s :=
    mul_le_mul_of_nonneg_left h3 (by norm_num)
  linarith

end Work.HP.DyadicAux
