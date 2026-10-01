import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.menuW_sums_le

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

/-! ### Nonnegativity of the menu weights -/

/-- Every menu weight is nonnegative.  This holds with no hypothesis on `p` and `e`: each of the
eight branches of the definition of `menuW` is either `0` or a product of positive constants with
a real power of the nonnegative base `p`. -/
lemma menuW_nonneg (p e s j : ℕ) : 0 ≤ menuW p e s j := by
  rw [menuW]
  split_ifs <;> positivity

/-- The two `menuW` sums of `menuW_univ` are nonnegative, term by term. -/
lemma menuW_univ_nonneg {p e : ℕ} (hp : p.Prime) :
    0 ≤ (∑ s ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1),
        menuW p e s j / (p : ℝ) ^ (s + j)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  refine Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun j _ => ?_
  exact div_nonneg (menuW_nonneg p e s j) (le_of_lt (pow_pos hp0 _))

theorem menuW_univ {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) :
    (0 ≤ (∑ s ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1),
        menuW p e s j / (p : ℝ) ^ (s + j)))
    ∧ (∑ s ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1),
        menuW p e s j / (p : ℝ) ^ (s + j)) ≤ 10 ^ 8 * ((e : ℝ) + 1) ^ 2
    ∧ (∑ s ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1),
        menuW p e s j / (p : ℝ) ^ j) ≤ 10 ^ 8 * ((e : ℝ) + 1) ^ 2 * (p : ℝ) ^ ((e : ℝ) / 6)
    ∧ (∀ s j : ℕ, 0 ≤ menuW p e s j) := by
  refine ⟨menuW_univ_nonneg hp, (menuW_sums_le hp he).1, (menuW_sums_le hp he).2,
    menuW_nonneg p e⟩

end Work.LinnikBurgess
