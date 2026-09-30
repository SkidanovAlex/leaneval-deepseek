import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.split_aux
import Submission.Work.BW.split_E0
import Submission.Work.BW.split_E23
import Submission.Work.BW.split_E1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace Work.BW

/-- The half split is antitone and fits the budgets. -/
theorem split_anti {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d : ℝ) ≤ σ j) :
    (∀ m, m < r → halfSplit r (calS r d h) (m + 1) ≤ halfSplit r (calS r d h) m) ∧
    (∀ m, m < r → halfSplit r (calT r d σ) (m + 1) ≤ halfSplit r (calT r d σ) m) ∧
    ((∑ m ∈ Finset.range (r + 1), halfSplit r (calS r d h) m : ℕ) : ℝ) ≤ calS r d h ∧
    ((∑ m ∈ Finset.range (r + 1), halfSplit r (calT r d σ) m : ℕ) : ℝ) ≤ calT r d σ :=
  ⟨fun m _ => halfSplit_anti (calS_nonneg r d h) m,
   fun m _ => halfSplit_anti (calT_nonneg r d σ) m,
   halfSplit_sum_le (calS_nonneg r d h),
   halfSplit_sum_le (calT_nonneg r d σ)⟩

/-- BW §21 numerics, part 1 (replaces BW's equal split `𝒮ᵢ = 𝒮/(r+1)`, which violates (5) at
`m = 0` for `r ≥ 7198`). With the half split of `𝒮 = 2ξ^{-rI}S` and `𝒯 = ξ^{rI+1}T` and
`𝒟₀ = h(D₀+1)`, `𝒟ⱼ = 2^{-I}Dⱼ`: the sequences are antitone, fit the budgets, and satisfy the
exclusion conditions (E0)–(E3) of `multiplicity_prop`. Tightest: (E1) at `m = 0`, `e = e₀`,
margin about `e^{4.8}` at `r = 2, d = 1`. -/
theorem split_conditions {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    (∀ m, m < r → halfSplit r (calS r d h) (m + 1) ≤ halfSplit r (calS r d h) m) ∧
    (∀ m, m < r → halfSplit r (calT r d σ) (m + 1) ≤ halfSplit r (calT r d σ) m) ∧
    ((∑ m ∈ Finset.range (r + 1), halfSplit r (calS r d h) m : ℕ) : ℝ) ≤ calS r d h ∧
    ((∑ m ∈ Finset.range (r + 1), halfSplit r (calT r d σ) m : ℕ) : ℝ) ≤ calT r d σ ∧
    (∀ j : Fin r, ((r : ℝ) + 1) * calD r d h σ j.succ < (halfSplit r (calT r d σ) 0 : ℝ) + 1) ∧
    (∀ m, m < r → ∀ e : Fin (r + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, calD r d h σ i ^ e i <
        ((halfSplit r (calS r d h) m : ℝ) + 1) *
          ((halfSplit r (calT r d σ) m + m + 1).choose (m + 1) : ℝ)) ∧
    ((r + 1).factorial : ℝ) * ∏ i, calD r d h σ i <
      ((halfSplit r (calS r d h) r : ℝ) + 1) *
        ((halfSplit r (calT r d σ) r + r).choose r : ℝ) ∧
    ((r + 1).factorial : ℝ) * ∏ i : Fin r, calD r d h σ i.succ <
      ((halfSplit r (calS r d h) (r - 1) : ℝ) + 1) *
        ((halfSplit r (calT r d σ) (r - 1) + (r - 1)).choose (r - 1) : ℝ) := by
  obtain ⟨e1, e2, e3, e4⟩ := split_anti hr hd hh σ hσ
  obtain ⟨e7, e8⟩ := split_E23 hr hd hh σ hσ
  exact ⟨e1, e2, e3, e4, split_E0 hr hd hh σ hσ, split_E1 hr hd hh σ hσ, e7, e8⟩

end Work.BW
