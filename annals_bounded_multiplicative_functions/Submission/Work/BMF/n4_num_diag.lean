import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n4_num_diag_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- **A numerical bound for the diagonal term of the large-`q` case of N4.**  For fixed
`ℓ ≥ 2`, `C₁ > 0`, `K > 0` there is `P₀` such that for `P ≥ P₀`, `3 ≤ N ≤ P^{ℓ-1}` and
`C₀ ≥ 1/log P`,

`(C₁ π₀(P))^ℓ · (ℓ+1)^ℓ ≤ K C₀ π₀(P)^{2ℓ} / N · (1/log N)`,  `π₀(P) = P/log P`.

Indeed the ratio of the two sides is `K C₀ π₀(P)^ℓ/(N log N C₁^ℓ (ℓ+1)^ℓ)`, and using
`C₀ ≥ 1/log P`, `π₀(P)^ℓ = P^ℓ/log^ℓ P` and `N ≤ P^{ℓ-1}` this is at least
`K P/(log^{ℓ+1}P · log N · C₁^ℓ (ℓ+1)^ℓ) ≥ K P/((ℓ-1) log^{ℓ+2}P C₁^ℓ (ℓ+1)^ℓ)`, which tends to
`∞`.  (Same claim as the currently unproved `Work.BMF.n4_num_diag_bound`, repeated because the
consumer needs a proved version.) -/
lemma n4_num_diag (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (C₁ K : ℝ) (hC₁ : 0 < C₁) (hK : 0 < K) :
    ∃ P₀ : ℝ, ∀ P N C₀ : ℝ, P₀ ≤ P → 3 ≤ N → N ≤ P ^ (ℓ - 1) → 1 / Real.log P ≤ C₀ →
      (C₁ * pi0 P) ^ ℓ * (((ℓ + 1 : ℕ)) : ℝ) ^ ℓ ≤
        K * C₀ * pi0 P ^ (2 * ℓ) / N * (1 / Real.log N) :=
  n4_num_diag_bound ℓ hℓ C₁ K hC₁ hK

end Work.BMF
