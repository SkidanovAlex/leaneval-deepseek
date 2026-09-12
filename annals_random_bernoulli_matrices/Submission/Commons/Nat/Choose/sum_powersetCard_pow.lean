import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

namespace Commons.Nat.Choose

open Finset
open scoped BigOperators

/-- Double-counting identity: grouping subsets of `Fin m` by their cardinality,
`∑_{ℓ ≤ r} ∑_{B ∈ powersetCard ℓ univ} α^(m−B.card) = ∑_{ℓ ≤ r} C(m,ℓ)·α^(m−ℓ)`
for real `α`.  (Here `powersetCard ℓ univ` is the finset of all `ℓ`-element subsets of `Fin m`,
of cardinality `m.choose ℓ`.) -/
theorem sum_powersetCard_pow {m r : ℕ} (α : ℝ) :
    (∑ ℓ ∈ Finset.range (r + 1),
      ∑ B ∈ (Finset.univ : Finset (Fin m)).powersetCard ℓ, α ^ (m - B.card)) =
      ∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ) * α ^ (m - ℓ) := by
  calc
    (∑ ℓ ∈ Finset.range (r + 1),
        ∑ B ∈ (Finset.univ : Finset (Fin m)).powersetCard ℓ, α ^ (m - B.card))
        = ∑ ℓ ∈ Finset.range (r + 1),
            ∑ B ∈ (Finset.univ : Finset (Fin m)).powersetCard ℓ, α ^ (m - ℓ) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            apply Finset.sum_congr rfl
            intro B hB
            rw [Finset.mem_powersetCard_univ.mp hB]
    _ = ∑ ℓ ∈ Finset.range (r + 1),
            (((Finset.univ : Finset (Fin m)).powersetCard ℓ).card : ℝ) * α ^ (m - ℓ) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ) * α ^ (m - ℓ) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end Commons.Nat.Choose