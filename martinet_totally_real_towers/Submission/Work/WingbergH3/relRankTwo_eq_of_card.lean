import Mathlib
import Submission.Work.WingbergH3.Defs

namespace Work.WingbergH3

/-- **The relation rank is the base-`2` logarithm of `#H²(Γ,𝔽₂)`.**  `relRankTwo Γ` is *defined*
as `Nat.log 2 (Nat.card (contH2 Γ))`, so whenever the cardinality of the continuous cohomology
`H²(Γ,𝔽₂)` is exhibited as a power of two, the relation rank is the exponent. -/
theorem relRankTwo_eq_of_card {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {k : ℕ} (h : Nat.card (Work.RelatorRank.contH2 Γ) = 2 ^ k) :
    Work.WingbergH3.relRankTwo Γ = k := by
  rw [relRankTwo, h, Nat.log_pow (by norm_num : 1 < 2)]

end Work.WingbergH3
