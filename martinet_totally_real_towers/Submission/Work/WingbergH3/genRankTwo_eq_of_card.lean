import Mathlib
import Submission.Work.WingbergH3.Defs

namespace Work.WingbergH3

/-- **The generator rank is the base-`2` logarithm of `#H¹(Γ,𝔽₂)`.**  `genRankTwo Γ` is *defined*
as `Nat.log 2 (Nat.card (H1 Γ (ZMod 2)))`, so whenever the cardinality of `H¹(Γ,𝔽₂)` is exhibited
as a power of two, the generator rank is the exponent. -/
theorem genRankTwo_eq_of_card {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d : ℕ} (h : Nat.card (Work.ConCohomology.H1 Γ (ZMod 2)) = 2 ^ d) :
    Work.WingbergH3.genRankTwo Γ = d := by
  rw [genRankTwo, h, Nat.log_pow (by norm_num : 1 < 2)]

end Work.WingbergH3
