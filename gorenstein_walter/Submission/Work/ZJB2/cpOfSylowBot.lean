import Submission.Work.ZJB2.Defs

/-!
# GW design 17, item B (ZJB2) — leaf `cpOfSylowBot` (B.bot) — PROVED

`S = 1`: every `W ⊆ S` is `⊆ {1}`, so `g = g · 1` with `g ∈ C(W)`.
-/

namespace Work.ZJB

open Work.GW2 Subgroup

theorem cpOfSylowBot (p : ℕ) (G : Type) [Group G] [Finite G] : CpOfSylowBotProp p G := by
  intro S hS W _ hWS g _
  refine ⟨g, 1, ?_, Subgroup.one_mem _, (mul_one g).symm⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have : h ∈ (S : Subgroup G) := hWS hh
  rw [hS, Subgroup.mem_bot] at this
  simp [this]

end Work.ZJB


