import Mathlib
import Submission.Work.BG.nCases

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 in
theorem rem31GenEven {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    Even (orderOf (D.t1 * D.t2)) := by
  -- `t = t₀` is an involution lying in `S₀ = ⟨t₁t₂⟩`, so its order `2` divides
  -- the order of the generator `t₁t₂`.
  rw [even_iff_two_dvd]
  have hmem : D.t ∈ Subgroup.zpowers (D.t1 * D.t2) := D.gen ▸ D.t_mem
  have h := orderOf_dvd_of_mem_zpowers hmem
  rwa [D.t_order] at h

end Work.BG
