import Mathlib
import Submission.Work.GLUE.Defs

-- the two `haveI`s below are genuine instance registrations for the following `exact`
set_option linter.style.haveILetI false

namespace Work.GLUE

/-- The Fitting subgroup of the area contract `Work.GW2.fitting` (the largest normal
nilpotent subgroup, `(sSup {N | N.Normal ∧ Group.IsNilpotent N}).normalCore`) agrees with
Isaacs' Fitting subgroup `OddOrder.Isaacs.Ch01.fitting` (the join `⨆ p, O_p(G)`).

The two `sSup`s generate the same subgroup: every normal nilpotent subgroup lies in Isaacs'
`fitting` (`nilpotent_normal_le_fitting`), and conversely Isaacs' `fitting` is itself normal
and nilpotent (`fitting.normal`, `fitting.isNilpotent`), so it is the greatest member of the
indexing family.  Since that `sSup` is the normal subgroup `fitting G`, its `normalCore`
wrapper is the identity. -/
theorem fitting_eq_isaacsFitting {G : Type*} [Group G] [Finite G] :
    Work.GW2.fitting G = OddOrder.Isaacs.Ch01.fitting G := by
  have hS : sSup {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N}
      = OddOrder.Isaacs.Ch01.fitting G := by
    refine le_antisymm (sSup_le ?_) (le_sSup ?_)
    · rintro N ⟨hN, hnil⟩
      haveI : N.Normal := hN
      haveI : Group.IsNilpotent ↥N := hnil
      exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    · exact ⟨OddOrder.Isaacs.Ch01.fitting.normal G,
        OddOrder.Isaacs.Ch01.fitting.isNilpotent⟩
  rw [Work.GW2.fitting, hS]
  exact Subgroup.normalCore_eq_self _

end Work.GLUE
