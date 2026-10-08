import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4

/-- The Fitting subgroup of a nilpotent group is the whole group: `⊤` is a normal nilpotent
subgroup, so the `sSup` defining `F(G)` is `⊤`, and `⊤` is of course its own `normalCore`. -/
theorem fitting_eq_top_of_isNilpotent {G : Type} [Group G] [Group.IsNilpotent G] :
    Work.GW2.fitting G = ⊤ := by
  unfold Work.GW2.fitting
  have htop : (sSup {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N}) = ⊤ :=
    le_antisymm (sSup_le fun _ _ => le_top)
      (le_sSup ⟨inferInstance, (Group.isNilpotent_congr Subgroup.topEquiv).mpr inferInstance⟩)
  rw [htop, Subgroup.normalCore_eq_self ⊤]

/-- A finite `p`-group `K` is nilpotent, hence `F(K) = K` and therefore `F(K)`, viewed as a
subgroup of the ambient group `G`, is `K` itself. -/
theorem fittingIn_eq_self_of_isPGroup {G : Type} [Group G] [Finite G] {K : Subgroup G}
    {p : ℕ} [Fact p.Prime] (h : IsPGroup p K) : Work.GW2.fittingIn K = K := by
  have hnil : Group.IsNilpotent ↥K := IsPGroup.isNilpotent h
  rw [Work.GW2.fittingIn, fitting_eq_top_of_isNilpotent (G := ↥K)]
  ext x
  simp [Subgroup.mem_map]

end Work.CORE4
