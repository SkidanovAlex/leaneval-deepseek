import Mathlib
import Submission.Work.ORLocInd.Basic

namespace Work.ORLocInd.LI

/-- The infinite cyclic group `Multiplicative ℤ` is locally indicable.

Every subgroup `H` of a cyclic group is cyclic (`Subgroup.isCyclic`); since `Multiplicative ℤ` is
torsion-free, a nontrivial `H` contains an element of infinite order and is therefore infinite;
and an infinite cyclic group is isomorphic to `Multiplicative ℤ` (`intCyclicMulEquiv`), giving the
required surjection `H →* Multiplicative ℤ`. -/
theorem locallyIndicable_multiplicativeInt : Group.LocallyIndicable (Multiplicative ℤ) := by
  intro H _hFG hne
  -- A subgroup of a cyclic group is cyclic.
  have hcyc : IsCyclic H := Subgroup.isCyclic H
  -- A nontrivial subgroup of the torsion-free group `Multiplicative ℤ` is infinite.
  have hinf : Infinite H := by
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hx' : (x : Multiplicative ℤ) ≠ 1 := by simpa using hx
    have hinf' : (Subgroup.zpowers (x : Multiplicative ℤ) :
        Set (Multiplicative ℤ)).Infinite :=
      Set.infinite_coe_iff.mp (infinite_zpowers.mpr (not_isOfFinOrder_of_isMulTorsionFree hx'))
    have hle : (Subgroup.zpowers (x : Multiplicative ℤ) :
        Set (Multiplicative ℤ)) ⊆ (H : Set (Multiplicative ℤ)) :=
      Subgroup.zpowers_le.mpr x.2
    exact Set.infinite_coe_iff.mpr (Set.Infinite.mono hle hinf')
  -- An infinite cyclic group is isomorphic to `Multiplicative ℤ`.
  exact ⟨(intCyclicMulEquiv (G := H)).symm, (intCyclicMulEquiv (G := H)).symm.surjective⟩

end Work.ORLocInd.LI
