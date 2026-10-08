import Mathlib
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.API

namespace Work.CORE4

/-- `|H : M ⊓ H| = |U : U ⊓ M|`, the index identity of the `A₇` sub-case of Bender §4.

Given `H = U · S` (Bender p. 219) and `S ≤ M` (the `A₇` case, where `S` is a Sylow
2-subgroup of `M`), the subgroup `S` is contained in `M ⊓ H`, so `H = U ⊔ (M ⊓ H)`.
Since `U ⊴ H`, the second isomorphism theorem gives `|H : M ⊓ H| = |U : U ⊓ (M ⊓ H)|`,
and `U ⊓ (M ⊓ H) = U ⊓ M` because `U ≤ H`. -/
theorem A7IndexCalc {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} {C : Work.GW2.Case2Ctx6 B}
    (hH : B.H = B.U ⊔ (B.S : Subgroup G)) (hSleM : (B.S : Subgroup G) ≤ C.D.M) :
    (C.D.M ⊓ B.H).relIndex B.H = (B.U ⊓ C.D.M).relIndex B.U := by
  -- `S ≤ M ⊓ H`: it lies in `M` by hypothesis and in `H = U · S`.
  have hS_le : (B.S : Subgroup G) ≤ C.D.M ⊓ B.H := le_inf hSleM B.S_le_H
  -- hence `H = U ⊔ (M ⊓ H)`, because `U · S ≤ U · (M ⊓ H) ≤ H`.
  have hsup : B.U ⊔ (C.D.M ⊓ B.H) = B.H := by
    refine le_antisymm (sup_le B.U_le_H inf_le_right) ?_
    exact hH.le.trans (sup_le le_sup_left (le_trans hS_le le_sup_right))
  -- second isomorphism theorem: `|H : M ⊓ H| = |U : U ⊓ (M ⊓ H)|`
  have hmain := relIndex_eq_relIndex_inf_of_normal_sup_eq B.U (C.D.M ⊓ B.H) B.H
    B.U_le_H inf_le_right hsup B.U_normal
  refine hmain.trans ?_
  -- `U ⊓ (M ⊓ H) = U ⊓ M`, since `U ≤ H`
  have key : B.U ⊓ (C.D.M ⊓ B.H) = B.U ⊓ C.D.M := by
    rw [← inf_assoc]
    exact inf_of_le_left (le_trans inf_le_left B.U_le_H)
  rw [key]

end Work.CORE4
