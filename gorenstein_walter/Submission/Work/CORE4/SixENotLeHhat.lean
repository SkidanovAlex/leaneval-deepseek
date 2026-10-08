import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs19
import Submission.Work.CORE4.LayerFactsProper
import Submission.Work.CORE4.API
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.CORE4.solvable_of_fourGroup_oddCore_relIndex_six
import Submission.Work.CORE4.false_of_center_involution_of_odd_center

namespace Work.CORE4

open Work.GW2 Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {G : Type} [Group G] [Finite G]

/-- `t ≠ 1`. -/
private theorem SixE_t_ne_one (B : Work.GW2.BenderSetup G) : B.t ≠ 1 := by
  intro h1
  have h2 := B.t_order
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

/-- **The layer of a proper subgroup containing `t`.**  If `M ≠ ⊤` and `t ∈ E(M)`, then `E(M)` is
quasisimple with odd centre.

This is the proper-subgroup form of `Work.CORE4.Case2S2_layer` (which assumes `IsCoatom M`): it is
`Work.CORE4.layer_facts_proper_quasisimple`, transported along `M.subtype` by
`Work.CORE4.quasisimple_shape_map`. -/
theorem layerIn_quasisimple_oddCenter (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    {B : Work.GW2.BenderSetup G} {M : Subgroup G} (hM : M ≠ ⊤) (ht : B.t ∈ Work.GW2.layerIn M) :
    Work.GW2.IsQuasisimple (Work.GW2.layerIn M) ∧
      Odd (Nat.card ↥(Subgroup.center ↥(Work.GW2.layerIn M))) := by
  obtain ⟨E1, _hE1norm, hlayer, hE1q, hodd, hshape⟩ :=
    layer_facts_proper_quasisimple I hbc hM ht
  have hEq : Work.GW2.layerIn M = E1.map (M.subtype) := by
    rw [Work.GW2.layerIn, hlayer]
  have hres := quasisimple_shape_map (M.subtype) (Subgroup.subtype_injective M) hE1q hodd hshape
  rw [hEq]
  exact ⟨hres.1, hres.2.1⟩

/-- **Design-19 leaf S1**: `E(M) ≰ Ĥ`.

Statement (verbatim from `_design_gw/Core19.lean` / `Defs19.lean`):
`SixENotLeHhatProp I` = for `BenderCtx G`, `B : BenderSetup G`, `D : Case2Data B` with
`Case2Pre B D`: `¬ layerIn D.M ≤ B.Hhat` (i.e. `E(M) ⊄ Ĥ`).

Route: suppose `E ≤ Ĥ`.  `I.thm26` (with `I.toolkit.ft`) gives `oddCoreIn Ĥ = U` and either
* (a) `Ĥ = H = C_G(t)`: then `E ≤ C_G(t)` and `t ∈ E` (`Case2Data.t_mem`) give `t ∈ Z(E)`, but
  `Odd (Nat.card (center ↥E₁))` (`Work.CORE4.layer_facts_proper`, applicable since
  `D.M_coatom.ne_top` and `D.t_mem`) contradicts `orderOf t = 2`
  (`Work.CORE4.false_of_center_involution_of_odd_center`);
* (b) `V := O₂(Ĥ)` is a four-group with `|Ĥ : VU| = 6`: `Ĥ` is solvable — it is an extension of the
  solvable `V U` (four-group times the odd-order `U`) by the group `Ĥ/VU` of order `6`
  (`Work.CORE4.solvable_of_fourGroup_oddCore_relIndex_six`) — while `E ≤ Ĥ` is perfect
  (quasisimple) and nontrivial (`t ∈ E`); a perfect section of a solvable group is trivial
  (`Group.IsPerfect.not_isSolvable`). -/
theorem SixENotLeHhat (I : Work.GW2.C4Inputs) : Work.GW2.C19.SixENotLeHhatProp I := by
  intro G _ _ hbc B D _hpre hle
  have h26 := I.thm26 G I.toolkit.ft hbc B
  have hEdata := layerIn_quasisimple_oddCenter I hbc D.M_coatom.ne_top D.t_mem
  rcases h26.2.2 with ⟨_, hHhat_eq_H⟩ | ⟨hfour, hrel, _⟩
  · -- (a) `Ĥ = H = C_G(t)`: `t ∈ E` is central of order `2`
    have hE_le_H : Work.GW2.layerIn D.M ≤ B.H := hHhat_eq_H ▸ hle
    have hcen : ∀ x ∈ Work.GW2.layerIn D.M, x * B.t = B.t * x := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hE_le_H hx)
    exact false_of_center_involution_of_odd_center (Work.GW2.layerIn D.M) hEdata.2 D.t_mem
      B.t_order hcen
  · -- (b) `Ĥ` is solvable while `E ≤ Ĥ` is perfect and nontrivial
    haveI hsolv : Group.IsSolvable ↥B.Hhat :=
      solvable_of_fourGroup_oddCore_relIndex_six I.toolkit.ft B h26.1 hfour hrel
    haveI : Group.IsSolvable ↥(Work.GW2.layerIn D.M) := by
      haveI : Group.IsSolvable ↥((Work.GW2.layerIn D.M).subgroupOf B.Hhat) := inferInstance
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hle).symm.injective
    haveI : Group.IsPerfect ↥(Work.GW2.layerIn D.M) :=
      Subgroup.isPerfect_iff.mpr hEdata.1.1
    haveI : Nontrivial ↥(Work.GW2.layerIn D.M) :=
      ⟨⟨⟨B.t, D.t_mem⟩, ⟨1, one_mem _⟩, fun h => SixE_t_ne_one B (congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isSolvable ↥(Work.GW2.layerIn D.M) inferInstance

end Work.CORE4
