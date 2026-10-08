import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.A7Split

namespace Work.CORE4.A7MEq

open Subgroup

/-- **`M ⊓ H = (U ⊓ M) · S` in the `A₇`-case of Bender §4 (the `Case2Ctx6` form).

This is `Work.CORE4.Case2Ctx.inter_H_M` with the two uses of §4 (9) (`Case2Ctx.nine`)
replaced by the corresponding consequences of the `A₇` hypothesis `A7Facts2`:

* `S ≤ M` comes from `A7Facts2` conjunct 3 (`S ≤ E(M) ≤ M`) instead of `Case2Ctx.S_le_M`;
* `H = U ⊔ S` comes from `Work.CORE4.A7Split` (which gets the dihedral shape of `S` from
  `BenderCtx.sylow` + `|S| = 8`) instead of `Case2Ctx.H_eq_U_sup_S` (which uses
  `I.toolkit.l2syl`).

Once `H = U ⊔ S`, `S ≤ M` and `U ≤ H`, the equality is the modular identity
`M ⊓ (U ⊔ S) = (M ⊓ U) ⊔ S`: an element `x ∈ M ⊓ H` is written `x = u * s` with `u ∈ U`,
`s ∈ S` (using `U ⊴ H`), and then `s ∈ S ≤ M` forces `u = x s⁻¹ ∈ M`. -/
theorem A7MEq_interHM6 (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
      Work.GW2.BenderCtx G → Work.GW2.A7Facts2 B C.D →
        C.D.M ⊓ B.H = (B.U ⊓ C.D.M) ⊔ (B.S : Subgroup G) := by
  intro G _ _ B C hbc h2
  have hH : B.H = B.U ⊔ (B.S : Subgroup G) := Work.CORE4.A7Split I hbc h2
  have hSleM : (B.S : Subgroup G) ≤ C.D.M :=
    le_trans h2.2.2.1 (Work.CORE4.layerIn_le C.D.M)
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxM, hxH⟩ := Subgroup.mem_inf.mp hx
    have htop : (B.U.subgroupOf B.H) ⊔ ((B.S : Subgroup G).subgroupOf B.H) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (Work.GW2.BenderSetup.U_le_H B)
        (Work.GW2.BenderSetup.S_le_H B), ← hH, Subgroup.subgroupOf_self]
    have hxH' : (⟨x, hxH⟩ : ↥B.H) ∈
        (B.U.subgroupOf B.H) ⊔ ((B.S : Subgroup G).subgroupOf B.H) := by
      rw [htop]; exact Subgroup.mem_top _
    have hUnorm : (B.U.subgroupOf B.H).Normal := Work.GW2.BenderSetup.U_normal B
    obtain ⟨u, hu, s, hs, hus⟩ := Subgroup.mem_sup_of_normal_left.mp hxH'
    have huU : (u : G) ∈ B.U := Subgroup.mem_subgroupOf.mp hu
    have hsS : (s : G) ∈ (B.S : Subgroup G) := Subgroup.mem_subgroupOf.mp hs
    have hxs : (u : G) * (s : G) = x := by
      have hh := congrArg (Subtype.val) hus
      simpa using hh
    have huM : (u : G) ∈ C.D.M := by
      have h2' : (u : G) = x * (s : G)⁻¹ := by rw [← hxs]; group
      rw [h2']
      exact C.D.M.mul_mem hxM (C.D.M.inv_mem (hSleM hsS))
    rw [← hxs]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨huU, huM⟩) hsS
  · refine sup_le ?_ ?_
    · exact le_inf inf_le_right (le_trans inf_le_left (Work.GW2.BenderSetup.U_le_H B))
    · exact le_inf hSleM (Work.GW2.BenderSetup.S_le_H B)

end Work.CORE4.A7MEq
