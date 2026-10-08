import Mathlib
import Submission.Work.CORE2B.fittingIn_U_normalizer
import Submission.Work.CORE2B.oddCore_odd
import Submission.Work.CORE2B.L27cf_helpers
import Submission.Work.CORE2B.HallAux
import Submission.Work.CORE2B.L27_fittingPi_compl_of_odd
import Submission.Work.CORE2B.L27cf_centralizes_odd_pi_part

namespace Work.CORE2B

open Subgroup

/-!
# CORE2B, design pass 12, leaf `L27v12_oddpart_mem_fittingU`

Every element of **odd order** of `F(Ĥ)` lies in `F(U)`, where `U = O(H) = O(Ĥ)` (Theorem 2.6).

Route.

* `⟨y⟩ ≤ F(Ĥ)` has odd order, and an odd-order subgroup of `F(Ĥ)` lies in the `2'`-part
  `Z := F_{2'}(Ĥ) = O_{2'}(F(Ĥ))` of the Fitting subgroup of `Ĥ`
  (`L27_fittingPi_compl_of_odd`, already proved in the area).  Hence `y ∈ Z`.
* `Z ◁ Ĥ` (`le_normalizer_fittingPiIn`) and `Z` has odd order, so `Z ≤ O(Ĥ) = U`
  (maximality of `O_{2'}`, Theorem 2.6's `oddCoreIn B.Hhat = B.U`).
* `Z ≤ F(Ĥ)` is nilpotent (a subgroup of the nilpotent `F(Ĥ)`), and `U ≤ Ĥ` normalizes it, so `Z`
  is a normal nilpotent subgroup of `U`, i.e. `Z ≤ F(U)`
  (`le_fittingIn_of_le_normalizer_of_isNilpotent_local`).

The helper `L27v12_le_oddCoreIn_of_normal_of_odd` is a copy of
`Work.CORE2A.le_oddCoreIn_of_normal_of_odd`: the two areas carry separate copies of the `Work.GW2`
vocabulary, which clash, so no `CORE2A` module can be imported here.
-/

/-- **Maximality of `O_{2'}(M)`.** An odd-order subgroup `X ≤ M` that is normal in `M` lies in
`O_{2'}(M) = Work.GW2.oddCoreIn M`. -/
theorem L27v12_le_oddCoreIn_of_normal_of_odd {G : Type} [Group G] [Finite G] {X M : Subgroup G}
    (hXM : X ≤ M) (hn : (X.subgroupOf M).Normal) (hodd : Odd (Nat.card X)) :
    X ≤ Work.GW2.oddCoreIn M := by
  -- `X.subgroupOf M` is a copy of `X`, so it also has odd order.
  have hcard : Nat.card (X.subgroupOf M) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv
  have hodd' : Odd (Nat.card (X.subgroupOf M)) := hcard.symm ▸ hodd
  -- Inside `↥M`, the normal odd-order subgroup `X.subgroupOf M` lies in `O_{2'}(↥M)`.
  have hle : X.subgroupOf M ≤ Work.GW2.oddCore ↥M :=
    (Subgroup.normal_le_normalCore (N := X.subgroupOf M) (hN := hn)
      (H := sSup {N : Subgroup ↥M | N.Normal ∧ Odd (Nat.card N)})).mpr
      (le_sSup ⟨hn, hodd'⟩)
  -- Transport along `M.subtype`: `X.subgroupOf M` maps onto `X`.
  rw [← Subgroup.map_subgroupOf_eq_of_le hXM]
  simpa [Work.GW2.oddCoreIn] using Subgroup.map_mono (f := M.subtype) hle

theorem L27v12_oddpart_mem_fittingU (h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    {y : G} (hy : y ∈ Work.GW2.fittingIn B.Hhat) (hodd : Odd (orderOf y)) :
    y ∈ Work.GW2.fittingIn B.U := by
  -- ## Step 1: `y ∈ Z := F_{2'}(Ĥ)`, because `⟨y⟩ ≤ F(Ĥ)` has odd order.
  have hyZ : y ∈ Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) B.Hhat :=
    L27_fittingPi_compl_of_odd G B.Hhat (Subgroup.zpowers y) (Subgroup.zpowers_le.mpr hy)
      (by rw [Nat.card_zpowers]; exact hodd) (Subgroup.mem_zpowers y)
  -- ## Step 2: `Z ≤ U`.  `Z` is normal in `Ĥ` of odd order, so `Z ≤ O(Ĥ) = U` (Theorem 2.6).
  have hZK : Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) B.Hhat ≤ B.Hhat :=
    (in_le_self B.Hhat 2 ({2}ᶜ : Set ℕ)).2.2.2.1
  have hZnorm : B.Hhat ≤ Subgroup.normalizer
      ((Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) B.Hhat : Subgroup G) : Set G) :=
    le_normalizer_fittingPiIn ({2}ᶜ : Set ℕ) B.Hhat
  have hZodd : Odd (Nat.card (Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) B.Hhat)) :=
    L27cf_odd_card_fittingPiIn (σ := ({2}ᶜ : Set ℕ)) (by intro p hp; exact hp) B.Hhat
  have hZsub : ((Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) B.Hhat).subgroupOf B.Hhat).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZK).mpr hZnorm
  have hZU : Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) B.Hhat ≤ B.U := by
    rw [← (h26 G hFT hCtx B).1]
    exact L27v12_le_oddCoreIn_of_normal_of_odd hZK hZsub hZodd
  -- ## Step 3: `Z ≤ F(U)`.  `Z` is a normal nilpotent subgroup of `U`: `Z ≤ F(Ĥ)` is nilpotent
  -- (a subgroup of the nilpotent `F(Ĥ)`), and `U ≤ Ĥ` normalizes it.
  have hZFH : Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) B.Hhat ≤ Work.GW2.fittingIn B.Hhat := by
    rw [Work.GW2.fittingPiIn, Work.GW2.fittingPi]
    exact Subgroup.map_mono (Subgroup.map_subtype_le _)
  haveI hFnil : Group.IsNilpotent ↥(Work.GW2.fittingIn B.Hhat) := by
    rw [Work.GW2.fittingIn]
    exact (Group.isNilpotent_congr (Subgroup.equivMapOfInjective (Work.GW2.fitting ↥B.Hhat)
      B.Hhat.subtype B.Hhat.subtype_injective)).mp (L27cf_isNilpotent_fitting (G := ↥B.Hhat))
  haveI hZnil : Group.IsNilpotent ↥(Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) B.Hhat) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hZFH)).mp inferInstance
  have hUHhat : B.U ≤ B.Hhat := (in_le_self B.H 2 B.pi).1.trans B.H_le_Hhat
  have hZFU : Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) B.Hhat ≤ Work.GW2.fittingIn B.U :=
    le_fittingIn_of_le_normalizer_of_isNilpotent_local hZU (hUHhat.trans hZnorm)
  exact hZFU hyZ

end Work.CORE2B
