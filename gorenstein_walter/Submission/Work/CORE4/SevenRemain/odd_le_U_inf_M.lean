import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup

namespace Work.CORE4.SevenRemain

open Subgroup

/-- **General group-theory step.**  Let `A ≤ C`, `X ≤ C` with `A ⊴ C` (as a subgroup of `C`).
If `|X|` is coprime to `|C : A| = (A.subgroupOf C).index`, then `X ≤ A`.

Indeed, the image of `X` under the quotient map `C → C ⧸ A` is a subgroup of `C ⧸ A` whose
order divides `|X|` (`Subgroup.card_map_dvd`) and `|C ⧸ A|` (`Subgroup.card_dvd_of_le`), hence
is `1` by coprimality.  The image is then trivial, i.e. `X` lies in the kernel
`A.subgroupOf C` of the quotient map. -/
theorem le_of_coprime_card_relIndex {G : Type} [Group G] [Finite G]
    (A X C : Subgroup G) (hAC : A ≤ C) (hXC : X ≤ C) (hNorm : (A.subgroupOf C).Normal)
    (hcop : Nat.Coprime (Nat.card ↥X) (A.subgroupOf C).index) : X ≤ A := by
  have := hNorm
  set π := QuotientGroup.mk' (A.subgroupOf C) with hπ
  have hker : π.ker = A.subgroupOf C := QuotientGroup.ker_mk' _
  have hcardX : Nat.card ↥(X.subgroupOf C) = Nat.card ↥X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv
  have h1 : Nat.card ↥((X.subgroupOf C).map π) ∣ Nat.card ↥X := by
    have h := Subgroup.card_map_dvd (X.subgroupOf C) π
    rwa [hcardX] at h
  have h2 : Nat.card ↥((X.subgroupOf C).map π) ∣ (A.subgroupOf C).index := by
    have h := Subgroup.card_dvd_of_le (le_top : (X.subgroupOf C).map π ≤ ⊤)
    rwa [Subgroup.card_top] at h
  have h3 : Nat.card ↥((X.subgroupOf C).map π) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : (X.subgroupOf C).map π = ⊥ := Subgroup.card_eq_one.mp h3
  have h5 : X.subgroupOf C ≤ π.ker := (Subgroup.map_eq_bot_iff _).mp h4
  have h5' : X.subgroupOf C ≤ A.subgroupOf C := hker ▸ h5
  have hXeq : X = (X.subgroupOf C).map C.subtype := by
    rw [Subgroup.subgroupOf_map_subtype X C, inf_eq_left.mpr hXC]
  have hAeq : (A.subgroupOf C).map C.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype A C, inf_eq_left.mpr hAC]
  rw [hXeq, ← hAeq]
  exact Subgroup.map_mono h5'

/-- **§4: every odd-order subgroup of `H ⊓ M` lies in `U ⊓ M`** (`U = O(H)`).

`H ⊓ M = (U ⊓ M) ⊔ S` (`Case2Ctx.inter_H_M`, via `I.toolkit.split`) with `U ⊓ M ⊴ H ⊓ M`
(`Case2Ctx.U_inf_M_normal`) and `|H ⊓ M : U ⊓ M| = |S|` a power of 2
(`Case2Ctx.relIndex_inter_MH_inter_UM`).  For an odd-order `X ≤ H ⊓ M` the group
`X(U ⊓ M)/(U ⊓ M) ≅ X/(X ⊓ U ⊓ M)` is a quotient of `X`, hence odd, and a subgroup of the
2-group `H ⊓ M/(U ⊓ M)`, hence trivial: `X ≤ U ⊓ M`. -/
theorem odd_le_U_inf_M (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∀ X : Subgroup G, X ≤ B.H ⊓ h.D.M → Odd (Nat.card ↥X) → X ≤ B.U ⊓ h.D.M := by
  intro G _ _ _ B h X hX hodd
  -- `H ⊓ M` and `M ⊓ H` are the same subgroup, and every named §4 fact is stated for `M ⊓ H`.
  have hXC : X ≤ h.D.M ⊓ B.H := by rwa [inf_comm] at hX
  have hAC : B.U ⊓ h.D.M ≤ h.D.M ⊓ B.H :=
    le_inf inf_le_right (le_trans inf_le_left B.U_le_H)
  -- `|H ⊓ M : U ⊓ M| = |S|` and `|S|` is a power of `2`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card ↥(B.S : Subgroup G) = 2 ^ n :=
    IsPGroup.iff_card.mp B.S.isPGroup'
  have hindex : ((B.U ⊓ h.D.M).subgroupOf (h.D.M ⊓ B.H)).index =
      Nat.card ↥(B.S : Subgroup G) := by
    rw [← h.relIndex_inter_MH_inter_UM I]
    rfl
  refine le_of_coprime_card_relIndex (B.U ⊓ h.D.M) X (h.D.M ⊓ B.H) hAC hXC
    h.U_inf_M_normal ?_
  rw [hindex, hn]
  exact ((Nat.coprime_two_left.mpr hodd).symm).pow_right n

end Work.CORE4.SevenRemain
