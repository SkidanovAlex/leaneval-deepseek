import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2Count11
import Submission.Work.CORE4.fourGroup_in_layerIn_subgroupOf
import Submission.Work.CORE4.odd_card_centralizer_layerIn_subgroupOf
import Submission.Work.CORE4.notMem_sup_centralizer_of_odd_of_center_eq_bot

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

/-- **LEAF C10.N5b `NineR`** (Bender p. 226): "`R := O(C_E(r))` has order `k'` and is inverted by
`t`", where `r ∈ (S ∩ M) ∖ E` is the outer involution of N5a.

This is stated over `C4Inputs10` (which is `C4Inputs` plus the `L2F` input
`l2outer : L2OuterInvolutionProp`, design pass 10 §3.4), because the proof needs that input; since
the body of `NineRProp` does not mention the bundle, this is literally a proof of
`NineRProp I.toC4Inputs`.  The sub-leaf `Work.CORE4.NineImpl9.NineR9` states the same thing with
the input as an explicit hypothesis; it follows from this theorem, since
`NineR { toC4Inputs := I, l2outer := h }` proves `NineRProp I` for `I : C4Inputs` and
`h : L2OuterInvolutionProp`.

Route (design pass 10 §3.3, N5b):
* `C_M(E)` has odd order: `C_M(E) ∩ E = Z(E) = 1` (`Z(E) = 1` from `NineCenter`'s route),
  and the dihedral `S ∩ M` (2-rank 2) cannot contain `(S ∩ E) × Ω₁(O₂(C_M(E)))`;
* so `r ∉ E·C_M(E)`: if `r = e·c` then `c² = 1`, hence `c = 1` and `r ∈ E`, contradiction;
* apply `L2OuterInvolutionProp` (= `I.l2outer`) with `Q = M`, `L = E`; `t ∈ E` is an involution
  commuting with `r` (t is central in `S`), so `C_E(r)` contains a cyclic `R` of order `k'` inverted
  by every involution of `C_E(r)`, in particular by `t`.

REVIEWER CHECK REQUESTED (design pass 10 item 5): "`C_M(E)` has odd order" at `q = 11`
(`C_E(r) ≅ A₄`, `N_M(E)/E ≅ S₃`).

The argument is uniform in `q` and in particular covers `q = 11`: for *every* odd `q ≥ 5` the group
`L₂(q) ≅ E(M)` contains a Klein four-subgroup `V` (its Sylow 2-subgroups are dihedral of order
`≥ 4`), and `M` has cyclic or dihedral Sylow 2-subgroups, hence 2-rank at most `2`; so an
involution `z ∈ C_M(E)` would make `V ⊔ ⟨z⟩` an elementary abelian subgroup of `M` of order `8`,
which is impossible.  No case distinction on `q` is needed.

Implementation: the three ingredients are proved in the sibling files
`fourGroup_in_layerIn_subgroupOf` (a Klein four-subgroup of `E(M)` inside `M`, transported from
`L₂(q)`'s dihedral Sylow 2-subgroups), `odd_card_centralizer_layerIn_subgroupOf` (`|C_M(E)|` odd,
from the 2-rank bound `≤ 2` for groups with cyclic or dihedral Sylow 2-subgroups) and
`notMem_sup_centralizer_of_odd_of_center_eq_bot` (`r ∉ E · C_M(E)` for `r` an involution outside
`E`, `C_M(E)` odd and `Z(E) = 1`). -/
theorem NineR (I : Work.GW2.C4Inputs10) : Work.GW2.NineRProp I.toC4Inputs := by
  intro G _ _ B C hH p e hp hshape hiso k k' hkd r hr hr2 hrE
  have hp' : Fact p.Prime := hp
  obtain ⟨hbc, _hc2, _hplus, _h7, _h8⟩ := hH
  -- `E = E(M) = layerIn C.D.M` sits in `M = C.D.M`, and `L := E.subgroupOf M ≤ ↥M`
  have hEM : Work.GW2.layerIn C.D.M ≤ C.D.M := Work.CORE4.layerIn_le C.D.M
  have hLnorm : ((Work.GW2.layerIn C.D.M).subgroupOf C.D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEM).mpr
      (Work.CORE4.layerIn_le_normalizer C.D.M)
  -- `E ≅ L₂(q)` has trivial centre (`E` is simple, `q ≥ 5`)
  have hcE : Subgroup.center ↥(Work.GW2.layerIn C.D.M) = ⊥ :=
    Work.CORE4.center_eq_bot_of_mulEquiv hiso.some
      (Work.CORE4.center_PSL2_bot p e hshape.1 hshape.2.1)
  have hcL : Subgroup.center ↥((Work.GW2.layerIn C.D.M).subgroupOf C.D.M) = ⊥ :=
    Work.CORE4.center_eq_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEM) hcE
  -- a Klein four-subgroup of `E`, and `|C_M(E)|` odd
  have hV : ∃ V : Subgroup ↥C.D.M,
      V ≤ (Work.GW2.layerIn C.D.M).subgroupOf C.D.M ∧ Work.GW2.IsFourGroup V :=
    Work.CORE4.fourGroup_in_layerIn_subgroupOf C I.toolkit.l2syl p e hshape hiso
  have hCodd : Odd (Nat.card (Subgroup.centralizer
      (((Work.GW2.layerIn C.D.M).subgroupOf C.D.M : Subgroup ↥C.D.M) : Set ↥C.D.M))) :=
    Work.CORE4.odd_card_centralizer_layerIn_subgroupOf C hbc hcL hV
  -- `r` as an element of `↥C.D.M`
  have hrM : r ∈ C.D.M := (Subgroup.mem_inf.mp hr).2
  set r' : ↥C.D.M := ⟨r, hrM⟩ with hr'def
  have hr'2 : orderOf r' = 2 := by rw [hr'def, Subgroup.orderOf_mk]; exact hr2
  have hr'L : r' ∉ (Work.GW2.layerIn C.D.M).subgroupOf C.D.M := by
    intro hm
    exact hrE (Subgroup.mem_subgroupOf.mp hm)
  -- `r` induces an automorphism of `E` that is not inner
  have hnotmem : r' ∉ (Work.GW2.layerIn C.D.M).subgroupOf C.D.M ⊔
      Subgroup.centralizer
        (((Work.GW2.layerIn C.D.M).subgroupOf C.D.M : Subgroup ↥C.D.M) : Set ↥C.D.M) :=
    Work.CORE4.notMem_sup_centralizer_of_odd_of_center_eq_bot _ hCodd hcL hr'2 hr'L
  have hsyM : Work.GW2.DihOrCycSylow ↥C.D.M := Work.CORE4.DihOrCycSub hbc.sylow C.D.M
  have hisoL : Nonempty (((Work.GW2.layerIn C.D.M).subgroupOf C.D.M) ≃*
      PSL(2, GaloisField p e)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hEM).trans hiso.some⟩
  have hk'conj : 2 * k' = p ^ e + 1 ∨ 2 * k' = p ^ e - 1 := by
    rcases hkd.2.2.1 with ⟨-, hc⟩ | ⟨-, hc⟩
    · exact Or.inr hc
    · exact Or.inl hc
  -- the `L2F` input, with `Q = ↥C.D.M` and `L = E(M)`
  obtain ⟨R', hR'L, hR'c, hR'card, _hR'cyc, hR'inv⟩ :=
    I.l2outer ↥C.D.M ((Work.GW2.layerIn C.D.M).subgroupOf C.D.M) p e hshape.1 hshape.2.1
      hLnorm hisoL hsyM r' hr'2 hnotmem k' hkd.2.1 hk'conj
  -- `t ∈ E` is an involution commuting with `r`
  have htE : B.t ∈ Work.GW2.layerIn C.D.M := C.D.t_mem
  have ht'2 : orderOf (⟨B.t, hEM htE⟩ : ↥C.D.M) = 2 := by
    rw [Subgroup.orderOf_mk]; exact B.t_order
  have ht'L : (⟨B.t, hEM htE⟩ : ↥C.D.M) ∈ (Work.GW2.layerIn C.D.M).subgroupOf C.D.M :=
    Subgroup.mem_subgroupOf.mpr htE
  have ht'r' : (⟨B.t, hEM htE⟩ : ↥C.D.M) * r' = r' * ⟨B.t, hEM htE⟩ := by
    apply Subtype.ext
    show B.t * r = r * B.t
    exact (Work.GW2.BenderSetup.t_central B r (Subgroup.mem_inf.mp hr).1).symm
  have hinv : Work.GW2.Inverts (⟨B.t, hEM htE⟩ : ↥C.D.M) R' :=
    hR'inv (⟨B.t, hEM htE⟩ : ↥C.D.M) ht'L ht'2 ht'r'
  -- push `R'` forward to `G`
  refine ⟨R'.map (C.D.M).subtype, ?_, ?_, ?_, ?_⟩
  · calc R'.map (C.D.M).subtype
        ≤ ((Work.GW2.layerIn C.D.M).subgroupOf C.D.M).map (C.D.M).subtype :=
          Subgroup.map_mono hR'L
      _ = Work.GW2.layerIn C.D.M := Subgroup.map_subgroupOf_eq_of_le hEM
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have hzcomm : r' * z = z * r' :=
      (Subgroup.mem_centralizer_iff.mp (hR'c hz)) r' (Set.mem_singleton r')
    simpa using congrArg (Subtype.val) hzcomm
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective C.D.M)]
    exact hR'card
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    have h := hinv z hz
    simpa using congrArg (Subtype.val) h

end Work.CORE4
