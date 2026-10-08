import Mathlib
import Submission.Work.RED.Basic
import Submission.Work.RED.centralizer_inf_sylow_eq
import Submission.Work.RED.normal_map_of_complement_sylow
import Submission.OddOrder.Isaacs.Ch05_Transfer.NilpotentPComplement
import Submission.OddOrder.Isaacs.Ch09_MoreSubnormality.SylowSubnormal

/-!
# RED: `C_G(N) = N` for a normal four-subgroup `N` when `O(G) = 1`

Let `G` be a finite group with `O(G) = 1` whose Sylow 2-subgroup `P` is dihedral of order
`2n` (`n ≥ 2`), and let `N ⊴ G` be a Klein four-group.  Then `C_G(N) = N`.

The argument (Gorenstein–Walter, "Klein case"; Bender's method):

* `N` is a normal `2`-subgroup, so `N ≤ P`; the dihedral self-centralizing fact gives
  `C_P(N) = N` (`Work.RED.centralizer_inf_sylow_eq`).
* `C := C_G(N)` is normal in `G` and `N ≤ C`; since `C ⊓ P = N` and `C` is normal,
  `N` is a Sylow `2`-subgroup of `C` (Isaacs Lemma 9.31), i.e. `|C : N|` is odd.
* By Burnside's normal `p`-complement theorem (transfer) applied inside `C`, the normal
  `2`-complement `K ⊴ C` of `N` exists: `C = N K`, `N ⊓ K = ⊥`, `K` of odd order.
  A normal `p`-complement is fixed by every automorphism of `C` (Isaacs §5E), so `K` is
  characteristic in `C`, hence normal in `G` (`Work.RED.normal_map_of_complement_sylow`).
* Every normal odd-order subgroup lies in `O(G) = 1`, so `K = 1` and `C = N`.

Note on the formal interface: the fields of `Work.RED.GW2.OddCoreFactsProp` (in particular
`le_oddCore`) quantify only over groups in `Type 0`, while the statement below is
universe-polymorphic.  The step "a normal odd-order subgroup lies in `O(G)`" is therefore
taken directly from the definition of `Work.RED.GW2.oddCore` (`le_oddCore_of_odd_normal'`).
-/

namespace Work.RED

open Subgroup

/-- Every normal odd-order subgroup is contained in `O(G)`; this is the content of
`OddCoreFactsProp.le_oddCore`, proved here directly from the definition of `oddCore` so that it
applies to a group in an arbitrary universe. -/
lemma le_oddCore_of_odd_normal' {G : Type*} [Group G] {N : Subgroup G} (hNn : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ Work.RED.GW2.oddCore G := by
  have hNn' : N.Normal := hNn
  exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hNn, hodd⟩)

theorem centralizer_eq_of_normal_fourGroup
    (hdi : Work.RED.GW2.DihedralFactsProp) (hodd : Work.RED.GW2.OddCoreFactsProp)
    {G : Type*} [Group G] [Finite G] {N : Subgroup G} (hNn : N.Normal)
    (hN4 : Work.RED.GW2.IsFourGroup N) (hO : Work.RED.GW2.oddCore G = ⊥)
    {n : ℕ} [NeZero n] {P : Sylow 2 G} (e : ↥(P : Subgroup G) ≃* DihedralGroup n) (hn : 2 ≤ n) :
    Subgroup.centralizer (N : Set G) = N := by
  classical
  have hNn' : N.Normal := hNn
  set C : Subgroup G := Subgroup.centralizer (N : Set G) with hCdef
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hNleC : N ≤ C := le_centralizer_self_of_isFourGroup hN4
  -- the centralizer meets the Sylow subgroup `P` in `N`
  have hCP : C ⊓ (P : Subgroup G) = N := by
    simpa [hCdef] using centralizer_inf_sylow_eq hdi hNn hN4 e hn
  -- hence the index of `N` in `C` is odd, i.e. `N` is a Sylow 2-subgroup of `C`
  have hNidx : ¬ 2 ∣ (N.subgroupOf C).index := by
    have hCn' : C.Normal := hCn
    have h := OddOrder.Isaacs.Ch09.not_dvd_relIndex_inf_of_normal C P
    have h' : ¬ 2 ∣ (((P : Subgroup G) ⊓ C).subgroupOf C).index := h
    rw [inf_comm, hCP] at h'
    exact h'
  have hNc2 : IsPGroup 2 ↥(N.subgroupOf C) :=
    (Work.RED.GW2.IsFourGroup.isPGroup_two hN4).comap_subtype (K := C)
  let Q : Sylow 2 ↥C := hNc2.toSylow hNidx
  have hQcoe : (Q : Subgroup ↥C) = N.subgroupOf C := IsPGroup.toSylow_coe hNc2 hNidx
  -- the normalizer of `Q` in `C` centralizes `Q` (everything in `C` centralizes `N`)
  have hQcent : Subgroup.normalizer (Q : Set ↥C) ≤
      Subgroup.centralizer ((Q : Subgroup ↥C) : Set ↥C) := by
    intro x _hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hxN : (x : G) ∈ Subgroup.centralizer (N : Set G) := x.2
    have hyN : (y : G) ∈ N := by
      have : y ∈ N.subgroupOf C := by rw [← hQcoe]; exact hy
      exact Subgroup.mem_subgroupOf.mp this
    exact Subgroup.mem_centralizer_iff.mp hxN (y : G) hyN
  -- Burnside's normal 2-complement theorem (transfer), inside `C`
  let K : Subgroup ↥C := (MonoidHom.transferSylow Q hQcent).ker
  have hKcompl : Subgroup.IsComplement' K (Q : Subgroup ↥C) :=
    MonoidHom.ker_transferSylow_isComplement' Q hQcent
  have hKn : K.Normal := MonoidHom.normal_ker _
  have hKodd : Odd (Nat.card K) := by
    have h := OddOrder.Isaacs.Ch05.not_dvd_card_of_isComplement'_sylow Q hKcompl
    exact Nat.not_even_iff_odd.mp (fun he => h (even_iff_two_dvd.mp he))
  -- `K` is characteristic in `C`, hence normal (and odd) in `G`
  have hK'normal : (K.map C.subtype).Normal :=
    normal_map_of_complement_sylow hCn hKn hKcompl
  have hK'odd : Odd (Nat.card (K.map C.subtype)) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hKodd
  have hK'le : K.map C.subtype ≤ Work.RED.GW2.oddCore G :=
    le_oddCore_of_odd_normal' hK'normal hK'odd
  have hK'bot : K.map C.subtype = ⊥ := by
    rw [hO] at hK'le
    exact le_bot_iff.mp hK'le
  have hKbot : K = ⊥ := by
    have h1 : K ≤ (C.subtype).ker := (Subgroup.map_eq_bot_iff K).mp hK'bot
    rw [Subgroup.ker_subtype] at h1
    exact le_bot_iff.mp h1
  have hQtop : (Q : Subgroup ↥C) = ⊤ := by
    have := hKcompl.sup_eq_top
    rw [hKbot, bot_sup_eq] at this
    exact this
  have hNctop : N.subgroupOf C = ⊤ := by rw [← hQcoe, hQtop]
  have hCleN : C ≤ N := by
    intro x hx
    have : (⟨x, hx⟩ : ↥C) ∈ N.subgroupOf C := by rw [hNctop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  exact le_antisymm hCleN hNleC

end Work.RED
