import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.NcardInvolsCentralizerEq
import Submission.Work.CORE3.NoElemAbelianCardEight
import Submission.Work.CORE3.CardCentralizerInfFourGroup
import Submission.Work.CORE3.NotLeCentralizerOfIsFourGroup

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# CORE3: the involutions of `Ĥ` commuting with `s ∈ Ĥ − V`

Bender 1981 §3, subcase `V = O₂(Ĥ)` of type `(2,2)`: for an involution `s ∈ Ĥ` outside
`V = O₂(Ĥ)`, the involutions of `Ĥ` commuting with `s` are exactly the three involutions of the
four-group `V`.  Equivalently `|I_Ĥ(s)| = 3` where `I_Ĥ(s)` counts involutions.

Mathematical content.  Write `V = O₂(Ĥ)` (Klein four-group), `U = O(Ĥ)` (odd), `N = V ⊔ U`,
so that `N ⊴ Ĥ` and `|Ĥ : N| = 6` (Bender's Theorem 2.6, the second alternative).  Since
`s ∉ N` (an involution of `N` lies in `V`, as `U` is odd) and `Ĥ/N` has order `6`, an involution
`x ∈ Ĥ` commuting with `s` has `xN ∈ {N, sN}` (two distinct commuting involutions of a group of
order `6` generate a four-group, of order `4 ∤ 6`).  Hence `x ∈ V` or `x = s·w` with `w ∈ V`;
the second case is an involution commuting with `s` precisely when `w` is centralized by `s`.
So the set is `(C_V(s) − 1) ∪ s·C_V(s)`, of cardinality `2·|C_V(s)| − 1`
(`Work.CORE3.NcardInvolsCentralizerEq`).

Finally `|C_V(s)| = 2`: `s ∉ V` gives `s ∉ C(V)` because `s ∈ C(V) ∩ Ĥ` forces `s ∈ V`, and
indeed if `V ≤ C(s)` then `⟨V, s⟩` is elementary abelian of order `8`, contradicting the
existence of a Sylow 2-subgroup of order `8` isomorphic to `DihedralGroup 4`
(`Work.CORE3.NoElemAbelianCardEight`, `Work.CORE3.NotLeCentralizerOfIsFourGroup`) together with
`Work.CORE3.CardCentralizerInfFourGroup`.  Hence `2·2 − 1 = 3`.
-/

namespace Work.CORE3

open Work.GW2

theorem CommutingInvolsOutsideV (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B) :
    ∀ s : G, s ∈ B.Hhat → orderOf s = 2 → s ∉ Work.GW2.pCoreIn 2 B.Hhat →
      (Work.GW2.involutionSet B.Hhat ∩ Subgroup.centralizer ({s} : Set G)).ncard = 3 := by
  intro s hsH hs2 hsV
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Bender's Theorem 2.6 in the configuration `Ĥ = V·U`.
  have h26 : Thm26Concl B := I.h26 G I.T.ft h B
  have hOC : oddCoreIn B.Hhat = B.U := h26.1
  have hVA : pCoreIn 2 B.Hhat ≤ B.Hhat := Subgroup.map_subtype_le _
  have hUA : B.U ≤ B.Hhat := Work.CORE2A.thm26Concl_U_le_Hhat h26
  have hVn : ((pCoreIn 2 B.Hhat).subgroupOf B.Hhat).Normal := by
    have heq : (pCoreIn 2 B.Hhat).subgroupOf B.Hhat = pCore 2 ↥B.Hhat := by
      ext x
      simp [pCoreIn, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    rw [heq]; infer_instance
  have hUn : ((B.U).subgroupOf B.Hhat).Normal := by
    have heq : (B.U).subgroupOf B.Hhat = oddCore ↥B.Hhat := by
      rw [← hOC]
      ext x
      simp [oddCoreIn, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    rw [heq]; infer_instance
  have hUodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  have hdisj : pCoreIn 2 B.Hhat ⊓ B.U = ⊥ := by
    have hcopVU : Nat.Coprime (Nat.card (pCoreIn 2 B.Hhat)) (Nat.card B.U) := by
      rw [D.four.1, show (4 : ℕ) = 2 ^ 2 from rfl]
      exact Nat.Coprime.pow_left 2 ((hUodd.coprime_two_right).symm)
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcopVU)
  have hUV : B.U ≤ Subgroup.centralizer ((pCoreIn 2 B.Hhat) : Set G) := by
    have hVleCU : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
      rw [← Work.CORE2A.thm26Concl_centralizer_eq h26]; exact inf_le_right
    exact (Subgroup.le_centralizer_iff).mp hVleCU
  have hq : (pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 := by
    rcases h26.2.2 with ⟨hle, -⟩ | ⟨-, h6, -⟩
    · exact absurd (isCyclic_of_le_of_isCyclic' hle B.S0_cyclic)
        (not_isCyclic_of_isFourGroup' D.four)
    · exact h6
  -- The Sylow 2-subgroup `S` has order `8` and is dihedral.
  have hdih : Nonempty (((B.S : Subgroup G)) ≃* DihedralGroup 4) := by
    obtain ⟨n, _hn2, ⟨e⟩⟩ := Work.CORE3.SylowDihedral G h B
    have hcardS : Nat.card (B.S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hn : n = 4 := by rw [D.S8] at hcardS; omega
    rw [hn] at e
    exact ⟨e⟩
  have hno : ¬ ∃ W : Subgroup G, Nat.card W = 8 ∧ ∀ x ∈ W, x ^ 2 = 1 :=
    NoElemAbelianCardEight B.S D.S8 hdih
  have hnot : ¬ pCoreIn 2 B.Hhat ≤ Subgroup.centralizer ({s} : Set G) :=
    NotLeCentralizerOfIsFourGroup (pCoreIn 2 B.Hhat) s D.four hs2 hsV hno
  have hsN : s ∈ Subgroup.normalizer ((pCoreIn 2 B.Hhat) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVA).mp hVn hsH
  have hm : Nat.card (pCoreIn 2 B.Hhat ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) = 2 :=
    CardCentralizerInfFourGroup (pCoreIn 2 B.Hhat) s D.four hsN hs2 hnot
  -- The count of involutions of `Ĥ` commuting with `s` is `2·|C_V(s)| − 1`.
  have hcount := NcardInvolsCentralizerEq B.Hhat (pCoreIn 2 B.Hhat) B.U s hVA hUA hVn hUn
    D.four hUodd hdisj hUV hq hsH hs2 hsV
  rw [hm] at hcount
  norm_num at hcount
  exact hcount

end Work.CORE3
