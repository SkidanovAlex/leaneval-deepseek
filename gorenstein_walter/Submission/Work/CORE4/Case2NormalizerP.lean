import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup

namespace Work.CORE4

open Subgroup

/-- **Subgroups of a cyclic group are normalised by anything normalising the ambient group.**

If `F ≤ G` is cyclic, `P ≤ F` and `g` normalises `F`, then `g` normalises `P`.  Indeed
`P^g ≤ F^g = F` and `|P^g| = |P|`, and in a cyclic group subgroups of equal order coincide
(`IsCyclic.subgroup_eq_iff_card_eq`). -/
lemma conjSub_eq_self_of_le_cyclic {G : Type*} [Group G] [Finite G] {F P : Subgroup G}
    (hF : IsCyclic F) (hP : P ≤ F) {g : G} (hg : g ∈ Subgroup.normalizer (F : Set G)) :
    Work.GW2.conjSub g P = P := by
  haveI : IsCyclic ↥F := hF
  have hconj_le : Work.GW2.conjSub g P ≤ F := by
    have h1 : Work.GW2.conjSub g P ≤ Work.GW2.conjSub g F := Subgroup.map_mono hP
    have h2 : Work.GW2.conjSub g F = F := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    rwa [h2] at h1
  have hcard : Nat.card ↥(P.subgroupOf F) = Nat.card ↥((Work.GW2.conjSub g P).subgroupOf F) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hconj_le).toEquiv]
    exact (Subgroup.card_map_of_injective (K := P) (MulAut.conj g).injective).symm
  have heq : P.subgroupOf F = (Work.GW2.conjSub g P).subgroupOf F :=
    (IsCyclic.subgroup_eq_iff_card_eq).mpr hcard
  have hmap := congrArg (Subgroup.map F.subtype) heq
  rw [Subgroup.map_subgroupOf_eq_of_le hP, Subgroup.map_subgroupOf_eq_of_le hconj_le] at hmap
  exact hmap.symm

/-- §4 (11)/(12), first step: for a nontrivial subgroup `P ≤ F = B₀ ⊓ F(U)`, `N_G(P) = M`.
`M = N_G(F) ≤ N_G(P)` because `F` is cyclic and a subgroup of a cyclic group is the unique
subgroup of its order; conversely `g ∈ N_G(P)`, `g ∉ M` would give `P ≤ F ⊓ F^g = ⊥` by the
TI-property `F_ti`. -/
theorem Case2NormalizerP :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
      (P : Subgroup G), P ≤ h.D.F → P ≠ ⊥ → Subgroup.normalizer (P : Set G) = h.D.M := by
  intro G _ _ B h P hPF hPne
  apply le_antisymm
  · -- `N_G(P) ≤ M`: an element outside `M` would place `P` inside `F ⊓ F^g = ⊥`.
    intro g hg
    by_contra hgm
    have hti := h.F_ti g hgm
    have hconj : Work.GW2.conjSub g P = P := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hle : P ≤ h.D.F ⊓ Work.GW2.conjSub g h.D.F := by
      refine le_inf hPF ?_
      rw [← hconj]
      exact Subgroup.map_mono hPF
    rw [hti] at hle
    exact hPne (le_bot_iff.mp hle)
  · -- `M = N_G(F) ≤ N_G(P)`: `F` is cyclic, so it has a unique subgroup of each order.
    intro g hg
    rw [← Work.GW2.Case2Pre.N_F B h.D h.pre] at hg
    have hconj : Work.GW2.conjSub g P = P :=
      conjSub_eq_self_of_le_cyclic h.F_cyclic hPF hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconj

end Work.CORE4
