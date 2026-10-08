import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.Q1_isNilpotent_of_D_ne_bot
import Submission.Work.FeitSibley.Coherence.centerMod
import Submission.Work.FeitSibley.Coherence.le_normalizer_commutator
import Submission.Work.LocalPrelim.pgroup_commutator_ne_self

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi II, App. XII: `⁅Q₂, Q₁⁆ ≤ Q₃` for a chief factor `Q₂/Q₃`

This is the chief-factor step used by Peterfalvi II, Appendice XII, step (1)
(`Submission/Work/FeitSibley/Coherence/step1.lean`): if `Q₃ ≤ Q₂ ≤ [Q₁,Q₁]` are both
normalised by `H`, `Q₂ ≠ Q₃` and there is no `H`-invariant subgroup strictly between them
(`hchief`), then `Q₁` centralises `Q₂/Q₃`, i.e. `⁅Q₂,Q₁⁆ ≤ Q₃`.

The mathematical input is that `Q₁` is nilpotent (Thompson's theorem, here
`Q1_isNilpotent_of_D_ne_bot`, which is why the hypothesis `h.D ≠ ⊥` is present), together
with the elementary fact that in a nilpotent group `P` one has `N = M` for subgroups
`M ≤ N ≤ P` normalised by `P` as soon as `N = M·⁅N,P⁆` ("nilpotent Nakayama": the
augmentation ideal of `F_p[P]` is nilpotent).  We prove that as
`nilpotent_commutator_le_of_le_sup_ambient` (with its in-group core
`nilpotent_commutator_le_of_le_sup_core`, which is obtained by quotienting by `M` and
applying `Work.LocalPrelim.exists_notMem_commutator_of_isNilpotent`).

Assembly of the chief-factor argument: if `⁅Q₂,Q₁⁆ ⊄ Q₃`, then `Q₃ ⊔ ⁅Q₂,Q₁⁆` is a
`H`-invariant subgroup strictly between `Q₃` and `Q₂` (it is `H`-invariant because `H`
normalises `Q₃` and, `H ≤ N(Q₂)` together with `H ≤ N(Q₁)`, also `⁅Q₂,Q₁⁆`), so by `hchief`
it equals `Q₂`; then `Q₂ = Q₃ ⊔ ⁅Q₂,Q₁⁆` and the nilpotency lemma (applied with `P = Q₁`)
give the contradiction `⁅Q₂,Q₁⁆ ≤ Q₃`.
-/

open Classical

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.FeitSibley.Coherence

noncomputable section

/-! ## The nilpotency input -/

/-- **Nilpotent Nakayama, in a group.**  If `G` is nilpotent, `M,N ◁ G`, `M ≤ N` and
`N ≤ M·⁅N,G⁆`, then `⁅N,G⁆ ≤ M`.

Proof: quotient by `M`.  Then `N/M` is a normal subgroup of the nilpotent group `G/M` with
`N/M ≤ ⁅N/M, G/M⁆`, hence `N/M = ⁅N/M, G/M⁆`; but a nontrivial normal subgroup of a
nilpotent group never equals its commutator with the whole group
(`Work.LocalPrelim.exists_notMem_commutator_of_isNilpotent`), so `N/M = ⊥`, i.e. `N ≤ M`. -/
theorem nilpotent_commutator_le_of_le_sup_core {G : Type*} [Group G] [Group.IsNilpotent G]
    {M N : Subgroup G} [hMn : M.Normal] [hNn : N.Normal]
    (hMN : M ≤ N) (h : N ≤ M ⊔ ⁅N, ⊤⁆) : ⁅N, ⊤⁆ ≤ M := by
  by_contra hcon
  have hsurj : Function.Surjective (QuotientGroup.mk' M) := QuotientGroup.mk'_surjective M
  have hker : (QuotientGroup.mk' M).ker = M := QuotientGroup.ker_mk' M
  have hbot0 : Subgroup.map (QuotientGroup.mk' M) M = ⊥ :=
    (Subgroup.map_eq_bot_iff M).mpr (le_of_eq hker.symm)
  have hmaple : Subgroup.map (QuotientGroup.mk' M) N ≤
      ⁅Subgroup.map (QuotientGroup.mk' M) N, ⊤⁆ := by
    have h1 := Subgroup.map_mono (f := QuotientGroup.mk' M) h
    rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr hsurj, hbot0] at h1
    simpa using h1
  have hEq : Subgroup.map (QuotientGroup.mk' M) N =
      ⁅Subgroup.map (QuotientGroup.mk' M) N, ⊤⁆ :=
    le_antisymm hmaple (Subgroup.commutator_le_left _ ⊤)
  by_cases hbot : Subgroup.map (QuotientGroup.mk' M) N = ⊥
  · refine hcon ((Subgroup.commutator_le_left N ⊤).trans ?_)
    rw [Subgroup.map_eq_bot_iff, hker] at hbot
    exact hbot
  · obtain ⟨x, hxN, hxcomm⟩ :=
      Work.LocalPrelim.exists_notMem_commutator_of_isNilpotent (G := G ⧸ M) hbot
    exact hxcomm (hEq ▸ hxN)

/-- **Nilpotent Nakayama, ambient form.**  Let `P` be a nilpotent subgroup of `G` and let
`M ≤ N ≤ P` be subgroups normalised by `P`.  If `N ≤ M·⁅N,P⁆` then `⁅N,P⁆ ≤ M`.

This is the form used for `P = Q₁`, `M = Q₃`, `N = Q₂`; the proof transports the previous
lemma to the group `↥P` (`M.subgroupOf P ≤ N.subgroupOf P`) and back along `P.subtype`. -/
theorem nilpotent_commutator_le_of_le_sup_ambient {G : Type*} [Group G] {P M N : Subgroup G}
    [Group.IsNilpotent ↥P] (hMN : M ≤ N) (hN : N ≤ P)
    (hPnM : P ≤ Subgroup.normalizer (M : Set G))
    (hPnN : P ≤ Subgroup.normalizer (N : Set G))
    (h : N ≤ M ⊔ ⁅N, P⁆) : ⁅N, P⁆ ≤ M := by
  have hMleP : M ≤ P := hMN.trans hN
  have hcomm_le_P : ⁅N, P⁆ ≤ P :=
    (Subgroup.commutator_le_sup N P).trans (le_of_eq (sup_eq_right.mpr hN))
  haveI hM0n : (M.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMleP).mpr hPnM
  haveI hN0n : (N.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr hPnN
  have hM0N0 : M.subgroupOf P ≤ N.subgroupOf P := Subgroup.subgroupOf_mono P hMN
  have keyM : Subgroup.map P.subtype (M.subgroupOf P) = M := by
    rw [Subgroup.subgroupOf_map_subtype M P, inf_eq_left.mpr hMleP]
  have keyN : Subgroup.map P.subtype (N.subgroupOf P) = N := by
    rw [Subgroup.subgroupOf_map_subtype N P, inf_eq_left.mpr hN]
  have keyTop : Subgroup.map P.subtype (⊤ : Subgroup ↥P) = P := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have keyComm : Subgroup.map P.subtype ((⁅N, P⁆).subgroupOf P) = ⁅N, P⁆ := by
    change Subgroup.map P.subtype (Subgroup.comap P.subtype ⁅N, P⁆) = ⁅N, P⁆
    rw [Subgroup.map_comap_eq P.subtype ⁅N, P⁆, Subgroup.range_subtype,
      inf_eq_right.mpr hcomm_le_P]
  have hsub : (⁅N, P⁆).subgroupOf P = ⁅N.subgroupOf P, ⊤⁆ := by
    refine Subgroup.map_injective (f := P.subtype) (fun a b hab => Subtype.ext hab) ?_
    rw [Subgroup.map_commutator, keyComm, keyN, keyTop]
  have hle : N.subgroupOf P ≤ M.subgroupOf P ⊔ ⁅N.subgroupOf P, ⊤⁆ := by
    have h1 : N.subgroupOf P ≤ (M ⊔ ⁅N, P⁆).subgroupOf P := Subgroup.subgroupOf_mono P h
    rw [Subgroup.subgroupOf_sup hMleP hcomm_le_P, hsub] at h1
    exact h1
  have hcore : ⁅N.subgroupOf P, ⊤⁆ ≤ M.subgroupOf P :=
    nilpotent_commutator_le_of_le_sup_core hM0N0 hle
  have hmap := Subgroup.map_mono (f := P.subtype) hcore
  rw [Subgroup.map_commutator, keyN, keyTop, keyM] at hmap
  exact hmap

/-! ## The chief factor argument -/

theorem commutator_le_of_chief {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (hD : h.D ≠ ⊥)
    (Q2 Q3 : Subgroup G) (hQ3Q2 : Q3 ≤ Q2) (hQ2 : Q2 ≤ ⁅h.Q1, h.Q1⁆)
    (hQ2n : h.H ≤ Subgroup.normalizer (Q2 : Set G))
    (hQ3n : h.H ≤ Subgroup.normalizer (Q3 : Set G)) (hne : Q3 ≠ Q2)
    (hchief : ∀ A : Subgroup G, Q3 ≤ A → A ≤ Q2 → h.H ≤ Subgroup.normalizer (A : Set G) →
      A = Q3 ∨ A = Q2) :
    ⁅Q2, h.Q1⁆ ≤ Q3 := by
  -- `Q₁` is nilpotent (Thompson), because `D ≠ 1`.
  haveI hNil : Group.IsNilpotent ↥h.Q1 := Q1_isNilpotent_of_D_ne_bot h hD
  have hQ1leH : h.Q1 ≤ h.H := h.Q1_le_H
  have hQ1n2 : h.Q1 ≤ Subgroup.normalizer (Q2 : Set G) := hQ1leH.trans hQ2n
  have hQ1n3 : h.Q1 ≤ Subgroup.normalizer (Q3 : Set G) := hQ1leH.trans hQ3n
  have hQ2leQ1 : Q2 ≤ h.Q1 :=
    hQ2.trans ((Subgroup.commutator_le_sup h.Q1 h.Q1).trans (le_of_eq (sup_idem h.Q1)))
  -- `Q₂` and `⁅Q₂,Q₁⁆` are `H`-invariant, hence so is `Q₃ ⊔ ⁅Q₂,Q₁⁆`.
  have hMleQ2 : ⁅Q2, h.Q1⁆ ≤ Q2 :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hQ1n2
  have hHnM : h.H ≤ Subgroup.normalizer ((⁅Q2, h.Q1⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hQ2n h.Q1_normal_in_H
  have hHnA : h.H ≤ Subgroup.normalizer (((Q3 ⊔ ⁅Q2, h.Q1⁆ : Subgroup G)) : Set G) :=
    (le_inf hQ3n hHnM).trans (Subgroup.inf_normalizer_le_normalizer_sup Q3 ⁅Q2, h.Q1⁆)
  by_contra hcon
  have hA_le : Q3 ⊔ ⁅Q2, h.Q1⁆ ≤ Q2 := sup_le hQ3Q2 hMleQ2
  have hA_ne : Q3 ⊔ ⁅Q2, h.Q1⁆ ≠ Q3 := by
    intro heq
    exact hcon (le_sup_right.trans (le_of_eq heq))
  -- the chief factor hypothesis forces `Q₂ = Q₃ ⊔ ⁅Q₂,Q₁⁆`
  have hA_eq : Q3 ⊔ ⁅Q2, h.Q1⁆ = Q2 := by
    rcases hchief (Q3 ⊔ ⁅Q2, h.Q1⁆) le_sup_left hA_le hHnA with hh | hh
    · exact absurd hh hA_ne
    · exact hh
  exact hcon (nilpotent_commutator_le_of_le_sup_ambient hQ3Q2 hQ2leQ1 hQ1n3 hQ1n2
    (le_of_eq hA_eq.symm))

end

end Work.FeitSibley.Coherence
