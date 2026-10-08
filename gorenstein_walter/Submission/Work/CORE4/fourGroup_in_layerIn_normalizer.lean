import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.LayerFactsProper
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.CORE4.NineQuasisimpleSylowNotCyclic
import Submission.Work.CORE4.exists_fourGroup_le_layer
import Submission.Work.RED.DihedralFacts
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic

namespace Work.CORE4

open Subgroup

set_option linter.unusedVariables false

/-- A Klein four-group is carried to a Klein four-group by an injective homomorphism. -/
theorem fourGroup_map_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {V : Subgroup G} (h : Work.GW2.IsFourGroup V) :
    Work.GW2.IsFourGroup (V.map f) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hf, h.1]
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
    rw [← map_pow, h.2 v hv, map_one]

/-- A Klein four-group `W` contained in two subgroups `H₁, H₂` of `G` produces a Klein four-group
of `↥H₁` contained in the trace `H₂.subgroupOf H₁`. -/
theorem exists_subgroupOf_of_fourGroup {G : Type*} [Group G] {W H1 H2 : Subgroup G}
    (hW : Work.GW2.IsFourGroup W) (hWH1 : W ≤ H1) (hWH2 : W ≤ H2) :
    ∃ V : Subgroup ↥H1, V ≤ H2.subgroupOf H1 ∧ Work.GW2.IsFourGroup V := by
  refine ⟨W.subgroupOf H1, ?_, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hWH2 hx
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH1).toEquiv, hW.1]
  · intro v hv
    have hv' : (v : G) ∈ W := Subgroup.mem_subgroupOf.mp hv
    have h2 : (v : G) ^ 2 = 1 := hW.2 v.1 hv'
    exact Subtype.ext (by simpa using h2)

theorem fourGroup_in_layerIn_normalizer {G : Type} [Group G] [Finite G]
    (hbc : Work.GW2.BenderCtx G) {B : Work.GW2.BenderSetup G} {D : Work.GW2.Case2Data B}
    {X : Subgroup G} (hX : X ≠ ⊥) (hXF : X ≤ D.F)
    (ht : B.t ∈ Work.GW2.layerIn (Subgroup.normalizer (X : Set G)))
    (hE : Work.GW2.layerIn D.M ≤ Work.GW2.layerIn (Subgroup.normalizer (X : Set G))) :
    ∃ V : Subgroup ↥(Work.GW2.layerIn (Subgroup.normalizer (X : Set G))),
      V ≤ (Work.GW2.layerIn D.M).subgroupOf (Work.GW2.layerIn (Subgroup.normalizer (X : Set G))) ∧
        Work.GW2.IsFourGroup V := by
  -- `layerIn D.M` contains the involution `D.s`, hence is nontrivial.
  have hsM : D.s ∈ Work.GW2.layerIn D.M := (Subgroup.mem_inf.mp D.s_mem).2
  have hs1 : D.s ≠ 1 := by
    intro h1
    have h2 := D.s_order
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hlayer_ne : Work.GW2.layer ↥D.M ≠ ⊥ := by
    intro hbot
    have hbot' : Work.GW2.layerIn D.M = ⊥ := by
      rw [Work.GW2.layerIn, hbot, Subgroup.map_bot]
    exact hs1 (Subgroup.mem_bot.mp (hbot' ▸ hsM))
  -- A four-group inside the layer of `M` (a D-group, by `hbc`).
  obtain ⟨W₁, hW₁le, hW₁⟩ :=
    exists_fourGroup_le_layer (DihOrCycSub hbc.sylow D.M) hlayer_ne
  -- Push it into `G`: it becomes a four-group inside `layerIn D.M`.
  have hW : Work.GW2.IsFourGroup (W₁.map D.M.subtype) :=
    fourGroup_map_of_injective _ D.M.subtype_injective hW₁
  have hWle : W₁.map D.M.subtype ≤ Work.GW2.layerIn D.M := by
    rw [Work.GW2.layerIn]
    exact Subgroup.map_mono hW₁le
  -- It lies in the layer of `N_G(X)` by hypothesis, and in the layer of `M`.
  exact exists_subgroupOf_of_fourGroup hW (le_trans hWle hE) hWle

end Work.CORE4
