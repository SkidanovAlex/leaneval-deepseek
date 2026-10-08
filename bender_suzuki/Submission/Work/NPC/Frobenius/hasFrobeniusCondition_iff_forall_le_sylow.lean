/-
Area A9 of the Feit--Thompson drive: Frobenius' hypothesis.

This file proves that **Frobenius' condition only has to be checked on the non-trivial
subgroups of a single Sylow `p`-subgroup**:

`HasFrobeniusCondition p G ↔ ∀ Q ≤ P, Q ≠ ⊥ → IsConjPGroup p Q`

for a fixed Sylow `p`-subgroup `P`.  The substantive point is that `IsConjPGroup` is
invariant under conjugation (equivalently, under automorphisms of `G`), which is the
content of `isConjPGroup_map_equiv`; combined with Sylow's theorem (every `p`-subgroup
lies in a Sylow subgroup, and all Sylow subgroups are conjugate) it gives the stated
equivalence.

## Main results

* `Work.NPC.Frobenius.isConjPGroup_map_equiv` : `IsConjPGroup` is invariant under the
  automorphisms of `G` (`Q ↦ Q.map e`).
* `Work.NPC.Frobenius.hasFrobeniusCondition_iff_forall_le_sylow` : the main statement.
-/
import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.NPC.Frobenius

variable {G : Type*} [Group G]

/-- An automorphism `e` of `G` maps the centralizer of a set to the centralizer of its
image: `C_G(s).map e = C_G(e '' s)`. -/
lemma map_centralizer_eq_of_mulEquiv (e : G ≃* G) (s : Set G) :
    (Subgroup.centralizer s).map (e : G →* G) = Subgroup.centralizer (e '' s) := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image s (e : G →* G)) ?_
  intro x hx
  rw [Subgroup.mem_map]
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  have h := hx (e y) ⟨y, hy, rfl⟩
  apply e.injective
  rw [map_mul, map_mul, e.apply_symm_apply]
  exact h

/-- For an isomorphism `e : G ≃* G'` and subgroups `K ≤ H`, the restriction of `e` to
`H` carries `K` (viewed inside `H`) to `K.map e` (viewed inside `H.map e`). -/
lemma map_subgroupMap_subgroupOf {G' : Type*} [Group G'] (e : G ≃* G') (H K : Subgroup G) :
    Subgroup.map (e.subgroupMap H) (K.subgroupOf H)
      = (K.map (e : G →* G')).subgroupOf (H.map (e : G →* G')) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    exact ⟨(x : G), hx, (MulEquiv.coe_subgroupMap_apply e H x).symm⟩
  · intro hy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hy
    obtain ⟨x, hxK, hxy⟩ := hy
    have hxH : x ∈ H := by
      have hyH : (y : G') ∈ H.map (e : G →* G') := y.2
      rw [Subgroup.mem_map] at hyH
      obtain ⟨z, hz, hzy⟩ := hyH
      have hxz : x = z := e.injective (hxy.trans hzy.symm)
      rw [hxz]; exact hz
    refine ⟨⟨x, hxH⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]; exact hxK
    · apply Subtype.ext
      exact (MulEquiv.coe_subgroupMap_apply e H ⟨x, hxH⟩).trans hxy

/-- `IsConjPGroup` is invariant under automorphisms of the ambient group: an isomorphism
`e` of `G` induces an isomorphism `N_G(Q)/C_G(Q) ≃* N_G(e Q)/C_G(e Q)`, since `e` maps
`N_G(Q)` to `N_G(e Q)` and `C_G(Q)` to `C_G(e Q)`. -/
lemma isConjPGroup_map_equiv {p : ℕ} (e : G ≃* G) (Q : Subgroup G) :
    Work.NPC.IsConjPGroup p (Q.map (e : G →* G)) ↔ Work.NPC.IsConjPGroup p Q := by
  have hC : (Subgroup.centralizer (Q : Set G)).map (e : G →* G)
      = Subgroup.centralizer ((Q.map (e : G →* G) : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact map_centralizer_eq_of_mulEquiv e (Q : Set G)
  have hN : (Subgroup.normalizer (Q : Set G)).map (e : G →* G)
      = Subgroup.normalizer ((Q.map (e : G →* G) : Subgroup G) : Set G) :=
    Subgroup.map_equiv_normalizer_eq Q e
  have key := map_subgroupMap_subgroupOf e (Subgroup.normalizer (Q : Set G))
    (Subgroup.centralizer (Q : Set G))
  -- `C.subgroupOf N` is normal in `N`, hence so is its image under the isomorphism `e`.
  haveI hcn : (((Subgroup.centralizer (Q : Set G)).map (e : G →* G)).subgroupOf
      ((Subgroup.normalizer (Q : Set G)).map (e : G →* G))).Normal := by
    rw [← key]
    exact Subgroup.Normal.map inferInstance
      (e.subgroupMap (Subgroup.normalizer (Q : Set G)) :
        ↥(Subgroup.normalizer (Q : Set G)) →* ↥((Subgroup.normalizer (Q : Set G)).map (e : G →* G)))
      (fun y => ⟨(e.subgroupMap (Subgroup.normalizer (Q : Set G))).symm y,
        (e.subgroupMap (Subgroup.normalizer (Q : Set G))).apply_symm_apply y⟩)
  let Φ : ((Subgroup.normalizer (Q : Set G)) ⧸
        (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)))
      ≃* (Subgroup.normalizer ((Q.map (e : G →* G) : Subgroup G) : Set G) ⧸
            (Subgroup.centralizer ((Q.map (e : G →* G) : Subgroup G) : Set G)).subgroupOf
              (Subgroup.normalizer ((Q.map (e : G →* G) : Subgroup G) : Set G))) :=
    (QuotientGroup.congr _ _ (e.subgroupMap (Subgroup.normalizer (Q : Set G))) key).trans
      (QuotientGroup.equivQuotientSubgroupOfOfEq hC hN)
  unfold Work.NPC.IsConjPGroup
  exact ⟨fun h => IsPGroup.of_equiv h Φ.symm, fun h => IsPGroup.of_equiv h Φ⟩

/-- Frobenius' condition restricted to a Sylow subgroup: the natural action of `G` on its
Sylow `p`-subgroups (via conjugation) shows that assuming `N_G(Q)/C_G(Q)` is a `p`-group for
all non-trivial `Q ≤ P` implies it for all non-trivial `p`-subgroups of `G`. -/
theorem hasFrobeniusCondition_iff_forall_le_sylow {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    Work.NPC.HasFrobeniusCondition p G ↔
      ∀ Q : Subgroup G, Q ≤ (P : Subgroup G) → Q ≠ ⊥ → Work.NPC.IsConjPGroup p Q := by
  constructor
  · intro h Q hQ hQne
    exact h Q (P.isPGroup'.to_le hQ) hQne
  · intro h Q hQp hQne
    -- Every `p`-subgroup lies in a Sylow subgroup ...
    obtain ⟨S, hQS⟩ := IsPGroup.exists_le_sylow hQp
    -- ... and all Sylow subgroups are conjugate.
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
    have h1 : MulAut.conj g • (S : Subgroup G) = (P : Subgroup G) := by
      rw [← Sylow.coe_subgroup_smul]
      exact congrArg (fun T : Sylow p G => (T : Subgroup G)) hg
    have hQ'le : MulAut.conj g • Q ≤ (P : Subgroup G) :=
      calc MulAut.conj g • Q ≤ MulAut.conj g • (S : Subgroup G) :=
              Subgroup.map_mono hQS
        _ = (P : Subgroup G) := h1
    have hQ'ne : MulAut.conj g • Q ≠ ⊥ := by
      intro hbot
      apply hQne
      exact Subgroup.map_injective (MulAut.conj g).injective
        (show MulAut.conj g • Q = MulAut.conj g • (⊥ : Subgroup G) by rw [hbot, Subgroup.smul_bot])
    exact (isConjPGroup_map_equiv (MulAut.conj g) Q).mp (h _ hQ'le hQ'ne)

end Work.NPC.Frobenius
