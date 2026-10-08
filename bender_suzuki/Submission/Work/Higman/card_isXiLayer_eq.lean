import Mathlib
import Submission.Work.Higman.BS.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.Higman

/-! ## Two bookkeeping lemmas for the cardinalities of `map` and `comap`

These are the "cardinality input" of the main result: for a homomorphism `f` and a subgroup `H`
containing `f.ker`, the image `H.map f` has order `|H| / |f.ker|`, and dually (for surjective
`f`) the preimage of `N` has order `|N| * |f.ker|`. -/

/-- `|H.map f| * |ker f| = |H|` for a subgroup `H` containing the kernel of `f`. -/
theorem card_map_mul_card_ker {G G' : Type} [Group G] [Group G'] (f : G →* G')
    {H : Subgroup G} (hf : f.ker ≤ H) :
    Nat.card ↥(H.map f) * Nat.card ↥(f.ker) = Nat.card ↥H := by
  have h1 : Nat.card ↥(f.ker.subgroupOf H) * (f.ker.subgroupOf H).index = Nat.card ↥H :=
    Subgroup.card_mul_index (f.ker.subgroupOf H)
  have h2 : (f.ker.subgroupOf H).index = Nat.card ↥(H.map f) := Subgroup.relIndex_ker H f
  have h3 : Nat.card ↥(f.ker.subgroupOf H) = Nat.card ↥(f.ker) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hf).toEquiv
  rw [h2, h3] at h1
  rw [mul_comm] at h1
  exact h1

/-- `|N.comap f| = |N| * |ker f|` for a surjective homomorphism `f`. -/
theorem card_comap_eq_card_mul_card_ker {G G' : Type} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Surjective f) (N : Subgroup G') :
    Nat.card ↥(N.comap f) = Nat.card ↥N * Nat.card ↥(f.ker) := by
  have hle : f.ker ≤ N.comap f := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact N.one_mem
  have h := card_map_mul_card_ker f hle
  rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top_of_surjective f hf, top_inf_eq] at h
  exact h.symm

/-- **Layers of `P` are `σ`-invariant subgroups of `P ⧸ Z(P)` of order `|Z(P)|`.**

The `ξ`-invariant subgroups `M` with `Z(P) ≤ M ≤ P` and `|M| = |Z(P)|²` (the `ξ`-layers of the
type-`B` characterisation) are in bijection with the `quotCenterAut ξ`-invariant subgroups
`N ≤ P ⧸ Z(P)` with `|N| = |Z(P)|`; hence the two sets of subgroups have the same cardinality.

The bijection is `M ↦ M.map (QuotientGroup.mk' (Subgroup.center P))` with inverse
`N ↦ N.comap (QuotientGroup.mk' (Subgroup.center P))`.  Cardinality input:
`Subgroup.relIndex_mul_index` and `Subgroup.relIndex_ker` for the projection, giving
`|M.map f| * |Z(P)| = |M|` for `Z(P) ≤ M` and dually `|N.comap f| = |N| * |Z(P)|`. -/
theorem card_isXiLayer_eq {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    (ξ : MulAut P) :
    Nat.card {M : Subgroup P // Work.Higman.IsXiLayer ξ M} =
      Nat.card {N : Subgroup (P ⧸ Subgroup.center P) //
        (∀ v ∈ N, Work.Higman.quotCenterAut ξ v ∈ N) ∧
          Nat.card N = Nat.card ↥(Subgroup.center P)} := by
  have hker : (Work.Higman.centerProj (P := P)).ker = Subgroup.center P :=
    QuotientGroup.ker_mk' _
  have hsurj : Function.Surjective (Work.Higman.centerProj (P := P)) :=
    Work.Higman.centerProj_surjective
  refine Nat.card_congr ⟨?_, ?_, ?_, ?_⟩
  · -- forward map: `M ↦ M.map (mk' Z(P))`
    intro M
    refine ⟨M.1.map (Work.Higman.centerProj (P := P)), ?_, ?_⟩
    · -- `quotCenterAut ξ`-invariance of the image
      intro v hv
      rw [Subgroup.mem_map] at hv ⊢
      obtain ⟨x, hx, rfl⟩ := hv
      exact ⟨ξ x, M.2.2.1 x hx, (Work.Higman.quotCenterAut_mk ξ x).symm⟩
    · -- the image has order `|Z(P)|`
      have h1 := card_map_mul_card_ker (Work.Higman.centerProj (P := P)) (H := M.1)
        (by rw [hker]; exact M.2.1)
      rw [hker] at h1
      rw [M.2.2.2, pow_two] at h1
      exact Nat.mul_right_cancel Nat.card_pos h1
  · -- inverse map: `N ↦ N.comap (mk' Z(P))`
    intro N
    refine ⟨N.1.comap (Work.Higman.centerProj (P := P)), ?_, ?_, ?_⟩
    · -- `Z(P) ≤ N.comap f` as `f.ker = Z(P)`
      intro x hx
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp (hker.symm ▸ hx)]
      exact N.1.one_mem
    · -- `ξ`-invariance of the preimage
      intro x hx
      rw [Subgroup.mem_comap] at hx ⊢
      rw [show Work.Higman.centerProj (P := P) (ξ x)
            = Work.Higman.quotCenterAut ξ (Work.Higman.centerProj (P := P) x)
          from (Work.Higman.quotCenterAut_mk ξ x).symm]
      exact N.2.1 _ hx
    · -- the preimage has order `|Z(P)|²`
      have h1 := card_comap_eq_card_mul_card_ker (Work.Higman.centerProj (P := P)) hsurj N.1
      rw [hker] at h1
      rw [N.2.2] at h1
      rw [pow_two]
      exact h1
  · -- `invFun ∘ toFun = id`
    intro M
    refine Subtype.ext ?_
    change Subgroup.comap (Work.Higman.centerProj (P := P))
        (Subgroup.map (Work.Higman.centerProj (P := P)) M.1) = M.1
    exact Subgroup.comap_map_eq_self (f := Work.Higman.centerProj (P := P))
      (by rw [hker]; exact M.2.1)
  · -- `toFun ∘ invFun = id`
    intro N
    refine Subtype.ext ?_
    change Subgroup.map (Work.Higman.centerProj (P := P))
        (Subgroup.comap (Work.Higman.centerProj (P := P)) N.1) = N.1
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top_of_surjective _ hsurj, top_inf_eq]

end Work.Higman
