import Mathlib
import Submission.Work.Models.PSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Strong embedding is preserved by group isomorphisms

`LeanEval.GroupTheory.Defs.IsStronglyEmbedded K` says that `K` is a proper subgroup of
even order such that for every `g ∉ K` the intersection `K ⊓ K ^ g` has odd order.

We show that this notion transports along a group isomorphism `e : G ≃* H`:

* `K.map e = ⊤` iff `K = ⊤` (an isomorphism of groups induces an order isomorphism
  on the lattices of subgroups, so it preserves `⊤`);
* `Nat.card (K.map e) = Nat.card K` (`Subgroup.equivMapOfInjective` is an equivalence
  of groups between `K` and its image);
* the crucial computation: for `g : H`, writing `conj` for conjugation,
  `(K.map e).map (conj g) = (K.map (conj (e.symm g))).map e`, which together with
  `Subgroup.map_inf` (valid because `e` is injective) identifies the relevant
  intersections up to the order-preserving bijection `K ≃ K.map e`.
-/

namespace Work.Models.Transport

open LeanEval.GroupTheory.Defs

/-- Conjugation commutes with a group isomorphism: the image of `K` under `e`
conjugated by `e g` is the image under `e` of `K` conjugated by `g`. -/
lemma map_conj_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) (K : Subgroup G)
    (g : G) :
    (K.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom
      = (K.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem stronglyEmbedded_map {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {K : Subgroup G} (h : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded (K.map e.toMonoidHom) := by
  refine ⟨?_, ?_, ?_⟩
  · -- properness: `e` induces an order isomorphism of the subgroup lattices
    intro htop
    exact h.1 ((MulEquiv.mapSubgroup e).injective (by
      rw [OrderIso.map_top]
      simpa using htop))
  · -- even order: `K ≃* K.map e`
    have hc : Nat.card ↥(K.map e.toMonoidHom) = Nat.card ↥K :=
      (Nat.card_congr (Subgroup.equivMapOfInjective K e.toMonoidHom e.injective)).symm
    rw [hc]
    exact h.2.1
  · -- odd order of the intersections
    intro g hg
    have hgK : e.symm g ∉ K := by
      intro hmem
      exact hg ⟨e.symm g, hmem, e.apply_symm_apply g⟩
    have hodd := h.2.2 (e.symm g) hgK
    have key : (K ⊓ K.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom
        = K.map e.toMonoidHom ⊓
            (K.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ e.injective, ← map_conj_map e K (e.symm g),
        e.apply_symm_apply]
    have hcard : Nat.card ↥(K.map e.toMonoidHom ⊓
          (K.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom)
        = Nat.card ↥(K ⊓ K.map (MulAut.conj (e.symm g)).toMonoidHom) := by
      rw [← key]
      exact (Nat.card_congr (Subgroup.equivMapOfInjective
        (K ⊓ K.map (MulAut.conj (e.symm g)).toMonoidHom) e.toMonoidHom
        e.injective)).symm
    rw [hcard]
    exact hodd

end Work.Models.Transport
