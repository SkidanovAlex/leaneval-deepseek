import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Submission.Work.CohomologicalShrinking.naturalAlpha.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.naturalAlpha

open scoped TensorProduct

/-- The value of `ψ` on the canonical generators, transported across a morphism of
representations and the induced map of the bottom `p`-central quotients.

This is the `tmul` case of `psiLin_natural`: it is pure computation with `H1π_comp_map_apply`
and the shape of `chainsMap₁` on a `Finsupp.single`. -/
private theorem psiLin_natural_generator (p : ℕ) [Fact p.Prime] {N N' : Type} [Group N] [Group N']
    (A : Rep (ZMod p) N) (A' : Rep (ZMod p) N') [A.IsTrivial] [A'.IsTrivial]
    (f : N →* N') (c : A ⟶ Rep.res f A')
    (ψ : TensorProduct (ZMod p) (Additive (Work.Shrinking.pCentralQuotient p N 0)) A.V →+ groupHomology.H1 A)
    (ψ' : TensorProduct (ZMod p) (Additive (Work.Shrinking.pCentralQuotient p N' 0)) A'.V →+ groupHomology.H1 A')
    (hψ : ∀ (x : ↥(Work.Shrinking.pCentralSeries p N 0)) (a : A.V),
        ψ (TensorProduct.tmul (ZMod p) (Additive.ofMul (QuotientGroup.mk'
              ((Work.Shrinking.pCentralSeries p N 1).subgroupOf
                (Work.Shrinking.pCentralSeries p N 0)) x) :
            Additive (Work.Shrinking.pCentralQuotient p N 0)) a)
          = groupHomology.H1π A ⟨Finsupp.single (x : N) a,
              (groupHomology.single_mem_cycles₁_iff (x : N) a).2
                (Representation.isTrivial_apply A.ρ (x : N) a)⟩)
    (hψ' : ∀ (x : ↥(Work.Shrinking.pCentralSeries p N' 0)) (a : A'.V),
        ψ' (TensorProduct.tmul (ZMod p) (Additive.ofMul (QuotientGroup.mk'
              ((Work.Shrinking.pCentralSeries p N' 1).subgroupOf
                (Work.Shrinking.pCentralSeries p N' 0)) x) :
            Additive (Work.Shrinking.pCentralQuotient p N' 0)) a)
          = groupHomology.H1π A' ⟨Finsupp.single (x : N') a,
              (groupHomology.single_mem_cycles₁_iff (x : N') a).2
                (Representation.isTrivial_apply A'.ρ (x : N') a)⟩)
    (x : ↥(Work.Shrinking.pCentralSeries p N 0)) (a : A.V) :
    ψ' (TensorProduct.map (pQMapLin p f) ((Rep.Hom.hom c).toLinearMap)
        (TensorProduct.tmul (ZMod p) (Additive.ofMul (QuotientGroup.mk'
              ((Work.Shrinking.pCentralSeries p N 1).subgroupOf
                (Work.Shrinking.pCentralSeries p N 0)) x) :
            Additive (Work.Shrinking.pCentralQuotient p N 0)) a))
      = (groupHomology.map f c 1).hom (ψ (TensorProduct.tmul (ZMod p)
            (Additive.ofMul (QuotientGroup.mk'
              ((Work.Shrinking.pCentralSeries p N 1).subgroupOf
                (Work.Shrinking.pCentralSeries p N 0)) x) :
            Additive (Work.Shrinking.pCentralQuotient p N 0)) a)) := by
  rw [TensorProduct.map_tmul, pQMapLin_mk, hψ x a,
    hψ' (pQTopHom p f x) ((Rep.Hom.hom c).toLinearMap a),
    groupHomology.H1π_comp_map_apply f c]
  congr 1
  refine Subtype.ext ?_
  rw [groupHomology.coe_mapCycles₁]
  simp only [groupHomology.chainsMap₁, pQTopHom_coe]
  simp [Finsupp.mapRange_single, Finsupp.mapDomain_single]

theorem psiLin_natural (p : ℕ) [Fact p.Prime] {N N' : Type} [Group N] [Group N']
    (A : Rep (ZMod p) N) (A' : Rep (ZMod p) N') [A.IsTrivial] [A'.IsTrivial]
    (f : N →* N') (c : A ⟶ Rep.res f A')
    (ψ : TensorProduct (ZMod p) (Additive (Work.Shrinking.pCentralQuotient p N 0)) A.V →+ groupHomology.H1 A)
    (ψ' : TensorProduct (ZMod p) (Additive (Work.Shrinking.pCentralQuotient p N' 0)) A'.V →+ groupHomology.H1 A')
    (hψ : ∀ (x : ↥(Work.Shrinking.pCentralSeries p N 0)) (a : A.V),
        ψ (TensorProduct.tmul (ZMod p) (Additive.ofMul (QuotientGroup.mk'
              ((Work.Shrinking.pCentralSeries p N 1).subgroupOf
                (Work.Shrinking.pCentralSeries p N 0)) x) :
            Additive (Work.Shrinking.pCentralQuotient p N 0)) a)
          = groupHomology.H1π A ⟨Finsupp.single (x : N) a,
              (groupHomology.single_mem_cycles₁_iff (x : N) a).2
                (Representation.isTrivial_apply A.ρ (x : N) a)⟩)
    (hψ' : ∀ (x : ↥(Work.Shrinking.pCentralSeries p N' 0)) (a : A'.V),
        ψ' (TensorProduct.tmul (ZMod p) (Additive.ofMul (QuotientGroup.mk'
              ((Work.Shrinking.pCentralSeries p N' 1).subgroupOf
                (Work.Shrinking.pCentralSeries p N' 0)) x) :
            Additive (Work.Shrinking.pCentralQuotient p N' 0)) a)
          = groupHomology.H1π A' ⟨Finsupp.single (x : N') a,
              (groupHomology.single_mem_cycles₁_iff (x : N') a).2
                (Representation.isTrivial_apply A'.ρ (x : N') a)⟩)
    (y : TensorProduct (ZMod p) (Additive (Work.Shrinking.pCentralQuotient p N 0)) A.V) :
    ψ' (TensorProduct.map (pQMapLin p f) ((Rep.Hom.hom c).toLinearMap) y)
      = (groupHomology.map f c 1).hom (ψ y) := by
  -- Both sides are additive in `y`, and the tensor product is spanned by the pure tensors
  -- `ofMul (mk' x) ⊗ a`: reduce to those and use the computation rules `hψ`, `hψ'`.
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m a =>
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
      ((Work.Shrinking.pCentralSeries p N 1).subgroupOf (Work.Shrinking.pCentralSeries p N 0))
      (Additive.toMul m)
    have hm : m = Additive.ofMul (QuotientGroup.mk'
        ((Work.Shrinking.pCentralSeries p N 1).subgroupOf
          (Work.Shrinking.pCentralSeries p N 0)) x) := by
      have h1 := congrArg Additive.ofMul hx.symm
      rwa [ofMul_toMul] at h1
    rw [TensorProduct.map_tmul, hm]
    exact psiLin_natural_generator p A A' f c ψ ψ' hψ hψ' x a
  | add u v hu hv =>
    simp only [map_add]
    rw [hu, hv]

end Work.CohomologicalShrinking.naturalAlpha
