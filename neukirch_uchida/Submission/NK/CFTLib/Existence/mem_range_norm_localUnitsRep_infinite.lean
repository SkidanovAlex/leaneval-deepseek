import Mathlib
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.Galois.globalCFT_localFixed_infinite
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_localAlgebraMapUnits
import Submission.NK.GlobalCFT.Galois.completionMap_surjective_of_isComplex_under
import Submission.NK.GlobalCFT.Galois.exists_stabilizer_isConj_of_isReal_isComplex
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleFun_principalIdele

/-!
# The local norm range at an archimedean place

For a finite Galois extension `N / K` of number fields and an infinite place `w` of `N` lying over
an infinite place `v` of `K`, the range of the norm endomorphism `Rep.norm` of the
`Γ_w`-representation `NK.HassePrinciple.localUnitsRep K N (Place.ofInfinite w)` (`Γ_w` the
stabilizer of `w` in `Gal(N/K)`, i.e. the decomposition group) is exactly the range of the local
norm `N_{N_w/K_v} = Place.localNormInfinite w v`, transported to `N_wˣ` along the completion
`NumberField.LiesOver.completionMap`.

This is the archimedean companion of `NK.CFTLib.IdeleHasse.Descent.mem_range_norm_localUnitsRep`
(the finite-place statement), proved exactly as there from the two ingredients

* `localUnitsRep_norm_apply`: the norm endomorphism of the local units representation is the
  product of the conjugates `∏_{γ ∈ Γ_w} γ(y)`, and
* `prod_localUnitsEquiv_eq_infinite`: that product is the completion of the local field norm.

For the second ingredient we use the already established archimedean computation
`NK.GlobalCFT.Inclusion.localNormInfinite_stab_prod` (the product of the conjugates of an idèle
at the stabilised place is the local norm of its component), together with
`NK.HassePrinciple.smul_apply_stabilizer` (the component of a translate at a stabilised place is
the local automorphism applied to the component) and the identification
`NK.GlobalCFT.Galois.localAlgebraMapUnits_ofInfinite_eq` of the local algebra map with
`Units.map completionMap`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open CategoryTheory
open NK.GlobalCFT

noncomputable section

namespace NK.CFTLib.Existence

variable {K N : Type} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
  [FiniteDimensional K N] [IsGalois K N]

/-- `Additive.ofMul` turns a product into a sum (in the additive group `Additive M`). -/
lemma sum_ofMul_eq_ofMul_prod {ι M : Type*} [CommMonoid M] (s : Finset ι) (f : ι → M) :
    (∑ i ∈ s, (Additive.ofMul (f i) : Additive M)) = Additive.ofMul (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ih]; rfl

/-- **The norm endomorphism of the local units representation is the product of the
conjugates.** -/
lemma localUnitsRep_norm_apply (w : Place N)
    [Fintype ↥(MulAction.stabilizer (N ≃ₐ[K] N) w)]
    (y : (Place.localField N w)ˣ) :
    (Rep.Hom.hom (Rep.norm (NK.HassePrinciple.localUnitsRep K N w))).toLinearMap
        (Additive.ofMul y)
      = Additive.ofMul (∏ γ : ↥(MulAction.stabilizer (N ≃ₐ[K] N) w),
          NK.HassePrinciple.localUnitsEquiv w γ y) := by
  change (Rep.Hom.hom (Rep.norm (NK.HassePrinciple.localUnitsRep K N w)))
      (Additive.ofMul y) = _
  rw [Rep.norm_apply]
  unfold Representation.norm
  rw [LinearMap.sum_apply]
  rw [show (∑ d, (NK.HassePrinciple.localUnitsRep K N w).ρ d (Additive.ofMul y))
      = ∑ d, (Additive.ofMul (NK.HassePrinciple.localUnitsEquiv w d y) :
          Additive (Place.localField N w)ˣ) from
    Finset.sum_congr rfl (fun d _ => by
      simp only [NK.HassePrinciple.localUnitsRep, Rep.ofDistribMulAction_ρ_apply_apply]
      rfl)]
  rw [sum_ofMul_eq_ofMul_prod]

/-- **The product of the `Γ_w`-conjugates is the completion of the local norm** (archimedean
case).

The stabilizer of the infinite place `w` is the local Galois group of `N_w / K_v` acting on
`N_wˣ`; hence the product of the conjugates `∏_{γ ∈ Γ_w} γ(y)` is the image of the field norm
`N_{N_w/K_v}(y)` under the completion `K_v →+* N_w`. -/
theorem prod_localUnitsEquiv_eq_infinite (w : NumberField.InfinitePlace N)
    (v : NumberField.InfinitePlace K) [w.LiesOver v]
    [Fintype ↥(MulAction.stabilizer (N ≃ₐ[K] N) (Place.ofInfinite w))]
    (u : (Place.localField N (Place.ofInfinite w))ˣ) :
    (∏ γ : ↥(MulAction.stabilizer (N ≃ₐ[K] N) (Place.ofInfinite w)),
        NK.HassePrinciple.localUnitsEquiv (Place.ofInfinite w) γ u)
      = Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom
          (Place.localNormInfinite w v u) := by
  classical
  -- the component of the idèle `onePlace w u` at the stabilised place is the local automorphism
  -- applied to `u`
  have hy : NK.HassePrinciple.onePlace (Place.ofInfinite w) u
      (Place.ofInfinite w) = u :=
    NK.HassePrinciple.onePlace_apply_self _ _
  -- the product over the stabilizer of the local components is the local norm
  have h := NK.GlobalCFT.Inclusion.localNormInfinite_stab_prod (K := K) (L := N) w v
    (NK.HassePrinciple.onePlace (Place.ofInfinite w) u)
  rw [hy] at h
  rw [NK.GlobalCFT.Galois.localAlgebraMapUnits_ofInfinite_eq (v := v) (w := w)
    (inferInstance : w.LiesOver v)] at h
  -- h : ∏ δ : {δ // δ • ofInfinite w = ofInfinite w}, (δ.1 • y) (ofInfinite w)
  --       = Units.map completionMap (localNormInfinite w v u)
  rw [← h]
  -- the two index types are the stabilizer as a subgroup and as a subtype; the products agree
  -- termwise
  exact @Fintype.prod_bijective
    ↥(MulAction.stabilizer (N ≃ₐ[K] N) (Place.ofInfinite w))
    {δ : N ≃ₐ[K] N // δ • Place.ofInfinite w = Place.ofInfinite w}
    (Place.localField N (Place.ofInfinite w))ˣ
    (inferInstanceAs (Fintype ↥(MulAction.stabilizer (N ≃ₐ[K] N) (Place.ofInfinite w))))
    (Subtype.fintype (fun δ : N ≃ₐ[K] N => δ • Place.ofInfinite w = Place.ofInfinite w))
    (inferInstanceAs (CommMonoid (Place.localField N (Place.ofInfinite w))ˣ))
    (fun x : ↥(MulAction.stabilizer (N ≃ₐ[K] N) (Place.ofInfinite w)) =>
      (x : {δ : N ≃ₐ[K] N // δ • Place.ofInfinite w = Place.ofInfinite w}))
    ⟨fun a b hab => hab, fun b => ⟨b, rfl⟩⟩
    (fun γ : ↥(MulAction.stabilizer (N ≃ₐ[K] N) (Place.ofInfinite w)) =>
      NK.HassePrinciple.localUnitsEquiv (Place.ofInfinite w) γ u)
    (fun δ : {δ : N ≃ₐ[K] N // δ • Place.ofInfinite w = Place.ofInfinite w} =>
      (δ.1 • NK.HassePrinciple.onePlace (Place.ofInfinite w) u) (Place.ofInfinite w))
    (fun γ => by rw [NK.HassePrinciple.smul_apply_stabilizer, hy]; rfl)

open CategoryTheory in
theorem mem_range_norm_localUnitsRep_infinite {K N : Type} [Field K] [NumberField K] [Field N]
    [NumberField N] [Algebra K N] [FiniteDimensional K N] [IsGalois K N]
    (w : NumberField.InfinitePlace N) (v : NumberField.InfinitePlace K) [w.LiesOver v]
    [Fintype ↥(MulAction.stabilizer (N ≃ₐ[K] N) (NK.GlobalCFT.Place.ofInfinite w))]
    (u : (NK.GlobalCFT.Place.localField N (NK.GlobalCFT.Place.ofInfinite w))ˣ) :
    (Additive.ofMul u ∈ LinearMap.range
      (Rep.norm (NK.HassePrinciple.localUnitsRep K N
        (NK.GlobalCFT.Place.ofInfinite w))).hom.toLinearMap)
      ↔ (∃ y, Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom
            (NK.GlobalCFT.Place.localNormInfinite w v y) = u) := by
  constructor
  · -- a `Γ_w`-norm is the completion of a local norm
    rintro ⟨z, hz⟩
    refine ⟨Additive.toMul z, ?_⟩
    rw [← prod_localUnitsEquiv_eq_infinite (K := K) (N := N) w v (Additive.toMul z)]
    apply Additive.ofMul.injective
    rw [← localUnitsRep_norm_apply (K := K) (N := N) (Place.ofInfinite w) (Additive.toMul z)]
    change (Rep.Hom.hom (Rep.norm (NK.HassePrinciple.localUnitsRep K N
        (Place.ofInfinite w)))).toLinearMap z = Additive.ofMul u
    exact hz
  · -- conversely the completion of a local norm is a `Γ_w`-norm
    rintro ⟨y, rfl⟩
    refine ⟨Additive.ofMul y, ?_⟩
    rw [localUnitsRep_norm_apply (K := K) (N := N) (Place.ofInfinite w) y,
      prod_localUnitsEquiv_eq_infinite (K := K) (N := N) w v y]

end NK.CFTLib.Existence
