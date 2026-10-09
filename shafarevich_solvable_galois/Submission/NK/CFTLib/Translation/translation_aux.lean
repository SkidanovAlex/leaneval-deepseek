import Mathlib
import Submission.NK.Cohomology.capture_two_map_eq_zero_of_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.Translation

open CategoryTheory Representation groupCohomology Rep
open Pointwise

-- Prefer the `Module`/`AddCommGroup` structures coming from a representation over the generic
-- `ℤ`-module structure, so that the `Rep ℤ G`-diamonds do not produce `isDefEq` failures.
attribute [local instance 5000] Rep.hV1 Rep.hV2
attribute [local instance 100] AddCommGroup.toIntModule

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## The coefficient morphism of a pair of complementary normal subgroups

For `M, N ◁ G`, the `N`-representation `A^M` (the `M`-invariants of a `G`-representation `A`) is
`N`-stable (because `M` is normal), and the inclusion of the invariants is a morphism of
`N`-representations `A^M ⟶ A`.  Under the identification `N ≅ G ⧸ M` this is the "coefficient
morphism" through which the composite `res_N ∘ inf_M` factors. -/

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of the `M`-invariants of `A` into `A`, viewed as a morphism of
`N`-representations (using that `A^M` is `N`-stable because `M` is normal). -/
noncomputable def coeffMor {k : Type} [CommRing k] {G : Type} [Group G] (M N : Subgroup G)
    [M.Normal] [N.Normal] (A : Rep k G) :
    (Rep.resFunctor N.subtype).obj
        ((Rep.resFunctor (QuotientGroup.mk' M)).obj (A.quotientToInvariants M)) ⟶
      (Rep.resFunctor N.subtype).obj A :=
  (Rep.resFunctor N.subtype).map
      (ofHom (A.ρ.quotientToInvariants_lift M)) ≫
    𝟙 (Rep.res N.subtype A)

set_option backward.isDefEq.respectTransparency false in
/-- The underlying linear map of the coefficient morphism is the inclusion of the invariants. -/
theorem coe_coeffMor {k : Type} [CommRing k] {G : Type} [Group G] (M N : Subgroup G)
    [M.Normal] [N.Normal] (A : Rep k G) :
    (coeffMor M N A).hom.toLinearMap = Submodule.subtype _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `ℤ`-specialisation of `coeffMor`, defined in the `ℤ`-context (the `Rep ℤ`-instances of the
type are the ones used in the main statement below). -/
noncomputable def coeffMorZ {G : Type} [Group G] (M N : Subgroup G) [M.Normal] [N.Normal]
    (A : Rep ℤ G) :
    (Rep.resFunctor N.subtype).obj
        ((Rep.resFunctor (QuotientGroup.mk' M)).obj (A.quotientToInvariants M)) ⟶
      (Rep.resFunctor N.subtype).obj A :=
  (Rep.resFunctor N.subtype).map
      (ofHom (A.ρ.quotientToInvariants_lift M)) ≫
    𝟙 (Rep.res N.subtype A)

set_option backward.isDefEq.respectTransparency false in
/-- The underlying linear map of `coeffMorZ` is the inclusion of the invariants. -/
theorem coe_coeffMorZ {G : Type} [Group G] (M N : Subgroup G) [M.Normal] [N.Normal]
    (A : Rep ℤ G) :
    (coeffMorZ M N A).hom.toLinearMap = Submodule.subtype _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient morphism with the source written as the restriction along the *identity* of
`N` (so that it can be fed to `groupCohomology.map (MonoidHom.id N)`). -/
noncomputable def coeffMorId {G : Type} [Group G] (M N : Subgroup G) [M.Normal] [N.Normal]
    (A : Rep ℤ G) :
    res (MonoidHom.id N)
        ((Rep.resFunctor N.subtype).obj
          ((Rep.resFunctor (QuotientGroup.mk' M)).obj (A.quotientToInvariants M))) ⟶
      (Rep.resFunctor N.subtype).obj A :=
  (Rep.resFunctor (MonoidHom.id N)).map
      ((Rep.resFunctor N.subtype).map (ofHom (A.ρ.quotientToInvariants_lift M))) ≫
    𝟙 (Rep.res (MonoidHom.id N) ((Rep.resFunctor N.subtype).obj A))

set_option backward.isDefEq.respectTransparency false in
/-- `coeffMorId` and `coeffMorZ` have the same underlying linear map. -/
theorem coe_coeffMorId_eq {G : Type} [Group G] (M N : Subgroup G) [M.Normal] [N.Normal]
    (A : Rep ℤ G) :
    (coeffMorId M N A).hom.toLinearMap = (coeffMorZ M N A).hom.toLinearMap := by
  ext x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The underlying linear map of `coeffMorId` is the inclusion of the invariants. -/
theorem coe_coeffMorId {G : Type} [Group G] (M N : Subgroup G) [M.Normal] [N.Normal]
    (A : Rep ℤ G) :
    (coeffMorId M N A).hom.toLinearMap = Submodule.subtype _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The composite `res_N ∘ inf_M` is the map induced by the coefficient morphism.**  With
`j := (QuotientGroup.mk' M).comp N.subtype`, the composite of the inflation along the normal
subgroup `M` with the restriction along the complementary normal subgroup `N` is the map on `H²`
induced by `coeffMor M N A`, transported along `j`.

This is the functoriality `map_comp` of group cohomology: the content is that restriction to the
complementary factor inverts the inflation. -/
theorem inf_comp_res_eq_map_coeff {k : Type} [CommRing k] {G : Type} [Group G]
    (M N : Subgroup G) [M.Normal] [N.Normal] (A : Rep k G) :
    (groupCohomology.infNatTrans k M 2).app A ≫
      (groupCohomology.resNatTrans k (G := N) (H := G) N.subtype 2).app A
    = groupCohomology.map ((QuotientGroup.mk' M).comp N.subtype) (coeffMor M N A) 2 := by
  have h1 : (groupCohomology.infNatTrans k M 2).app A
      = groupCohomology.map (QuotientGroup.mk' M)
          (ofHom (A.ρ.quotientToInvariants_lift M)) 2 := rfl
  have h2 : (groupCohomology.resNatTrans k (G := N) (H := G) N.subtype 2).app A
      = groupCohomology.map N.subtype (𝟙 (Rep.res N.subtype A)) 2 := rfl
  rw [h1, h2, ← groupCohomology.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `ℤ`-form of `inf_comp_res_eq_map_coeff`, with the coefficient morphism written as
`coeffMorZ`. -/
theorem H2_inf_comp_res_eq_map_coeff {G : Type} [Group G] (M N : Subgroup G) [M.Normal] [N.Normal]
    (A : Rep ℤ G) :
    (groupCohomology.infNatTrans ℤ M 2).app A ≫
      (groupCohomology.resNatTrans ℤ (G := N) (H := G) N.subtype 2).app A
    = groupCohomology.map ((QuotientGroup.mk' M).comp N.subtype) (coeffMorZ M N A) 2 :=
  inf_comp_res_eq_map_coeff M N A

set_option backward.isDefEq.respectTransparency false in
/-- **Transport of the coefficient morphism to the identity group homomorphism.**  If `j : N →* Q`
is a group homomorphism, `X` a representation of `Q`, `B` a representation of `N` and
`ψ : res j X ⟶ B` a morphism whose underlying linear map also defines a morphism
`ψ' : res (𝟙 N) (res j X) ⟶ B` of `N`-representations, then
`map j ψ = map j (𝟙 (res j X)) ≫ map (𝟙 N) ψ'`.  This is `map_comp`; the point is that it
isolates the coefficient endomorphism `map (𝟙 N) ψ'` of the *same* group `N`, to which the
cyclic-group vanishing criterion applies. -/
theorem map_eq_comp_of_res_id {k : Type} [CommRing k] {N Q : Type} [Group N] [Group Q]
    (j : N →* Q) (X : Rep k Q) (B : Rep k N) (ψ : res j X ⟶ B)
    (ψ' : res (MonoidHom.id N) (res j X) ⟶ B) (hψ : ψ'.hom.toLinearMap = ψ.hom.toLinearMap) :
    groupCohomology.map j ψ 2 =
      groupCohomology.map j (𝟙 (res j X)) 2 ≫ groupCohomology.map (MonoidHom.id N) ψ' 2 := by
  rw [← groupCohomology.map_comp]
  refine (groupCohomology.map_congr (by ext x; rfl) ?_ 2).symm
  rw [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap]
  have hid : ((resFunctor (MonoidHom.id N)).map (𝟙 (res j X))).hom.toLinearMap = LinearMap.id := by
    ext x
    rfl
  rw [hid, LinearMap.comp_id]
  exact hψ

set_option backward.isDefEq.respectTransparency false in
/-- The transport identity of `map_eq_comp_of_res_id` specialised to the coefficient morphism
`coeffMorZ M N A` and `j := (QuotientGroup.mk' M).comp N.subtype`. -/
theorem coeffMor_transport {G : Type} [Group G] (M N : Subgroup G) [M.Normal] [N.Normal]
    (A : Rep ℤ G) :
    groupCohomology.map ((QuotientGroup.mk' M).comp N.subtype) (coeffMorZ M N A) 2
      = groupCohomology.map ((QuotientGroup.mk' M).comp N.subtype)
          (𝟙 (res ((QuotientGroup.mk' M).comp N.subtype) (A.quotientToInvariants M))) 2
        ≫ groupCohomology.map (MonoidHom.id N) (coeffMorId M N A) 2 :=
  map_eq_comp_of_res_id ((QuotientGroup.mk' M).comp N.subtype)
    (A.quotientToInvariants M) ((Rep.resFunctor N.subtype).obj A)
    (coeffMorZ M N A) (coeffMorId M N A) (by ext x; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- **The coefficient morphism induces the zero map on `H²` of the cyclic group `N`.**  This is the
`H²`-form of the reciprocity input: the coefficient morphism is the inclusion of the invariants
`A^M ⊆ A`, so its source is fixed pointwise by `N` exactly on `A^G = (A^M)^N`, and every such
element is a norm for `N` by hypothesis. -/
theorem capture_coeffMor {G : Type} [Group G] [Fintype G] (M N : Subgroup G) [M.Normal] [N.Normal]
    [IsCyclic N] [Fintype N] (hMN : M ⊔ N = ⊤) (A : Rep ℤ G)
    (hnorm : ∀ a : A.V, (∀ g : G, A.ρ g a = a) →
      ∃ b : A.V, (∑ n : N, A.ρ (n : G) b) = a) :
    groupCohomology.map (MonoidHom.id N) (coeffMorId M N A) 2 = 0 := by
  apply NK.Cohomology.capture_two_map_eq_zero_of_cyclic
  intro a ha
  -- `a` lies in `A^M`; `ha` says that it is also fixed by `N`; hence it is fixed by `G`
  have ha' : ∀ n : N, A.ρ (n : G) (a : A.V) = (a : A.V) := by
    intro n
    have h1 : (((Rep.resFunctor (QuotientGroup.mk' M)).obj
          (A.quotientToInvariants M)).ρ (N.subtype n) a : A.V) = (a : A.V) :=
      congrArg Subtype.val (ha n)
    simpa using h1
  have hfix : ∀ g : G, A.ρ g (a : A.V) = (a : A.V) := by
    intro g
    have hgmem : g ∈ (M : Set G) * (N : Set G) := by
      rw [← Subgroup.mul_normal M N, hMN]
      exact Subgroup.mem_top g
    obtain ⟨m, hm, n, hn, hmn⟩ := Set.mem_mul.mp hgmem
    rw [← hmn, map_mul]
    show A.ρ m (A.ρ n (a : A.V)) = (a : A.V)
    rw [show A.ρ n (a : A.V) = (a : A.V) from ha' ⟨n, hn⟩]
    exact a.2 ⟨m, hm⟩
  obtain ⟨b, hb⟩ := hnorm (a : A.V) hfix
  refine ⟨b, ?_⟩
  show (Rep.norm ((Rep.resFunctor N.subtype).obj A)).hom b = (coeffMorId M N A).hom a
  have hco : (coeffMorId M N A).hom a = (a : A.V) := rfl
  rw [hco, Rep.norm_apply,
    show ((Rep.resFunctor N.subtype).obj A).ρ.norm b
      = ∑ n : N, ((Rep.resFunctor N.subtype).obj A).ρ n b from by
    rw [Representation.norm, LinearMap.sum_apply]]
  exact hb

set_option backward.isDefEq.respectTransparency false in
/-- **The composite `res_N ∘ inf_M` vanishes.**  The composite is the map on `H²` of the cyclic
group `N` induced by the coefficient inclusion `A^M ↪ A` (`H2_inf_comp_res_eq_map_coeff`),
transported to the identity group homomorphism (`coeffMor_transport`), and that map is zero
because every `G`-invariant of `A` is a norm for `N` (`capture_coeffMor`). -/
theorem H2_comp_eq_zero {G : Type} [Group G] [Fintype G] (M N : Subgroup G) [M.Normal] [N.Normal]
    [IsCyclic N] [Fintype N] (hMN : M ⊔ N = ⊤) (A : Rep ℤ G)
    (hnorm : ∀ a : A.V, (∀ g : G, A.ρ g a = a) →
      ∃ b : A.V, (∑ n : N, A.ρ (n : G) b) = a) :
    ((groupCohomology.resNatTrans ℤ (G := N) (H := G) N.subtype 2).app A).hom.comp
      ((groupCohomology.infNatTrans ℤ M 2).app A).hom = 0 := by
  have h : ((groupCohomology.infNatTrans ℤ M 2).app A) ≫
      ((groupCohomology.resNatTrans ℤ (G := N) (H := G) N.subtype 2).app A) = 0 := by
    rw [H2_inf_comp_res_eq_map_coeff M N A, coeffMor_transport M N A,
      capture_coeffMor M N hMN A hnorm, Limits.comp_zero]
  have h2 := congrArg (fun f => f.hom) h
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero] using h2


end NK.CFTLib.Translation
