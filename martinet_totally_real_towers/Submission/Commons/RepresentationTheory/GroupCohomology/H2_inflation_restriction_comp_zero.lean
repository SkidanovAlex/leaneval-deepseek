import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# The composite `res ∘ inf` in degree two is zero

For a normal subgroup `S ◁ G` and a `ℤ`-linear representation `A` of `G`, the composite of the
inflation map `H²(G ⧸ S, A^S) ⟶ H²(G, A)` with the restriction map `H²(G, A) ⟶ H²(S, A)` is
zero.  This is the exactness of the five-term inflation–restriction sequence at `H²(G, A)`
(Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Chapter XII, in the proof of (12.2.1)).

The composite is the map induced on `H²` by the *trivial* group homomorphism `S →* G ⧸ S` composed
with the morphism of `S`-representations `A^S ⟶ A`; every map induced by a trivial group
homomorphism is zero in degree two, because the image of a `2`-cocycle is a constant `2`-cocycle
which is the coboundary of the corresponding constant `1`-cochain.
-/

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory Representation groupCohomology Rep

universe u

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

/-- The `2`-cochain map attached to a trivial group homomorphism sends every `2`-cochain to the
constant `2`-cochain with value the image of the value at `(1, 1)`. -/
lemma cochainsMap₂_trivial_hom_apply {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (φ : res (1 : G →* H) A ⟶ B) (x : H × H → A) (p : G × G) :
    cochainsMap₂ (1 : G →* H) φ x p = φ.hom (x (1, 1)) := by
  simp [cochainsMap₂, Prod.map]

/-- A representation morphism out of the restriction along a trivial homomorphism is invariant
under the whole group. -/
lemma rho_trivial_hom_apply {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (φ : res (1 : G →* H) A ⟶ B) (g : G) (a : A) : B.ρ g (φ.hom a) = φ.hom a := by
  rw [← hom_comm_apply φ g a]
  congr 1
  simp

/-- **The map induced on `H²` by a trivial group homomorphism is zero.**  The image of a
`2`-cocycle `x` is the constant `2`-cocycle with value `φ (x (1,1))`, which is the coboundary of
the constant `1`-cochain with the same value. -/
lemma map_two_eq_zero_of_hom_eq_one {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (φ : res (1 : G →* H) A ⟶ B) : map (1 : G →* H) φ 2 = 0 := by
  have key : mapCocycles₂ (1 : G →* H) φ ≫ H2π B = 0 := by
    ext x
    change H2π B (mapCocycles₂ (1 : G →* H) φ x) = 0
    rw [H2π_eq_zero_iff]
    rw [coe_mapCocycles₂]
    refine ⟨fun _ => φ.hom (x (1, 1)), ?_⟩
    funext p
    rw [d₁₂_hom_apply, cochainsMap₂_trivial_hom_apply, rho_trivial_hom_apply]
    simp
  rw [← cancel_epi (H2π A), H2π_comp_map, CategoryTheory.Limits.comp_zero, key]

set_option backward.isDefEq.respectTransparency false in
/-- **The inflation–restriction composite vanishes in degree two**, for a general coefficient ring
`k`.  The composite is the map induced by the trivial group homomorphism `S →* G ⧸ S`. -/
lemma inf_comp_res_eq_zero_general (S : Subgroup G) [S.Normal] (A : Rep k G) :
    (infNatTrans k S 2).app A ≫ (resNatTrans k (G := S) (H := G) S.subtype 2).app A = 0 := by
  have hf : (infNatTrans k S 2).app A
      = groupCohomology.map (QuotientGroup.mk' S) (ofHom <| A.ρ.quotientToInvariants_lift S) 2 :=
    rfl
  have hg : (resNatTrans k (G := S) (H := G) S.subtype 2).app A
      = groupCohomology.map S.subtype (𝟙 (res S.subtype A)) 2 := rfl
  rw [hf, hg, ← groupCohomology.map_comp, Category.comp_id,
    groupCohomology.congr (QuotientGroup.mk'_comp_subtype S) (fun f φ => groupCohomology.map f φ 2),
    map_two_eq_zero_of_hom_eq_one]

theorem H2_inflation_restriction_comp_zero {G : Type} [Group G] (S : Subgroup G) [S.Normal]
    (A : Rep ℤ G) :
    CategoryTheory.CategoryStruct.comp
      ((groupCohomology.infNatTrans ℤ S 2).app A)
      ((groupCohomology.resNatTrans ℤ (G := S) (H := G) S.subtype 2).app A) = 0 :=
  inf_comp_res_eq_zero_general S A

end Commons.RepresentationTheory.GroupCohomology
