import Mathlib
import Submission.NK.HassePrinciple.LevelDictionary

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

section Aux

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The range of the quotient lift of a group homomorphism is the range of the homomorphism. -/
lemma range_quotientGroup_lift {G M : Type u} [Group G] [Group M] (N : Subgroup G) [N.Normal]
    (φ : G →* M) (HN : N ≤ φ.ker) :
    (QuotientGroup.lift N φ HN).range = φ.range := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    exact ⟨g, QuotientGroup.lift_mk' N HN g⟩
  · rintro y ⟨g, rfl⟩
    exact ⟨QuotientGroup.mk' N g, QuotientGroup.lift_mk' N HN g⟩

/-- The level group of `W` at the level `L`, mapped into `Gal(L/K)` by restriction: the quotient
lift of `levelRestrictHom W L`. -/
noncomputable def levelAlpha (W : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    LevelGroup W L →* Gal(↥L/K) :=
  QuotientGroup.lift (L.fixingSubgroup.subgroupOf W) (levelRestrictHom W L)
    (le_of_eq (levelRestrictHom_ker W L).symm)

/-- Computation rule for `levelAlpha` on the class of an element of `W`. -/
lemma levelAlpha_coe (W : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (w : ↥W) :
    levelAlpha W L (w : LevelGroup W L) = levelRestrictHom W L w :=
  QuotientGroup.lift_mk' _ _ w

/-- The range of `levelAlpha` is the image of `W` under the restriction map to `L`. -/
lemma levelAlpha_range (W : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    (levelAlpha W L).range = W.map (levelRestrict L) := by
  unfold levelAlpha
  rw [range_quotientGroup_lift, levelRestrictHom_range]

/-- `levelAlpha` is injective. -/
lemma levelAlpha_injective (W : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    Function.Injective (levelAlpha W L) :=
  (QuotientGroup.injective_lift_iff (L.fixingSubgroup.subgroupOf W) (levelRestrictHom W L)
    (le_of_eq (levelRestrictHom_ker W L).symm)).mpr (levelRestrictHom_ker W L).symm

/-- The level group `LevelGroup W L` is the image of `W` in the finite Galois group `Gal(L/K)`. -/
noncomputable def levelEquiv (W : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    LevelGroup W L ≃* ↥(W.map (levelRestrict L)) :=
  MulEquiv.ofBijective
    ((levelAlpha W L).codRestrict (W.map (levelRestrict L))
      (fun x => by rw [← levelAlpha_range]; exact ⟨x, rfl⟩))
    ⟨fun a b h => levelAlpha_injective W L (congrArg Subtype.val h), fun y => by
      have hy : (y : Gal(↥L/K)) ∈ (levelAlpha W L).range := by
        rw [levelAlpha_range]; exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩

lemma levelEquiv_apply_coe (W : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (x : LevelGroup W L) :
    ((levelEquiv W L x : ↥(W.map (levelRestrict L))) : Gal(↥L/K)) = levelAlpha W L x := rfl

/-- The restriction map `levelAlpha` is compatible with the inclusion of level groups induced by
an inclusion `W' ≤ W`: the obvious square commutes. -/
lemma levelAlpha_levelInclHom {W W' : Subgroup Gal(K'/K)} (h : W' ≤ W)
    (L : FiniteGaloisIntermediateField K K') (x : LevelGroup W' L) :
    levelAlpha W L (levelInclHom h L x) = levelAlpha W' L x := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (L.fixingSubgroup.subgroupOf W') x
  rw [levelInclHom, QuotientGroup.map_mk', levelAlpha_coe, QuotientGroup.mk'_apply,
    levelAlpha_coe]
  show levelRestrict L ↑(Subgroup.inclusion h u) = levelRestrict L ↑u
  rw [Subgroup.coe_inclusion]

end Aux

theorem localInclHom_eq_restriction {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K']
    (V : Subgroup (K' ≃ₐ[K] K')) (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K') :
    ∃ (eL : NK.BrauerHasse.LevelGroup V L ≃* ↥(V.map (NK.HassePrinciple.levelRestrict L)))
      (eA : NK.BrauerHasse.LocalLevelGroup V A L ≃*
        ↥((V ⊓ NK.BrauerHasse.stabSubgroup A).map (NK.HassePrinciple.levelRestrict L))),
      ∀ x : NK.BrauerHasse.LocalLevelGroup V A L,
        eL (NK.BrauerHasse.localInclHom V A L x) =
          Subgroup.inclusion (Subgroup.map_mono inf_le_left) (eA x) := by
  refine ⟨levelEquiv V L, levelEquiv (V ⊓ stabSubgroup A) L, ?_⟩
  intro x
  apply Subtype.ext
  rw [levelEquiv_apply_coe, Subgroup.coe_inclusion, levelEquiv_apply_coe]
  exact levelAlpha_levelInclHom inf_le_left L x

end NK.HassePrinciple
