import Mathlib.FieldTheory.Galois.Basic
import Submission.NK.Reconstruct.GammaSup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The ℓ-part projective system of Shimizu's §4 is a functor: `ellRestrict` is compatible
with composition

This file proves that the transition maps of the projective system whose limit is `Γ_K`
(Shimizu, arXiv:2009.10431, §4; CoNF Ch. X §10.3) are compatible with composition, i.e. that

```
ellRestrict ℓ L M h  ∘  ellRestrict ℓ M N h'  =  ellRestrict ℓ L N (h.trans h')
```

for intermediate levels `L ⊆ M ⊆ N` of `K'/K`.  Equivalently: the finite ℓ-parts
`Γ_{L,ℓ} = ℓ-part(Gal(L/K)^{ab})` together with the restriction maps `ellRestrict` form a
(bona fide) projective system, so that `Γ_K = lim_L Γ_{L,ℓ}` as defined in
`NK.Reconstruct.GammaSubgroup` really is the limit of a well-defined diagram, and every general
statement about limits (uniqueness of the comparison maps, naturality of a family of coherent
maps) applies to it.

The proof descends the three layers of the definition:

* **(level restriction, group level)** `NK.Reconstruct.levelRestrictHom_comp`:
  `levelRestrictHom L M h ∘ levelRestrictHom M N h' = levelRestrictHom L N (h.trans h')`.
  Since `levelRestrictHom L M h` is the composite of the restriction
  `AlgEquiv.restrictNormalHom (levelTo L M h)` with the conjugation by `levelToEquiv L M h` that
  identifies the level `L ⊆ M` with `L` itself, this is the compatibility of "restricting an
  automorphism of `N` first to `M` and then to `L`" with "restricting directly to `L`".  The key
  computation `NK.Reconstruct.levelRestrictHom_apply_coe` is that the value of
  `levelRestrictHom L M h σ` at `y ∈ L` is, in the ambient field, simply `σ` applied to `y`:
  this is `AlgEquiv.restrictNormal_commutes` together with the fact that the identifications
  `levelToEquiv` do not move the ambient element (`levelToEquiv_apply_coe`,
  `levelToEquiv_symm_apply_coe`).  The composition then follows by evaluating at `y ∈ L`: both
  sides are `σ` applied to the element of `N.L` lying over `y`.
* **(abelianisation)** `levelRestrict_comp`, by the functoriality of `Abelianization.map`
  (`Abelianization.map_comp`).
* **(ℓ-primary parts)** the target lemma `ellRestrict_comp`, by restricting to the subgroup of
  ℓ-primary elements (`ellRestrict_coe`) and applying `levelRestrict_comp`.
-/

namespace NK.Reconstruct

open scoped Pointwise

section LevelToEquiv

variable {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K']

/-- The identification `levelToEquiv L M h : ↥(levelTo L M h) ≃ₐ[K] ↥L.L` of the level `L ⊆ M`
with `L` itself does not move the ambient element. -/
theorem levelToEquiv_apply_coe (L M : FrobLevel K K') (h : L.L ≤ M.L)
    (x : ↥(levelTo L M h)) :
    ((levelToEquiv L M h x : ↥L.L) : K') = ((x : ↥M.L) : K') := rfl

/-- The inverse of `levelToEquiv L M h` reads off the ambient element: the preimage of `y ∈ L` is
the element `y` of `M` (together with the proof that it lies in the level). -/
theorem levelToEquiv_symm_apply_coe (L M : FrobLevel K K') (h : L.L ≤ M.L) (y : ↥L.L) :
    ((levelToEquiv L M h).symm y : ↥M.L) = ⟨(y : K'), h y.2⟩ := rfl

end LevelToEquiv

section Transition

variable {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K']

/-- **The value of a restriction map**: restricting an automorphism `σ` of `M/K` to the level `L`
and evaluating at `y ∈ L` is the same as evaluating `σ` at the element of `M` lying over `y`, read
off in the ambient field `K'`.

(There are two invisible identifications here: the restriction lands in the level `L` viewed inside
`M` — this is where normality of `L/K` is used — which is then identified with `L` by
`levelToEquiv L M h`; both preserve the ambient element.) -/
theorem levelRestrictHom_apply_coe (L M : FrobLevel K K') (h : L.L ≤ M.L)
    (σ : Gal(↥M.L/K)) (y : ↥L.L) :
    ((levelRestrictHom L M h σ y : ↥L.L) : K') = ((σ ⟨(y : K'), h y.2⟩ : ↥M.L) : K') := by
  rw [levelRestrictHom, algEquivConjHom, MonoidHom.comp_apply]
  have : Normal K ↥(levelTo L M h) := normal_levelTo L M h
  show ((levelToEquiv L M h) ((AlgEquiv.restrictNormalHom (levelTo L M h) σ)
        ((levelToEquiv L M h).symm y)) : K') = ((σ ⟨(y : K'), h y.2⟩ : ↥M.L) : K')
  rw [levelToEquiv_apply_coe, AlgEquiv.restrictNormalHom_apply, levelToEquiv_symm_apply_coe]

/-- **The transition maps of the group-level projective system are compatible with composition**:
restricting from `N` to `L` directly is the same as restricting first to `M` and then to `L`. -/
theorem levelRestrictHom_comp (L M N : FrobLevel K K') (h : L.L ≤ M.L) (h' : M.L ≤ N.L) :
    (levelRestrictHom L M h).comp (levelRestrictHom M N h') =
      levelRestrictHom L N (h.trans h') := by
  ext σ y
  rw [MonoidHom.comp_apply, levelRestrictHom_apply_coe, levelRestrictHom_apply_coe,
    levelRestrictHom_apply_coe]

/-- **The transition maps on the abelianisations are compatible with composition**, by
functoriality of the abelianisation. -/
theorem levelRestrict_comp (L M N : FrobLevel K K') (h : L.L ≤ M.L) (h' : M.L ≤ N.L) :
    (levelRestrict L M h).comp (levelRestrict M N h') = levelRestrict L N (h.trans h') := by
  rw [levelRestrict, levelRestrict, levelRestrict,
    Abelianization.map_comp (f := levelRestrictHom M N h') (g := levelRestrictHom L M h),
    levelRestrictHom_comp]

end Transition

/-- **The transition maps of the projective system of ℓ-parts are compatible with composition**:
`ellRestrict ℓ L M h ∘ ellRestrict ℓ M N h' = ellRestrict ℓ L N (h.trans h')` for intermediate
levels `L ⊆ M ⊆ N` of `K'/K`.  This is the functoriality of Shimizu's projective system
`(Γ_{L,ℓ})_L` whose limit is `Γ_K`. -/
theorem ellRestrict_comp {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K']
    [IsGalois K K'] (ℓ : ℕ) {L M N : FrobLevel K K'} (h : L.L ≤ M.L) (h' : M.L ≤ N.L) :
    (ellRestrict ℓ L M h).comp (ellRestrict ℓ M N h') = ellRestrict ℓ L N (h.trans h') := by
  ext x
  rw [MonoidHom.comp_apply, ellRestrict_coe, ellRestrict_coe, ellRestrict_coe]
  exact congrArg (fun (g : LevelAbelianization N.L →* LevelAbelianization L.L) =>
    g (x : LevelAbelianization N.L)) (levelRestrict_comp L M N h h')

end NK.Reconstruct
