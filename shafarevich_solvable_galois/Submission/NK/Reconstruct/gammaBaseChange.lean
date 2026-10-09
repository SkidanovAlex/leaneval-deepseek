import Mathlib
import Submission.NK.Reconstruct.baseChange
import Submission.NK.Reconstruct.GammaSup
import Submission.NK.Reconstruct.ellIncl_ellRestrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The base-change map `π_{L/K} : Γ_L → Γ_K` and the construction of `Γ_K`'s limit maps

This file proves `NK.Reconstruct.gammaBaseChange`: for a finite Galois level `L` of `K'/K` there is
a *continuous* group homomorphism

  `π_{L/K} : Γ_L → Γ_K`

between Shimizu's ℓ-adic abelianisations (`NK.Reconstruct.Gamma`), uniquely characterised by the
projection formula

  `(π_{L/K} f)_N = π_{N ⊔ L / N,ℓ} (ι_{N ⊔ L / L} (f_{N ⊔ L / L}))`

for every level `N` of `K'/K`: project `f` to the compositum `N ⊔ L` viewed over `L`, apply the level
inclusion `ellIncl` (forget the `L`-structure), and restrict back to `N` (`ellRestrict`).

## The two ingredients

The only non-formal input is the **naturality square** relating the inclusion of the two projective
systems (levels over `K` and levels over `L`) to the transition maps:

* `gammaBaseChange_levelInclHom_comp` — the group-level identity
  `res_{A/B} ∘ incl_{B/L} = incl_{A/L} ∘ res_{B/L}` for `L ≤ A ≤ B`, where `incl` forgets the
  `L`-structure and `res` restricts inside the level.  Its proof is a computation with the explicit
  identification `levelToEquiv` of `GammaObject.lean` (both sides evaluate at `y ∈ A` to `g` applied
  to the element of `B` over `y`);
* `gammaBaseChange_ellIncl_comp` — its descent to the ℓ-primary parts, obtained from the
  functoriality of the abelianisation (`Abelianization.map_comp`).

With the naturality square, the projection formula is *forced*: given two levels `N₁ ≤ N₂`, the
composita `Aᵢ = Nᵢ ⊔ L` satisfy `A₁ ≤ A₂`, and both the restriction
`π_{N₁/N₂} ∘ π_{N₂/A₂}` and the target expression unwind, through the naturality square and the
coherence of `f ∈ Γ_L`, to the same element `ι_{A₁/L}(f_{A₁/L})` (`gammaBaseChange_compatible`).
Hence the projections define an element of the limit `Γ_K` (`gammaBaseChangeHom`), which is
continuous because the topology of `Γ_K` is the initial one for the projections
(`gammaBaseChange_continuous`).

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3 and Ch. XII;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.Reconstruct

open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K']

/-! ## The naturality square -/

/-- **The naturality square at the group level.**  For finite Galois levels `L ≤ A ≤ B` of `K'/K`,
restricting an automorphism of the (`L`-relative) level `B` to `A` is the same as restricting it
inside the level `B` and then forgetting the `L`-structure:

`res_{A/B} ∘ incl_{B/L} = incl_{A/L} ∘ res_{(B/L)/(A/L)}`.

Both sides send `g` to the automorphism of `A/K` given by `y ↦ g(ỹ)` (`ỹ` the element of `B` over
`y`); the content is that the identifications `levelToEquiv` of `GammaObject.lean` and the
forgetful maps do not move the ambient element. -/
theorem gammaBaseChange_levelInclHom_comp (L A B : FrobLevel K K') (hA : L.L ≤ A.L)
    (hAB : A.L ≤ B.L) :
    ((levelRestrictHom A B hAB).comp (levelInclHom L B (hA.trans hAB)) :
      Gal(↥(levelExtend L B (hA.trans hAB)).L/↥L.L) →* Gal(↥A.L/K))
      = ((levelInclHom L A hA).comp
        (levelRestrictHom (levelExtend L A hA) (levelExtend L B (hA.trans hAB))
          (levelExtend_mono L A B hA (hA.trans hAB) hAB)) :
        Gal(↥(levelExtend L B (hA.trans hAB)).L/↥L.L) →* Gal(↥A.L/K)) := by
  ext g x
  simp only [MonoidHom.comp_apply, levelRestrictHom_apply_coe, levelInclHom_apply_coe]

/-- **The naturality square for the ℓ-primary parts** (`NK.Reconstruct.ellIncl_ellRestrict`,
proved here in the form needed below): the level inclusions `Γ_{M,ℓ}(L) → Γ_{M,ℓ}(K)` commute with
the transition maps `ellRestrict` of the two projective systems (levels over `K` and over `L`).  It
is obtained from the group-level identity by functoriality of the abelianisation. -/
theorem gammaBaseChange_ellIncl_comp (ℓ : ℕ) (L A B : FrobLevel K K') (hA : L.L ≤ A.L)
    (hAB : A.L ≤ B.L) :
    ((ellRestrict ℓ A B hAB).comp (ellIncl ℓ L B (hA.trans hAB)) :
      LevelEllPart (K := ↥L.L) (K' := K') (levelExtend L B (hA.trans hAB)).L ℓ →*
        LevelEllPart (K := K) (K' := K') A.L ℓ)
      = ((ellIncl ℓ L A hA).comp
        (ellRestrict ℓ (levelExtend L A hA) (levelExtend L B (hA.trans hAB))
          (levelExtend_mono L A B hA (hA.trans hAB) hAB)) :
        LevelEllPart (K := ↥L.L) (K' := K') (levelExtend L B (hA.trans hAB)).L ℓ →*
          LevelEllPart (K := K) (K' := K') A.L ℓ) := by
  ext x
  simp only [MonoidHom.comp_apply, ellRestrict_coe, ellIncl_coe, levelRestrict]
  show ((Abelianization.map (levelRestrictHom A B hAB)).comp
        (Abelianization.map (levelInclHom L B (hA.trans hAB)))) x.1
      = ((Abelianization.map (levelInclHom L A hA)).comp
        (Abelianization.map (levelRestrictHom (levelExtend L A hA) (levelExtend L B (hA.trans hAB))
          (levelExtend_mono L A B hA (hA.trans hAB) hAB)))) x.1
  rw [DFunLike.congr_fun (Abelianization.map_comp (levelInclHom L B (hA.trans hAB))
        (levelRestrictHom A B hAB)) x.1,
      DFunLike.congr_fun (Abelianization.map_comp
        (levelRestrictHom (levelExtend L A hA) (levelExtend L B (hA.trans hAB))
          (levelExtend_mono L A B hA (hA.trans hAB) hAB))
        (levelInclHom L A hA)) x.1,
      congrArg Abelianization.map (gammaBaseChange_levelInclHom_comp L A B hA hAB)]

/-! ## The projections of the base-change map are compatible -/

/-- **The projections of the base-change map form a compatible family.**  For `N₁ ≤ N₂` the two
composita `Aᵢ = Nᵢ ⊔ L` satisfy `A₁ ≤ A₂`, and the composite

`Γ_{N₂ ⊔ L,ℓ}(L) → Γ_{N₂,ℓ}(K) → Γ_{N₁,ℓ}(K)`

(include and restrict) unwinds — using the naturality square
(`gammaBaseChange_ellIncl_comp`) and the coherence of `f ∈ Γ_L`
(`Gamma.proj_compatible`) — to `Γ_{N₁ ⊔ L,ℓ}(L) → Γ_{N₁,ℓ}(K)`, i.e. to the projection at `N₁`. -/
theorem gammaBaseChange_compatible (ℓ : ℕ) (L : FrobLevel K K') (f : Gamma ↥L.L K' ℓ) :
    Compatible ℓ (fun N : FrobLevel K K' =>
      ellRestrict ℓ N (L.sup N) (FrobLevel.le_sup_right L N)
        (ellIncl ℓ L (L.sup N) (FrobLevel.le_sup_left L N)
          (Gamma.proj (levelExtend L (L.sup N) (FrobLevel.le_sup_left L N)) f))) := by
  intro N₁ N₂ h
  have h12 : (L.sup N₁).L ≤ (L.sup N₂).L :=
    FrobLevel.sup_le (L := L) (M := N₁) (N := L.sup N₂)
      (FrobLevel.le_sup_left L N₂) (h.trans (FrobLevel.le_sup_right L N₂))
  have e₁ : ellRestrict ℓ N₁ N₂ h
        (ellRestrict ℓ N₂ (L.sup N₂) (FrobLevel.le_sup_right L N₂)
          (ellIncl ℓ L (L.sup N₂) (FrobLevel.le_sup_left L N₂)
            (Gamma.proj (levelExtend L (L.sup N₂) (FrobLevel.le_sup_left L N₂)) f)))
      = ellRestrict ℓ N₁ (L.sup N₂) (h.trans (FrobLevel.le_sup_right L N₂))
          (ellIncl ℓ L (L.sup N₂) (FrobLevel.le_sup_left L N₂)
            (Gamma.proj (levelExtend L (L.sup N₂) (FrobLevel.le_sup_left L N₂)) f)) :=
    DFunLike.congr_fun (ellRestrict_comp (K := K) (K' := K') ℓ (L := N₁) (M := N₂)
      (N := L.sup N₂) h (FrobLevel.le_sup_right L N₂)) _
  have e₂ : ellRestrict ℓ N₁ (L.sup N₂) (h.trans (FrobLevel.le_sup_right L N₂))
        (ellIncl ℓ L (L.sup N₂) (FrobLevel.le_sup_left L N₂)
          (Gamma.proj (levelExtend L (L.sup N₂) (FrobLevel.le_sup_left L N₂)) f))
      = ellRestrict ℓ N₁ (L.sup N₁) (FrobLevel.le_sup_right L N₁)
          (ellRestrict ℓ (L.sup N₁) (L.sup N₂) h12
            (ellIncl ℓ L (L.sup N₂) (FrobLevel.le_sup_left L N₂)
              (Gamma.proj (levelExtend L (L.sup N₂) (FrobLevel.le_sup_left L N₂)) f))) :=
    (DFunLike.congr_fun (ellRestrict_comp (K := K) (K' := K') ℓ (L := N₁) (M := L.sup N₁)
      (N := L.sup N₂) (FrobLevel.le_sup_right L N₁) h12) _).symm
  have e₃ : ellRestrict ℓ (L.sup N₁) (L.sup N₂) h12
        (ellIncl ℓ L (L.sup N₂) (FrobLevel.le_sup_left L N₂)
          (Gamma.proj (levelExtend L (L.sup N₂) (FrobLevel.le_sup_left L N₂)) f))
      = ellIncl ℓ L (L.sup N₁) (FrobLevel.le_sup_left L N₁)
          (ellRestrict ℓ (levelExtend L (L.sup N₁) (FrobLevel.le_sup_left L N₁))
            (levelExtend L (L.sup N₂) ((FrobLevel.le_sup_left L N₁).trans h12))
            (levelExtend_mono L (L.sup N₁) (L.sup N₂) (FrobLevel.le_sup_left L N₁)
              ((FrobLevel.le_sup_left L N₁).trans h12) h12)
            (Gamma.proj (levelExtend L (L.sup N₂) (FrobLevel.le_sup_left L N₂)) f)) :=
    DFunLike.congr_fun (gammaBaseChange_ellIncl_comp ℓ L (L.sup N₁) (L.sup N₂)
      (FrobLevel.le_sup_left L N₁) h12) _
  have e₄ : ellRestrict ℓ (levelExtend L (L.sup N₁) (FrobLevel.le_sup_left L N₁))
        (levelExtend L (L.sup N₂) ((FrobLevel.le_sup_left L N₁).trans h12))
        (levelExtend_mono L (L.sup N₁) (L.sup N₂) (FrobLevel.le_sup_left L N₁)
          ((FrobLevel.le_sup_left L N₁).trans h12) h12)
        (Gamma.proj (levelExtend L (L.sup N₂) (FrobLevel.le_sup_left L N₂)) f)
      = Gamma.proj (levelExtend L (L.sup N₁) (FrobLevel.le_sup_left L N₁)) f :=
    Gamma.proj_compatible (levelExtend L (L.sup N₁) (FrobLevel.le_sup_left L N₁))
      (levelExtend L (L.sup N₂) ((FrobLevel.le_sup_left L N₁).trans h12))
      (levelExtend_mono L (L.sup N₁) (L.sup N₂) (FrobLevel.le_sup_left L N₁)
        ((FrobLevel.le_sup_left L N₁).trans h12) h12) f
  rw [e₁, e₂, e₃, e₄]

/-! ## The base-change map and its continuity -/

/-- **The base-change map `π_{L/K} : Γ_L → Γ_K`** (Shimizu, §4): the map whose projection to the
level `N` of `K'/K` is inclusion into the compositum `N ⊔ L` followed by restriction.  It exists by
`gammaBaseChange_compatible` and is a group homomorphism because every projection is. -/
noncomputable def gammaBaseChangeHom (ℓ : ℕ) (L : FrobLevel K K') :
    Gamma ↥L.L K' ℓ →* Gamma K K' ℓ where
  toFun f := Gamma.mk (fun N => ellRestrict ℓ N (L.sup N) (FrobLevel.le_sup_right L N)
      (ellIncl ℓ L (L.sup N) (FrobLevel.le_sup_left L N)
        (Gamma.proj (levelExtend L (L.sup N) (FrobLevel.le_sup_left L N)) f)))
    (gammaBaseChange_compatible ℓ L f)
  map_one' := by
    refine Gamma.ext (fun N => ?_)
    simp only [Gamma.proj_mk, map_one]
  map_mul' f g := by
    refine Gamma.ext (fun N => ?_)
    simp only [Gamma.proj_mk, map_mul]

/-- **`π_{L/K}` is continuous**: `Γ_K` carries the topology induced by its projections onto the
(finite, discrete) levels, and so does `Γ_L`; the projection of `π_{L/K}` to a level is a composite
of continuous maps (`ellIncl` and `ellRestrict` have discrete domains). -/
theorem gammaBaseChange_continuous (ℓ : ℕ) (L : FrobLevel K K') :
    Continuous ⇑(gammaBaseChangeHom ℓ L) := by
  show Continuous fun f : Gamma ↥L.L K' ℓ =>
    (⟨fun N => ellRestrict ℓ N (L.sup N) (FrobLevel.le_sup_right L N)
        (ellIncl ℓ L (L.sup N) (FrobLevel.le_sup_left L N)
          (Gamma.proj (levelExtend L (L.sup N) (FrobLevel.le_sup_left L N)) f)),
      gammaBaseChange_compatible ℓ L f⟩ : Gamma K K' ℓ)
  refine Continuous.subtype_mk ?_ ?_
  · rw [continuous_pi_iff]
    intro N
    exact (continuous_of_discreteTopology.comp (continuous_of_discreteTopology.comp
      (continuous_proj ℓ (levelExtend L (L.sup N) (FrobLevel.le_sup_left L N)))))

/-! ## The base-change map -/

/-- The base-change map `π_{L/K} : Γ_L → Γ_K` of Shimizu's §4: the map induced on the torsion-free
ℓ-adic abelianisations by the inclusion `G_L ⊆ G_K`.  It is the unique continuous homomorphism whose
projection to the level `N` of `K'/K` is obtained by passing to the compositum `N ⊔ L`, applying the
level inclusion `ellIncl` and restricting back. -/
theorem gammaBaseChange {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] (L : FrobLevel K K') :
    ∃ π : Gamma ↥L.L K' ℓ →* Gamma K K' ℓ, Continuous ⇑π ∧
      ∀ (f : Gamma ↥L.L K' ℓ) (N : FrobLevel K K'),
        Gamma.proj N (π f) = ellRestrict ℓ N (L.sup N) (FrobLevel.le_sup_right L N)
          (ellIncl ℓ L (L.sup N) (FrobLevel.le_sup_left L N)
            (Gamma.proj (levelExtend L (L.sup N) (FrobLevel.le_sup_left L N)) f)) :=
  ⟨gammaBaseChangeHom ℓ L, gammaBaseChange_continuous ℓ L, fun f N => rfl⟩

end NK.Reconstruct
