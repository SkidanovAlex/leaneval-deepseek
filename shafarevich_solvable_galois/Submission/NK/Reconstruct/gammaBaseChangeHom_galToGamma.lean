import Mathlib
import Submission.NK.Reconstruct.galToGamma
import Submission.NK.Reconstruct.gammaBaseChange
import Submission.NK.Reconstruct.GammaObject
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of `galToGamma` with respect to the base-change map `π_{L/K}`

`NK.Reconstruct.galToGamma ℓ : Gal(K'/K) →* Γ_K` sends an automorphism of `K'` over `K` to the
coherent family of the ℓ-primary components of its restrictions to the finite levels of `K'/K`
(`Submission/Work/Reconstruct/galToGamma.lean`), and `NK.Reconstruct.gammaBaseChangeHom ℓ L`
is Shimizu's base-change map `π_{L/K} : Γ_L → Γ_K`
(`Submission/Work/Reconstruct/gammaBaseChange.lean`).

Both are models of the same construction: the ℓ-adic abelianisation of an absolute Galois group,
functorially in the base field.  This file proves that they agree, i.e. that the square

```
   Gal(K'/L)  --galToGamma-->  Γ_L
       |                          |
   restrictScalars K           π_{L/K}
       v                          v
   Gal(K'/K)  --galToGamma-->  Γ_K
```

commutes: `galToGamma` is compatible with the change of base field `K ⊆ L`.

## Contents

* `aux_ellIncl_ellComp` — the level inclusion `ellIncl` intertwines the ℓ-primary projection
  `ellComp` with `Abelianization.map`;
* `aux_group` — the group-level identity
  `levelInclHom L A h (σ|_A) = (σ.restrictScalars K)|_A` for a level `A` of `K'/K` containing `L`;
* `aux_key` — the resulting identity
  `ellIncl ℓ L A h (levelComponent_{L} σ) = levelComponent_{K} (σ.restrictScalars K)`;
* `gammaBaseChangeHom_galToGamma` — the naturality square above.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3 and Ch. XII;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']

/-- **The level inclusion `ellIncl` intertwines `ellComp` with `Abelianization.map`**: the ℓ-primary
component of the image of `y` under `levelInclHom` is the image of the ℓ-primary component of `y`.
Both sides are ℓ-coprime-related to `Abelianization.map (levelInclHom L A h) y`, so they agree by
uniqueness of the ℓ-primary component. -/
private theorem aux_ellIncl_ellComp [IsGalois K K'] (ℓ : ℕ) (L A : FrobLevel K K')
    (h : L.L ≤ A.L) (y : LevelAbelianization (levelExtend L A h).L) :
    ellIncl ℓ L A h (ellComp ℓ y) = ellComp ℓ (Abelianization.map (levelInclHom L A h) y) := by
  refine eq_ellComp_of_ellCoprimeRel ?_
  rw [ellIncl_coe]
  exact ellCoprimeRel_map (Abelianization.map (levelInclHom L A h)) (ellCoprimeRel_ellComp ℓ y)

/-- **The group-level identity**: for a level `A` of `K'/K` containing `L`, the automorphism `σ` of
`K'/L` restricted to `A` and then viewed over `K` is the restriction to `A` of `σ` viewed over
`K`.  Both act on `A ⊆ K'` by `σ`, so the two automorphisms of `A/K` agree. -/
private theorem aux_group [IsSepClosure K K'] (L A : FrobLevel K K') (h : L.L ≤ A.L)
    (σ : Gal(K'/↥L.L)) :
    levelInclHom L A h (AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := K') (levelExtend L A h).L σ)
      = AlgEquiv.restrictNormalHom (F := K) (K₁ := K') A.L (σ.restrictScalars K) := by
  ext x
  rw [AlgEquiv.restrictNormalHom_apply]
  exact AlgEquiv.restrictNormalHom_apply (F := ↥L.L) (K₁ := K') (levelExtend L A h).L σ x

/-- **The compatibility of the ℓ-primary components with the level inclusion**: for a level `A` of
`K'/K` containing `L`, the image under `ellIncl` of the ℓ-primary component of `σ ∈ Gal(K'/L)` at
the level `A/L` is the ℓ-primary component of `σ.restrictScalars K` at the level `A/K`. -/
private theorem aux_key [IsSepClosure K K'] (ℓ : ℕ) (L A : FrobLevel K K') (h : L.L ≤ A.L)
    (σ : Gal(K'/↥L.L)) :
    ellIncl ℓ L A h (levelComponent (K := ↥L.L) (K' := K') ℓ (levelExtend L A h) σ)
      = levelComponent (K := K) (K' := K') ℓ A (σ.restrictScalars K) := by
  rw [levelComponent, levelComponent, aux_ellIncl_ellComp, Abelianization.map_of, aux_group]

/-- **`galToGamma` is compatible with the base change `K ⊆ L`**: the naturality square

```
   Gal(K'/L)  --galToGamma-->  Γ_L
       |                          |
   restrictScalars K           π_{L/K}
       v                          v
   Gal(K'/K)  --galToGamma-->  Γ_K
```

commutes.  Both composites are compared through their projections to the levels `N` of `K'/K`
(`NK.Reconstruct.Gamma.ext`): the projection of `π_{L/K}(galToGamma σ)` at `N` is obtained by
passing to the compositum `N ⊔ L`, which is exactly where `aux_key` compares the two ℓ-primary
components, and the coherence of `Γ_K` (`NK.Reconstruct.Gamma.proj_compatible`) then identifies
the result with the projection of `galToGamma (σ.restrictScalars K)`. -/
theorem gammaBaseChangeHom_galToGamma {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) (L : FrobLevel K K')
    (σ : Gal(K'/↥L.L)) :
    gammaBaseChangeHom (K := K) (K' := K') ℓ L (galToGamma (K := ↥L.L) (K' := K') ℓ σ)
      = galToGamma (K := K) (K' := K') ℓ (σ.restrictScalars K) := by
  refine Gamma.ext (fun N => ?_)
  rw [galToGamma_proj]
  rw [show Gamma.proj N (gammaBaseChangeHom (K := K) (K' := K') ℓ L
        (galToGamma (K := ↥L.L) (K' := K') ℓ σ))
      = ellRestrict ℓ N (L.sup N) (FrobLevel.le_sup_right L N)
          (ellIncl ℓ L (L.sup N) (FrobLevel.le_sup_left L N)
            (Gamma.proj (levelExtend L (L.sup N) (FrobLevel.le_sup_left L N))
              (galToGamma (K := ↥L.L) (K' := K') ℓ σ))) from rfl]
  rw [galToGamma_proj]
  rw [aux_key]
  rw [← galToGamma_proj (K := K) (K' := K') ℓ (L.sup N) (σ.restrictScalars K)]
  exact Gamma.proj_compatible N (L.sup N) (FrobLevel.le_sup_right L N)
    (galToGamma (K := K) (K' := K') ℓ (σ.restrictScalars K))

end NK.Reconstruct
