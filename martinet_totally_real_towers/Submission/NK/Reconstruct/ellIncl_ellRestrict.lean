import Mathlib
import Submission.NK.Reconstruct.baseChange

/-!
# Naturality of the level inclusion `ellIncl` with respect to the transition maps

`NK.Reconstruct.ellIncl ℓ L M h : Γ_{M,ℓ}(L) →* Γ_{M,ℓ}(K)` is the map on the ℓ-primary parts
of the abelianisations induced by the inclusion `Gal(M/L) →* Gal(M/K)`
(`NK.Reconstruct.levelInclHom`) — "forgetting the `L`-structure" of an automorphism of `M`.
`NK.Reconstruct.ellRestrict ℓ L M h` is the transition map of the projective system of ℓ-parts
— "restricting" an automorphism of `M` to the level `L` (`NK.Reconstruct.levelRestrictHom`).

The two constructions live over *different* base fields (`ellRestrict` for levels of `K'/L`,
`ellIncl` for levels of `K'/K`), and the content of this file is that they are compatible: for
finite Galois levels `L ≤ A ≤ B` of `K'/K` the square

```
  ℓ-part(Gal(B/L)^{ab}) --ellIncl--> ℓ-part(Gal(B/K)^{ab})
          |                                  |
   ellRestrict                        ellRestrict
          v                                  v
  ℓ-part(Gal(A/L)^{ab}) --ellIncl--> ℓ-part(Gal(A/K)^{ab})
```

commutes.  This is `NK.Reconstruct.ellIncl_ellRestrict`, the naturality that makes the level
inclusions `ellIncl` descend to a map `π_{L/K} : Γ_L → Γ_K` of the projective limits
(`NK.Reconstruct.pi`, Shimizu arXiv:2009.10431 §4, CoNF Ch. X §10.3).

## Contents

* `levelInclHom_extend_apply_coe` — the value of the relative restriction
  `levelRestrictHom (levelExtend L A hA) (levelExtend L B h) h'` at `y ∈ A`, in the ambient field;
* `levelInclHom_comp_levelRestrictHom` — **the naturality square at the level of the groups**
  `Gal(B/L) → Gal(A/K)`: restricting and then forgetting is forgetting and then restricting;
* `ellIncl_ellRestrict` — the same square on the ℓ-primary parts of the abelianisations.

The group-level statement reduces to the element computations of
`NK.Reconstruct.levelRestrictHom_apply_coe` (a restriction does not move the ambient element)
and `NK.Reconstruct.levelInclHom_apply_coe` (nor does the inclusion); the passage to the
abelianisation is the functoriality `Abelianization.map_comp` of the abelianisation, and the
passage to the ℓ-primary parts is the definition `ellRestrict_coe`/`ellIncl_coe` of the two maps.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K']

/-- **The value of the relative restriction map at a `K`-level, in the ambient field.**  Restricting
an automorphism `g` of the level `B/L` (i.e. of `levelExtend L B h`) to the level `A/L`
(i.e. of `levelExtend L A hA`) and evaluating at `y ∈ A` is evaluating `g` at `y`, read off in the
ambient field `K'`.

(Both `levelExtend L A hA` and `levelExtend L B h` have the same underlying subsets of `K'` as `A`
and `B`; the two subtypes are identified without moving the ambient element.) -/
theorem levelRestrictHom_extend_apply_coe (L A B : FrobLevel K K') (hA : L.L ≤ A.L)
    (hAB : A.L ≤ B.L)
    (g : Gal(↥(levelExtend L B (hA.trans hAB)).L/↥L.L)) (y : ↥A.L) :
    ((levelRestrictHom (levelExtend L A hA) (levelExtend L B (hA.trans hAB))
        (levelExtend_mono L A B hA (hA.trans hAB) hAB) g) y : K')
      = (g ⟨(y : K'), (show (y : K') ∈ B.L from hAB y.2)⟩ : K') := by
  rw [levelRestrictHom_apply_coe (levelExtend L A hA) (levelExtend L B (hA.trans hAB))
    (levelExtend_mono L A B hA (hA.trans hAB) hAB) g
    (show ↥(levelExtend L A hA).L from y)]

/-- **The naturality square at the level of the Galois groups.**  For finite Galois levels
`L ≤ A ≤ B` of `K'/K`, restricting a `B/L`-automorphism to the level `A/L` and then forgetting the
`L`-structure agrees with forgetting the `L`-structure and then restricting the resulting
`B/K`-automorphism to `A`:

```
  (levelRestrictHom A B hAB) ∘ (levelInclHom L B (hA.trans hAB))
    = (levelInclHom L A hA) ∘ (levelRestrictHom (levelExtend L A hA) (levelExtend L B _) _).
```

Both sides are computed on an element `x ∈ A` via the two "the map does not move the ambient
element" lemmas: the left one gives `g` evaluated at the element of `B` lying over `x`, and so does
the right one. -/
theorem levelInclHom_comp_levelRestrictHom (L A B : FrobLevel K K') (hA : L.L ≤ A.L)
    (hAB : A.L ≤ B.L) :
    ((levelRestrictHom A B hAB).comp (levelInclHom L B (hA.trans hAB)) :
      Gal(↥(levelExtend L B (hA.trans hAB)).L/↥L.L) →* Gal(↥A.L/K))
      = ((levelInclHom L A hA).comp
        (levelRestrictHom (levelExtend L A hA) (levelExtend L B (hA.trans hAB))
          (levelExtend_mono L A B hA (hA.trans hAB) hAB)) :
        Gal(↥(levelExtend L B (hA.trans hAB)).L/↥L.L) →* Gal(↥A.L/K)) := by
  ext g x
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, levelRestrictHom_apply_coe,
    levelInclHom_apply_coe, levelInclHom_apply_coe, levelRestrictHom_apply_coe]

/-- Naturality of the level inclusion `ellIncl` with respect to the transition maps of the two
projective systems: restricting a `B/L`-automorphism to `A` and then forgetting the `L`-structure
is forgetting the `L`-structure and then restricting, for `L ≤ A ≤ B` finite Galois levels of
`K'/K`. -/
theorem ellIncl_ellRestrict {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) (L A B : FrobLevel K K')
    (hA : L.L ≤ A.L) (hAB : A.L ≤ B.L) :
    ((ellRestrict ℓ A B hAB).comp (ellIncl ℓ L B (hA.trans hAB)) :
      LevelEllPart (K := ↥L.L) (K' := K') (levelExtend L B (hA.trans hAB)).L ℓ →*
        LevelEllPart (K := K) (K' := K') A.L ℓ)
      = ((ellIncl ℓ L A hA).comp
        (ellRestrict ℓ (levelExtend L A hA) (levelExtend L B (hA.trans hAB))
          (levelExtend_mono L A B hA (hA.trans hAB) hAB)) :
        LevelEllPart (K := ↥L.L) (K' := K') (levelExtend L B (hA.trans hAB)).L ℓ →*
          LevelEllPart (K := K) (K' := K') A.L ℓ) := by
  -- Both sides are morphisms out of the same ℓ-part; it suffices to compare their underlying
  -- elements of `Gal(A/K)^{ab}`.
  ext x
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ellRestrict_coe, ellIncl_coe, ellIncl_coe]
  -- Descend to the level `A` (unfolding `ellRestrict`), and use the functoriality of the
  -- abelianisation to combine the two induced maps.
  rw [levelRestrict, ellRestrict_coe, levelRestrict, ← MonoidHom.comp_apply,
    ← MonoidHom.comp_apply, Abelianization.map_comp, Abelianization.map_comp,
    levelInclHom_comp_levelRestrictHom]

end NK.Reconstruct
