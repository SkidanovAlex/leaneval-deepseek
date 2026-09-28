import Mathlib
import Submission.Work.Kunneth.CrossH

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Bilinearity of the cross product on cohomology

`Work.Kunneth.crossH X Y p q : Hᵖ(X;ℤ) → H^q(Y;ℤ) → H^{p+q}(X×Y;ℤ)` is defined as
`π₁^*a ⌣ π₂^*b` (`Work.Kunneth.crossH_apply`).  This file proves that it is **bilinear**: it
packages it as a `ℤ`-linear map `Hᵖ(X;ℤ) →ₗ[ℤ] H^q(Y;ℤ) →ₗ[ℤ] H^{p+q}(X×Y;ℤ)`
(`Work.Kunneth.crossH_bilinear`), at the element level by the four laws of a bilinear map.

Concretely, `crossH` is the composite of the cup product with the two pullbacks of the
projections; additivity and `ℤ`-scalar-linearity of pullback and cup (`LinearMap.map_add`,
`LinearMap.map_zsmul` for the maps `pullbackH` and `cupH'`) give the four laws, and the packaged
map is `LinearMap.mk₂`.

## Note on instances

The carriers here are the underlying types of `ModuleCat ℤ`-objects, and Mathlib's `LinearMap`
records its scalar structure among its implicit arguments; for `ℤ` the structure coming from an
`AddCommGroup` (`AddCommGroup.toIntModule`) is only *propositionally*, not definitionally, equal to
the one carried by a `ModuleCat` object.  Consequently the proofs below assemble the identities
with `calc`/`congrArg`/`DFunLike.congr_fun` (checked by definitional equality of the *statements*)
rather than by `rw`/`simp`, which would insist on a syntactic match of the scalar-structure
arguments.

## Main results

* `crossH_add_left`, `crossH_smul_left`, `crossH_add_right`, `crossH_smul_right` — the four laws
  of a bilinear map, at the level of elements;
* `crossH_bilinear` — the packaged bilinear map.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Work.Kunneth

attribute [local instance 5000] AddCommGroup.toIntModule

/-- Additivity of the cross product in its first variable. -/
theorem crossH_add_left (X Y : SSet) (p q : ℕ)
    (a₁ a₂ : ↑((Work.Cohomology.cochainC ℤ X).homology p))
    (b : ↑((Work.Cohomology.cochainC ℤ Y).homology q)) :
    crossH X Y p q (a₁ + a₂) b = crossH X Y p q a₁ b + crossH X Y p q a₂ b := by
  calc crossH X Y p q (a₁ + a₂) b
      = (Work.Cohomology.cupH' ℤ (sProd X Y) p q)
          ((pullbackH (sProd X Y) X
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) (a₁ + a₂))
          ((pullbackH (sProd X Y) Y
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b) := rfl
    _ = (Work.Cohomology.cupH' ℤ (sProd X Y) p q)
          ((pullbackH (sProd X Y) X
              (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a₁
            + (pullbackH (sProd X Y) X
              (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a₂)
          ((pullbackH (sProd X Y) Y
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b) := by
          exact congrArg (fun x => (Work.Cohomology.cupH' ℤ (sProd X Y) p q) x
            ((pullbackH (sProd X Y) Y
              (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b))
            (map_add (pullbackH (sProd X Y) X
              (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a₁ a₂)
    _ = (Work.Cohomology.cupH' ℤ (sProd X Y) p q)
          ((pullbackH (sProd X Y) X
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a₁)
          ((pullbackH (sProd X Y) Y
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b)
        + (Work.Cohomology.cupH' ℤ (sProd X Y) p q)
          ((pullbackH (sProd X Y) X
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a₂)
          ((pullbackH (sProd X Y) Y
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b) := by
          exact DFunLike.congr_fun (map_add (Work.Cohomology.cupH' ℤ (sProd X Y) p q)
            ((pullbackH (sProd X Y) X
              (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a₁)
            ((pullbackH (sProd X Y) X
              (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a₂))
            ((pullbackH (sProd X Y) Y
              (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b)
    _ = crossH X Y p q a₁ b + crossH X Y p q a₂ b := rfl

/-- `ℤ`-scalar-linearity (indeed, `zsmul`-linearity) of the cross product in its first variable. -/
theorem crossH_smul_left (X Y : SSet) (p q : ℕ) (c : ℤ)
    (a : ↑((Work.Cohomology.cochainC ℤ X).homology p))
    (b : ↑((Work.Cohomology.cochainC ℤ Y).homology q)) :
    crossH X Y p q (c • a) b = c • crossH X Y p q a b := by
  calc crossH X Y p q (c • a) b
      = (Work.Cohomology.cupH' ℤ (sProd X Y) p q)
          ((pullbackH (sProd X Y) X
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) (c • a))
          ((pullbackH (sProd X Y) Y
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b) := rfl
    _ = (Work.Cohomology.cupH' ℤ (sProd X Y) p q)
          (c • (pullbackH (sProd X Y) X
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a)
          ((pullbackH (sProd X Y) Y
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b) := by
          exact congrArg (fun x => (Work.Cohomology.cupH' ℤ (sProd X Y) p q) x
            ((pullbackH (sProd X Y) Y
              (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b))
            (map_zsmul (pullbackH (sProd X Y) X
              (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) c a)
    _ = c • ((Work.Cohomology.cupH' ℤ (sProd X Y) p q)
          ((pullbackH (sProd X Y) X
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a)
          ((pullbackH (sProd X Y) Y
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b)) := by
          exact DFunLike.congr_fun (map_zsmul (Work.Cohomology.cupH' ℤ (sProd X Y) p q) c
            ((pullbackH (sProd X Y) X
              (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a))
            ((pullbackH (sProd X Y) Y
              (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b)
    _ = c • crossH X Y p q a b := rfl

/-- Additivity of the cross product in its second variable. -/
theorem crossH_add_right (X Y : SSet) (p q : ℕ)
    (a : ↑((Work.Cohomology.cochainC ℤ X).homology p))
    (b₁ b₂ : ↑((Work.Cohomology.cochainC ℤ Y).homology q)) :
    crossH X Y p q a (b₁ + b₂) = crossH X Y p q a b₁ + crossH X Y p q a b₂ := by
  calc crossH X Y p q a (b₁ + b₂)
      = (Work.Cohomology.cupH' ℤ (sProd X Y) p q)
          ((pullbackH (sProd X Y) X
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a)
          ((pullbackH (sProd X Y) Y
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) (b₁ + b₂)) := rfl
    _ = (Work.Cohomology.cupH' ℤ (sProd X Y) p q)
          ((pullbackH (sProd X Y) X
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a)
          ((pullbackH (sProd X Y) Y
              (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b₁
            + (pullbackH (sProd X Y) Y
              (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b₂) := by
          exact congrArg (fun x => (Work.Cohomology.cupH' ℤ (sProd X Y) p q)
            ((pullbackH (sProd X Y) X
              (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a) x)
            (map_add (pullbackH (sProd X Y) Y
              (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b₁ b₂)
    _ = (Work.Cohomology.cupH' ℤ (sProd X Y) p q)
          ((pullbackH (sProd X Y) X
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a)
          ((pullbackH (sProd X Y) Y
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b₁)
        + (Work.Cohomology.cupH' ℤ (sProd X Y) p q)
          ((pullbackH (sProd X Y) X
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a)
          ((pullbackH (sProd X Y) Y
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b₂) := by
          exact map_add ((Work.Cohomology.cupH' ℤ (sProd X Y) p q)
            ((pullbackH (sProd X Y) X
              (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a))
            ((pullbackH (sProd X Y) Y
              (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b₁)
            ((pullbackH (sProd X Y) Y
              (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b₂)
    _ = crossH X Y p q a b₁ + crossH X Y p q a b₂ := rfl

/-- `ℤ`-scalar-linearity of the cross product in its second variable. -/
theorem crossH_smul_right (X Y : SSet) (p q : ℕ) (c : ℤ)
    (a : ↑((Work.Cohomology.cochainC ℤ X).homology p))
    (b : ↑((Work.Cohomology.cochainC ℤ Y).homology q)) :
    crossH X Y p q a (c • b) = c • crossH X Y p q a b := by
  calc crossH X Y p q a (c • b)
      = (Work.Cohomology.cupH' ℤ (sProd X Y) p q)
          ((pullbackH (sProd X Y) X
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a)
          ((pullbackH (sProd X Y) Y
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) (c • b)) := rfl
    _ = (Work.Cohomology.cupH' ℤ (sProd X Y) p q)
          ((pullbackH (sProd X Y) X
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a)
          (c • (pullbackH (sProd X Y) Y
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b) := by
          exact congrArg (fun x => (Work.Cohomology.cupH' ℤ (sProd X Y) p q)
            ((pullbackH (sProd X Y) X
              (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a) x)
            (map_zsmul (pullbackH (sProd X Y) Y
              (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) c b)
    _ = c • ((Work.Cohomology.cupH' ℤ (sProd X Y) p q)
          ((pullbackH (sProd X Y) X
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a)
          ((pullbackH (sProd X Y) Y
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b)) := by
          exact map_zsmul ((Work.Cohomology.cupH' ℤ (sProd X Y) p q)
            ((pullbackH (sProd X Y) X
              (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p) a)) c
            ((pullbackH (sProd X Y) Y
              (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q) b)
    _ = c • crossH X Y p q a b := rfl

theorem crossH_bilinear (X Y : SSet) (p q : ℕ) :
    ∃ F : ↑((Work.Cohomology.cochainC ℤ X).homology p) →ₗ[ℤ]
            ↑((Work.Cohomology.cochainC ℤ Y).homology q) →ₗ[ℤ]
              ↑((Work.Cohomology.cochainC ℤ (Work.Kunneth.sProd X Y)).homology (p + q)),
      ∀ (a : ↑((Work.Cohomology.cochainC ℤ X).homology p))
        (b : ↑((Work.Cohomology.cochainC ℤ Y).homology q)),
        F a b = Work.Kunneth.crossH X Y p q a b := by
  refine ⟨LinearMap.mk₂ ℤ (fun a b => crossH X Y p q a b) ?_ ?_ ?_ ?_, ?_⟩
  · exact fun a₁ a₂ b => crossH_add_left X Y p q a₁ a₂ b
  · exact fun c a b => crossH_smul_left X Y p q c a b
  · exact fun a b₁ b₂ => crossH_add_right X Y p q a b₁ b₂
  · exact fun c a b => crossH_smul_right X Y p q c a b
  · intro a b
    rfl

end Work.Kunneth
