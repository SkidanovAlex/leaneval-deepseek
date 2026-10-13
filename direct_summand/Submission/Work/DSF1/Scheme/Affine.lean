import Mathlib
import ChallengeDeps

/-!
# Affineness results for a scheme separated over an affine base (DSF1)

Area `F1` of the direct summand project computes `RΓ(X, 𝒪_X)` by the Čech complex of a finite
affine open cover `U` of a scheme `X` separated over `Spec A`.  The Čech terms are products of the
sheaves `secSheaf (U (x 0) ⊓ ⋯ ⊓ U (x n))`, and to know that they are acyclic for global sections
one needs that the intersections of the members of the cover are affine, and that the open
immersions of affine opens of `X` are affine morphisms.  These are the two facts assembled here,
both consequences of `IsSeparated f`:

* `Work.DSF1.Scheme.diagonal_affineHom_of_isSeparated`: the diagonal `X ⟶ X ×_ℤ X` of `X` over
  `Spec ℤ` is an affine morphism (it is a closed immersion, since `X` is separated over the affine
  scheme `Spec A`);
* `Work.DSF1.Scheme.affineOpen_inf_of_isSeparated`,
  `Work.DSF1.Scheme.affineOpen_iInf_of_isSeparated`: intersections of affine opens of `X` are
  affine (Mathlib's `AlgebraicGeometry.IsAffineOpen.inf`/`iInf`, fed by the affine diagonal);
* `Work.DSF1.Scheme.affineHom_opens_ι_of_isSeparated`: for an affine open `W` of `X`, the open
  immersion `W.ι : W ⟶ X` is affine.
-/

namespace Work.DSF1.Scheme

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

variable {A : Type u} [CommRing A] {X : AlgebraicGeometry.Scheme.{u}}
  {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)}

/-- The diagonal of a scheme separated over an affine base, taken over the terminal scheme
`Spec ℤ`, is an affine morphism. -/
theorem diagonal_affineHom_of_isSeparated (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) [AlgebraicGeometry.IsSeparated f] :
    AlgebraicGeometry.IsAffineHom
      (CategoryTheory.Limits.pullback.diagonal (CategoryTheory.Limits.terminal.from X)) := by
  haveI : AlgebraicGeometry.IsSeparated (CategoryTheory.Limits.terminal.from X) := by
    rw [← CategoryTheory.Limits.terminal.comp_from f]
    infer_instance
  infer_instance

/-- Intersections of affine opens of a scheme separated over an affine base are affine. -/
theorem affineOpen_inf_of_isSeparated (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) [AlgebraicGeometry.IsSeparated f]
    {V W : X.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
    (hW : AlgebraicGeometry.IsAffineOpen W) : AlgebraicGeometry.IsAffineOpen (V ⊓ W) := by
  haveI := diagonal_affineHom_of_isSeparated (A := A) X f
  exact hV.inf hW

/-- Finite intersections of affine opens of a scheme separated over an affine base are affine. -/
theorem affineOpen_iInf_of_isSeparated (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) [AlgebraicGeometry.IsSeparated f]
    {ι : Type u} {n : ℕ} (U : ι → X.Opens)
    (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i)) (x : Fin (n + 1) → ι) :
    AlgebraicGeometry.IsAffineOpen (⨅ a, U (x a)) := by
  haveI := diagonal_affineHom_of_isSeparated (A := A) X f
  exact AlgebraicGeometry.IsAffineOpen.iInf (fun a => hU (x a))

/-- The open immersion of an affine open of a scheme separated over an affine base is an affine
morphism. -/
theorem affineHom_opens_ι_of_isSeparated (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) [AlgebraicGeometry.IsSeparated f]
    (W : X.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) :
    AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.Scheme.Opens.ι W) := by
  rw [AlgebraicGeometry.isAffineHom_iff]
  intro U hU
  rw [← (AlgebraicGeometry.Scheme.Opens.ι W).isAffineOpen_iff_of_isOpenImmersion]
  rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
    AlgebraicGeometry.Scheme.Opens.opensRange_ι]
  exact affineOpen_inf_of_isSeparated X f hW hU

end Work.DSF1.Scheme
