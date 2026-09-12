import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.klain333_step

/-!
# `klain_333_box_vanishing` — Klain's Theorem 3.3 ("box vanishing")

This is Theorem 3.3 of D. A. Klain, *A short proof of Hadwiger's characterization
theorem*, Mathematika 42 (1995) 329–339:

> Suppose that `μ` is a continuous translation invariant simple valuation on `Kⁿ`.
> Suppose also that `μ([0,1]ⁿ) = 0`, and that `μ(K) = μ(−K)` for all `K ∈ Kⁿ`.
> Then `μ(K) = 0` for all `K ∈ Kⁿ`.

In the language of the `hadwiger` challenge, the same statement reads: a continuous
quadruple-additive (inclusion–exclusion) valuation `φ` on the convex bodies of
`EuclideanSpace ℝ (Fin n)` that is translation invariant, vanishes on bodies with empty
interior, satisfies `φ(-A) = φ(A)`, and vanishes on the coordinate unit cube, is
identically zero.

## Where the mathematics lives

The full proof (Klain pp. 334–337) is an induction on the dimension `n`:

* `n = 0` is trivial (`AuxK333`-style argument / `boxVan_zero`);
* `n = 1` is `klain_333_dim_one` (`klain333_fin1` for the coordinate space);
* the induction step (section valuation `τ(K) = μ(K × [0,1])`, axis-parallel boxes,
  boxes in every orthonormal frame via Givens/orthogonal-word decomposition, right
  cylinders, oblique prisms, zonotopes and zonoids, smooth centred bodies via the
  cosine transform, simplices via the parallelotope decomposition
  `P = A ∪ P₁ ∪ (−A+v)`, triangulation of polytopes, and density of polytopes)
  is assembled in the shared commons:

  * `Commons.Geometry.Convex.Hadwiger.BoxVan` and
    `Commons.Geometry.Convex.Hadwiger.boxVan_all : ∀ n, BoxVan n`
    (module `Submission.Commons.Geometry.Convex.Hadwiger.klain333_step`),
  * built on the supporting commons modules `dissection_additivity`,
    `valuation_zero_on_axisBoxes`, `klain333_boxes_all_orientations`,
    `oblique_prism_zero`, `klain333_from_cylinders`,
    `zonoidLimit_of_continuous_even_nonneg`, `smoothCentred_dense`,
    `simplex_parallelotope_dissection`, `polytope_triangulation`, ... .

This module is the thin wrapper that restates `boxVan_all` with the exact statement
requested for the `hadwiger` project (the phrasing with the outer `let V := ...`).
-/

namespace Commons.Geometry.Convex.Hadwiger

theorem klain_333_box_vanishing (n : ℕ) :
    let V := EuclideanSpace ℝ (Fin n)
    ∀ (φ : ConvexBody V → ℝ),
      Continuous φ →
      (∀ A B C D : ConvexBody V,
          (A : Set V) = (C : Set V) ∪ (D : Set V) →
          (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D) →
      (∀ A B : ConvexBody V, ∀ t : V,
          (B : Set V) = (fun x : V => x + t) '' (A : Set V) → φ A = φ B) →
      (∀ K : ConvexBody V, interior (K : Set V) = ∅ → φ K = 0) →
      (∀ A B : ConvexBody V, (B : Set V) = -(A : Set V) → φ A = φ B) →
      (∀ Q : ConvexBody V,
          (Q : Set V) = (EuclideanSpace.equiv (Fin n) ℝ).symm '' (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) → φ Q = 0) →
      ∀ K : ConvexBody V, φ K = 0 := by
  dsimp
  exact Commons.Geometry.Convex.Hadwiger.boxVan_all n

end Commons.Geometry.Convex.Hadwiger
