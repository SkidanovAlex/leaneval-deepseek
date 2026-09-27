/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Naturality of the cup product on simplicial cohomology

The cup product on the cohomology of a simplicial set is natural with respect to pullback along a
morphism `f : S ⟶ T` of simplicial sets:

`f^* (x ⌣ y) = f^* x ⌣ f^* y`.

Since `H.cupOf` is defined on arbitrary cohomology classes by choosing representatives with
`Quot.out` (`Submission.Work.Cohomology.Cohomology`), the proof runs as follows.

* Replace `x` and `y` by the classes of their chosen representatives, so that the chain-level
  computation rule `H_cupOf_mk` for the cup product of *classes of cocycles* applies.
* On the left, `H.map_mk` computes the pullback of a class on a representative, and then the
  chain-level naturality `pullbackCo_cupOf` moves the pullback past the cup product.
* On the right, `H.map_mk` again computes the pullback of the two arguments on the chosen
  representatives, and `H_cupOf_mk` computes the resulting product.

Both sides are then the class of `cupOf S R h (pullbackCo R f A) (pullbackCo R f B)`, where
`A, B` are the chosen representatives of `x, y`; the two witnesses of being a cocycle are
irrelevant, so `Subtype.ext`/`congrArg` finishes.
-/
import Mathlib
import Submission.Work.Cohomology.Basic
import Submission.Work.Cohomology.Cup
import Submission.Work.Cohomology.coboundary_comp
import Submission.Work.Cohomology.cupOf_coboundary
import Submission.Work.Cohomology.Cohomology
import Submission.Work.Cohomology.H_cupOf_mk

namespace Work.Cohomology

open Submission.Cohomology

/-- **Naturality of the cup product on cohomology.**  Pullback along a morphism of simplicial sets
is a ring homomorphism for the cup product: `f^* (x ⌣ y) = (f^* x) ⌣ (f^* y)`. -/
theorem H_map_cupOf {S T : SSet.{0}} {R : Type} [CommRing R] (f : S ⟶ T) {n p q : ℕ}
    (h : p + q = n) (x : Submission.Cohomology.H T R p) (y : Submission.Cohomology.H T R q) :
    Submission.Cohomology.H.map R f n (Submission.Cohomology.H.cupOf h x y)
      = Submission.Cohomology.H.cupOf h (Submission.Cohomology.H.map R f p x)
          (Submission.Cohomology.H.map R f q y) := by
  -- Work with the representatives chosen by `Quot.out`.
  have hx : H.mk (Quot.out x).1 (Quot.out x).2 = x := Quotient.out_eq x
  have hy : H.mk (Quot.out y).1 (Quot.out y).2 = y := Quotient.out_eq y
  rw [← hx, ← hy]
  -- Left hand side: compute the product on representatives, then pull back.
  rw [H_cupOf_mk h (Quot.out x).1 (Quot.out y).1 (Quot.out x).2 (Quot.out y).2]
  rw [Submission.Cohomology.H.map_mk]
  -- Right hand side: pull back both factors, then compute the product.
  rw [Submission.Cohomology.H.map_mk, Submission.Cohomology.H.map_mk,
    H_cupOf_mk h _ _ _ _]
  -- Both sides are now the class of the same cochain; the cocycle witnesses are irrelevant.
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  exact Submission.Cohomology.pullbackCo_cupOf R f h _ _

end Work.Cohomology
