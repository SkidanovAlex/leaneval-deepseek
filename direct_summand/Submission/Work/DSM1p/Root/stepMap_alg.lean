import Mathlib
import Submission.Work.DSM1p.Basic
import Submission.Work.DSM1p.Root.stepMap_root

/-!
# `RootTower.stepMap` fixes the image of the base ring

This module records the elementary but notationally delicate fact that the transition maps of the
root tower `R[x]/(x^{p^m} - a)` (`Work.DSM1p.RootTower`) are maps of `R`-algebras: they commute
with the structure maps `R → R[x]/(x^{p^m} - a)`.

The only difficulty is that `RootTower.stepMap i j h` is defined as
`(Nat.add_sub_cancel' h) ▸ RootTower.stepIter R p a i (j - i)`, a `▸`-cast of a ring hom along an
equality of the *codomain index*; the two helper lemmas `eqrec_rootTower_ringHom_apply` (which is
`Work.DSM1p.Root.eqrec_rootTower_ringHom_apply`, proved in `stepMap_root.lean`) and
`eqrec_rootTower_algebraMap` move the cast out of the way.

The main results are

* `stepIter_algebraMap` : `stepIter i k (algebraMap r) = algebraMap r` (both sides in the
  `(i+k)`-th stage);
* `stepMap_algebraMap` : `stepMap i j h (algebraMap r) = algebraMap r`;
* `stepMap_directedSystem` : the instance `DirectedSystem (RootTower R p a) (stepMap · · ·)`,
  needed to invoke the colimit calculus of `Ring.DirectLimit` (e.g.
  `Ring.DirectLimit.of.zero_exact`).  It is proved by extensionality for ring homomorphisms out
  of `AdjoinRoot` (`AdjoinRoot.ringHom_ext`): two such maps agree as soon as they agree on the
  image of the base ring (which is `stepMap_algebraMap`) and on the adjoined root (which is
  `stepMap_root`).
-/

namespace Work.DSM1p.Root

universe u

open Polynomial

section Cast

variable (R : Type u) [CommRing R] (p : ℕ) (a : R)

/-- Casting an `R`-multiple of `1` in the root tower along an equality of the index. -/
lemma eqrec_rootTower_algebraMap {i j : ℕ} (e : i = j) (r : R) :
    e ▸ (algebraMap R (RootTower R p a i) r) = algebraMap R (RootTower R p a j) r := by
  cases e
  rfl

end Cast

section AlgebraMap

variable (R : Type u) [CommRing R] (p : ℕ) (a : R)

/-- The iterated transition maps of the root tower are `R`-algebra maps: they send the image of
`r : R` to the image of `r`. -/
theorem stepIter_algebraMap (i k : ℕ) (r : R) :
    RootTower.stepIter R p a i k (algebraMap R (RootTower R p a i) r) =
      algebraMap R (RootTower R p a (i + k)) r := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show RootTower.step R p a (i + k)
        (RootTower.stepIter R p a i k (algebraMap R (RootTower R p a i) r)) =
      algebraMap R (RootTower R p a (i + k + 1)) r
    rw [ih]
    rw [show RootTower.step R p a (i + k) = AdjoinRoot.lift (AdjoinRoot.of _)
          (RootTower.root R p a (i + k + 1) ^ p) _ from rfl]
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.lift_of _

/-- The transition maps of the root tower are `R`-algebra maps. -/
theorem stepMap_algebraMap (i j : ℕ) (h : i ≤ j) (r : R) :
    RootTower.stepMap R p a i j h (algebraMap R (RootTower R p a i) r) =
      algebraMap R (RootTower R p a j) r := by
  rw [show RootTower.stepMap R p a i j h =
      (Nat.add_sub_cancel' h) ▸ RootTower.stepIter R p a i (j - i) from rfl]
  rw [eqrec_rootTower_ringHom_apply]
  rw [stepIter_algebraMap]
  exact eqrec_rootTower_algebraMap R p a (Nat.add_sub_cancel' h) r

end AlgebraMap

section DirectedSystem

variable (R : Type u) [CommRing R] (p : ℕ) (a : R)

/-- The transition maps of the root tower form a directed system: the composite of two transition
maps is the transition map of the composite index.  This is the compatibility datum needed to use
the colimit calculus of `Ring.DirectLimit` for `RootClosure R p a`. -/
instance stepMap_directedSystem :
    DirectedSystem (RootTower R p a) (fun i j h => ⇑(RootTower.stepMap R p a i j h)) where
  map_self := fun {i} x => by
    have h : RootTower.stepMap R p a i i le_rfl = RingHom.id _ := by
      refine AdjoinRoot.ringHom_ext ?_ ?_
      · ext r
        show RootTower.stepMap R p a i i le_rfl (algebraMap R (RootTower R p a i) r)
            = algebraMap R (RootTower R p a i) r
        exact stepMap_algebraMap R p a i i le_rfl r
      · show RootTower.stepMap R p a i i le_rfl (RootTower.root R p a i) = RootTower.root R p a i
        rw [stepMap_root, show i - i = 0 from Nat.sub_self i]
        simp
    rw [h]
    rfl
  map_map := fun {k j i} hij hjk x => by
    have h : (RootTower.stepMap R p a j k hjk).comp (RootTower.stepMap R p a i j hij) =
        RootTower.stepMap R p a i k (hij.trans hjk) := by
      refine AdjoinRoot.ringHom_ext ?_ ?_
      · ext r
        show RootTower.stepMap R p a j k hjk
              (RootTower.stepMap R p a i j hij (algebraMap R (RootTower R p a i) r))
            = RootTower.stepMap R p a i k (hij.trans hjk) (algebraMap R (RootTower R p a i) r)
        simp only [stepMap_algebraMap]
      · show RootTower.stepMap R p a j k hjk
            (RootTower.stepMap R p a i j hij (RootTower.root R p a i))
          = RootTower.stepMap R p a i k (hij.trans hjk) (RootTower.root R p a i)
        rw [stepMap_root, map_pow, stepMap_root, stepMap_root, ← pow_mul, ← pow_add]
        rw [show (k - j) + (j - i) = k - i from by omega]
    show ((RootTower.stepMap R p a j k hjk).comp (RootTower.stepMap R p a i j hij)) x
        = (RootTower.stepMap R p a i k (hij.trans hjk)) x
    rw [h]

end DirectedSystem

end Work.DSM1p.Root
