import Mathlib
import Submission.Work.DSM1p.Basic
import Submission.Work.DSM1p.Root.stepMap_alg

/-!
# The root closure as an `R`-algebra: linearity of the structure maps

This module collects the elementary algebra facts about the root closure
`RootClosure R p a = colim_m R[x]/(x^{p^m} - a)` that make it usable as an `R`-algebra:

* `flat_stage` : every stage of the tower is a flat `R`-module (it is even free, of rank `p ^ m`);
* `of_algebraMap` : the canonical maps `RootClosure.of R p a m` are `R`-algebra maps, i.e. they
  respect the structure maps from `R`;
* `of_smul` and `ofLinearMap` : consequently `RootClosure.of R p a m` is `R`-linear;
* `stepMapLinear` : likewise the transition maps `RootTower.stepMap R p a i j h` are `R`-linear.

These are used in the proof that `RootClosure R p a` is flat over `R`, and are the natural
interface for the parallel statement that it is `p`-torsion-free.
-/

namespace Work.DSM1p.Root

universe u

section Stage

variable (R : Type u) [CommRing R] (p : ℕ) (a : R)

/-- Every stage `R[x]/(x^{p^m} - a)` of the root tower is a flat `R`-module: it is free of rank
`p ^ m`, because `X ^ (p ^ m) - C a` is monic as soon as `p ≠ 0`. -/
theorem flat_stage (hp : p ≠ 0) (m : ℕ) : Module.Flat R (RootTower R p a m) :=
  RootExt.flat R (p ^ m) a (pow_ne_zero m hp)

end Stage

section Linearity

variable (R : Type u) [CommRing R] (p : ℕ) (a : R)

/-- The canonical map from a stage of the tower to the root closure is an `R`-algebra map. -/
theorem of_algebraMap (m : ℕ) (r : R) :
    RootClosure.of R p a m (algebraMap R (RootTower R p a m) r) =
      algebraMap R (RootClosure R p a) r := by
  show RootClosure.of R p a m (algebraMap R (RootTower R p a m) r) =
    RootClosure.of R p a 0 (algebraMap R (RootTower R p a 0) r)
  rw [← stepMap_algebraMap R p a 0 m (Nat.zero_le m) r]
  exact Ring.DirectLimit.of_f (Nat.zero_le m) (algebraMap R (RootTower R p a 0) r)

/-- The canonical map from a stage of the tower to the root closure is `R`-linear. -/
theorem of_smul (m : ℕ) (r : R) (y : RootTower R p a m) :
    RootClosure.of R p a m (r • y) = r • RootClosure.of R p a m y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, of_algebraMap]

/-- The canonical map from a stage of the tower to the root closure, as an `R`-linear map. -/
noncomputable def ofLinearMap (m : ℕ) : RootTower R p a m →ₗ[R] RootClosure R p a where
  toFun := RootClosure.of R p a m
  map_add' x y := map_add (RootClosure.of R p a m) x y
  map_smul' r x := of_smul R p a m r x

@[simp]
theorem ofLinearMap_apply (m : ℕ) (x : RootTower R p a m) :
    ofLinearMap R p a m x = RootClosure.of R p a m x := rfl

/-- The transition maps of the root tower are `R`-linear. -/
noncomputable def stepMapLinear (i j : ℕ) (h : i ≤ j) :
    RootTower R p a i →ₗ[R] RootTower R p a j where
  toFun := RootTower.stepMap R p a i j h
  map_add' x y := map_add (RootTower.stepMap R p a i j h) x y
  map_smul' r x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, stepMap_algebraMap]
    simp

@[simp]
theorem stepMapLinear_apply (i j : ℕ) (h : i ≤ j) (x : RootTower R p a i) :
    stepMapLinear R p a i j h x = RootTower.stepMap R p a i j h x := rfl

end Linearity

end Work.DSM1p.Root
