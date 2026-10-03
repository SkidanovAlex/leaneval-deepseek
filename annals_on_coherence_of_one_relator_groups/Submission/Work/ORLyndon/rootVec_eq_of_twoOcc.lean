import Mathlib
import Submission.Work.ORLyndon.twoOccBase

/-!
# The root Fox vector of a word in which a letter occurs exactly twice

Let `α` be a set of generators, `K` a field, `r : F(α)` a relator and `G = ⟨α | r⟩` the associated
one-relator group (`Work.ORLyndon.OneRelatorGroup`).  For a *root* `u` of `r` (the relator is then
`r = u ^ l`), the component at a letter `x` of the Fox vector of `u`, pushed into `K[G]`, is
`Work.ORLyndon.rootVec K r u x = presentAlg K r (∂u/∂x)`.

When the letter `x` occurs **exactly twice** in `u` -- say
`u = P · xᵇ · A · xᵇ · B` with `b : Bool` recording the exponent of `x` and with `P`, `A`, `B` words
in the other generators (`P, A, B : FreeGroup {z // z ≠ x}`, embedded by the Magnus inclusion
`Work.ORLyndon.magIncl x`) -- the Fox derivative `∂u/∂x` has exactly the two terms coming from the
two occurrences of `x`:

* the prefix ending just before the first occurrence, i.e. `P` (resp. `P · x⁻¹` when `b = false`),
  carrying the sign `+1` (resp. `-1`),
* that prefix times the *ratio* `x · A` (resp. `A · x⁻¹`) of the two occurrence terms.

This is packaged by `Work.ORLyndon.twoOccPref` and `Work.ORLyndon.twoOccRatio`, and the present file
proves the resulting identity

`rootVec K r u x = (if b then 1 else -1) • of (presentRho r (twoOccPref x b P)) *
                                        (1 + of (presentRho r (twoOccRatio x b A)))`

-- the two-term factorisation of the component on which the residual of the two-occurrence analysis
of `Submission/Work/ORLyndon/epsNeZeroDescent.lean` (`annAt_of_twoOcc`, and the order statement
`Work.ORLyndon.orderOf_presentRho_twoOcc`) operates: `annAt` at `x` becomes the order of the ratio.

## Proof

The Fox calculus is entirely formal here.  If `Q : FreeGroup {z // z ≠ x}` and `w` is a letter
different from `x`, then `∂(of w)/∂x = 0`, and the set of `Q` with `∂(magIncl x Q)/∂x = 0` is a
subgroup of `F(α ∖ {x})` by the derivation rule (`Work.ORLyndon.foxD_mul`, `foxD_inv`); hence
`foxD_magIncl`: the Magnus subgroup `F(α ∖ {x})` lies in the kernel of `∂/∂x`.  Applying the
derivation rule four times to `P · xᵇ · A · xᵇ · B` then leaves only the two terms of the two
occurrences of `xᵇ`: in the reduced word of `magIncl x Q` the letter `x` does not occur, so the
derivatives of the factors `P, A, B` vanish and each occurrence of `x` contributes `±` its prefix.
This is `foxD_twoOcc`, at the level of `K[F(α)]`.

The passage to `K[G]` is the ring homomorphism `presentAlg K r`, which sends `of w` to
`of (presentRho r w)` (`presentAlg_of`) and is `K`-linear (`presentAlg_smul`, from the fact that
`mapDomainRingHom` commutes with `algebraMap`).  Hence the scalar `(if b then 1 else -1)` and the
factorisation of the two-term sum both survive the push-forward, and the target identity follows
from the free one by rewriting with `rootVec_apply` (`rootVec K r u x = presentAlg K r (∂u/∂x)`).
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

/-- **The Fox derivative kills the Magnus subgroup.**  If `P` is a word in the generators other than
`x`, then `∂(magIncl x P)/∂x = 0` in `K[F(α)]`: the reduced word representing `magIncl x P` does not
contain the letter `x`.  Equivalently, `F(α ∖ {x})` is contained in the kernel of `∂/∂x`. -/
theorem foxD_magIncl {α : Type*} [DecidableEq α] {K : Type*} [Field K] (x : α)
    (P : FreeGroup {z : α // z ≠ x}) :
    foxD (K := K) x (magIncl x P) = 0 := by
  refine FreeGroup.induction_on P ?_ ?_ ?_ ?_
  · rw [map_one, foxD_one]
  · intro z
    simp [magIncl, z.2]
  · intro z ih
    rw [map_inv, foxD_inv, ih, mul_zero, neg_zero]
  · intro g h ihg ihh
    rw [map_mul, foxD_mul, ihg, ihh, mul_zero, add_zero]

/-- **The Fox derivative of a word with exactly two occurrences of `x`.**  For
`u = P · xᵇ · A · xᵇ · B` with `P, A, B` words in the generators other than `x`, the `x`-component
of the Fox vector of `u` is the two-term sum whose terms are the two occurrence prefixes, factored
through `Work.ORLyndon.twoOccPref` and `Work.ORLyndon.twoOccRatio`, with the overall sign
`(if b then 1 else -1)` recording whether the occurrences are of `x` or of `x⁻¹`. -/
theorem foxD_twoOcc {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    {u : FreeGroup α} {x : α} {b : Bool} {P A B : FreeGroup {z : α // z ≠ x}}
    (hu : u = magIncl x P * xbOf x b * magIncl x A * xbOf x b * magIncl x B) :
    foxD (K := K) x u = (if b then (1 : K) else -1) •
      (MonoidAlgebra.of K (FreeGroup α) (twoOccPref x b P) *
        (1 + MonoidAlgebra.of K (FreeGroup α) (twoOccRatio x b A))) := by
  subst hu
  cases b
  · simp only [xbOf, twoOccPref, twoOccRatio, Bool.false_eq_true, if_false]
    rw [neg_one_smul]
    rw [foxD_mul, foxD_mul, foxD_mul, foxD_mul]
    rw [foxD_magIncl, foxD_magIncl, foxD_magIncl, foxD_inv_of, if_pos rfl]
    simp only [map_mul, mul_zero, zero_add, add_zero, mul_neg, mul_add, mul_one, mul_assoc, neg_add]
  · simp only [xbOf, twoOccPref, twoOccRatio, if_true]
    rw [one_smul]
    rw [foxD_mul, foxD_mul, foxD_mul, foxD_mul]
    rw [foxD_magIncl, foxD_magIncl, foxD_magIncl, foxD_of, if_pos rfl]
    simp only [map_mul, mul_zero, zero_add, add_zero, mul_one, mul_add, mul_assoc]

/-- `presentAlg` fixes the scalars: the group-algebra map induced by an epimorphism of groups is a
map of `K`-algebras, so it commutes with `algebraMap` (`= MonoidAlgebra.single 1`). -/
theorem presentAlg_algebraMap {α : Type*} [DecidableEq α] {K : Type*} [Field K] (r : FreeGroup α)
    (c : K) :
    presentAlg K r (algebraMap K (MonoidAlgebra K (FreeGroup α)) c) =
      algebraMap K (MonoidAlgebra K (OneRelatorGroup r)) c :=
  RingHom.congr_fun
    (MonoidAlgebra.mapDomainRingHom_comp_algebraMap (R := K) (A := K)
      (M := FreeGroup α) (N := OneRelatorGroup r) (presentRho r)) c

/-- `presentAlg` is `K`-linear: it commutes with the scalar action of `K`. -/
theorem presentAlg_smul {α : Type*} [DecidableEq α] {K : Type*} [Field K] (r : FreeGroup α) (c : K)
    (z : MonoidAlgebra K (FreeGroup α)) :
    presentAlg K r (c • z) = c • presentAlg K r z := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, presentAlg_algebraMap]

/-- `presentAlg` carries the factored two-term shape
`of g * (1 + of h)` to the corresponding shape in `K[⟨α | r⟩]`. -/
theorem presentAlg_of_mul_one_add {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (r g h : FreeGroup α) :
    presentAlg K r ((MonoidAlgebra.of K (FreeGroup α) g) *
      (1 + MonoidAlgebra.of K (FreeGroup α) h)) =
    MonoidAlgebra.of K (OneRelatorGroup r) (presentRho r g) *
      (1 + MonoidAlgebra.of K (OneRelatorGroup r) (presentRho r h)) := by
  rw [map_mul, map_add, map_one, presentAlg_of, presentAlg_of]

theorem rootVec_eq_of_twoOcc {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    {r u : FreeGroup α} {x : α} {b : Bool} {P A B : FreeGroup {z : α // z ≠ x}}
    (hu : u = Work.ORLyndon.magIncl x P * Work.ORLyndon.xbOf x b * Work.ORLyndon.magIncl x A *
      Work.ORLyndon.xbOf x b * Work.ORLyndon.magIncl x B) :
    Work.ORLyndon.rootVec K r u x = (if b then (1 : K) else -1) •
      (MonoidAlgebra.of K (Work.ORLyndon.OneRelatorGroup r)
          (Work.ORLyndon.presentRho r (Work.ORLyndon.twoOccPref x b P)) *
        (1 + MonoidAlgebra.of K (Work.ORLyndon.OneRelatorGroup r)
          (Work.ORLyndon.presentRho r (Work.ORLyndon.twoOccRatio x b A)))) := by
  rw [rootVec_apply, foxD_twoOcc hu, presentAlg_smul, presentAlg_of_mul_one_add]

end Work.ORLyndon
