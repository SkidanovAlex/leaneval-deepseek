import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.ORLyndon.annAtDefs
import Submission.Work.OROneRel.Interface

/-!
# The geometric factorisation of the root Fox vector at a letter occurring once

Let `x` be a generator that occurs neither in `t` nor in `W`, and put

`u = t * (of x * W) ^ k`,  `r = u ^ l`.

Because `x` does not occur in `t` or in `W`, the Fox derivative of `u` with respect to `x`
collapses to the geometric series in `of x * W`:

`(∂u/∂x) = t * ∑_{i < k} (of x * W) ^ i   in K[F(α)]`,

and pushing this identity along the presentation map `F(α) →* ⟨α | r⟩` gives

`rootVec K r u x = of (presentRho r t) * ∑_{i < k} (of (presentRho r (of x * W))) ^ i`.

The Fox-calculus input is the Leibniz rule `foxD_mul` together with the power rule `foxD_pow`:
`∂u/∂x = ∂t/∂x + of t * ∂((of x * W) ^ k)/∂x`, the derivative `∂t/∂x` vanishes because `x ∉ t`,
the derivative `∂(of x * W)/∂x = 1` since `∂W/∂x = 0` and `∂(of x)/∂x = 1`, and then
`∂((of x * W) ^ k)/∂x = (∑_{i < k} (of x * W) ^ i) * 1`.

The corresponding identity in the group algebra is obtained by applying the ring homomorphism
`presentAlg`, which sends `of w` to `of (presentRho r w)` and commutes with sums and products.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

/-- `FreeGroup.toWord` does not depend on the `DecidableEq` instance with which it is computed
(`Decidable _` is a subsingleton); the noncomputable definitions of this development elaborate with
the `Classical` instance, while a hypothesis `x ∉ relatorLetters v` may be used at the ambient
instance. -/
theorem toWord_eq_of_decEq' {α : Type*} (i j : DecidableEq α) (v : FreeGroup α) :
    @FreeGroup.toWord α i v = @FreeGroup.toWord α j v := by
  have h : i = j := funext fun a => funext fun b => Subsingleton.elim _ _
  rw [h]

/-- The Fox derivative of a word vanishes on a symbol that does not occur in it.  (Local copy of
`Work.ORLyndon.foxD_eq_zero_of_notMem_relatorLetters`, kept here to avoid the heavy import of the
Cohen--Lyndon induction file; it is proved from `Fox.lean` alone.) -/
theorem foxD_eq_zero_of_notMem_relatorLetters' {α : Type*} [DecidableEq α] {K : Type*} [Ring K]
    (q : α) (v : FreeGroup α) (h : q ∉ Work.OROneRel.relatorLetters v) :
    foxD (K := K) q v = 0 := by
  have hq : ∀ b : Bool, (q, b) ∉ @FreeGroup.toWord α (Classical.decEq α) v := by
    intro b hb
    exact h (by rw [Work.OROneRel.relatorLetters]; exact ⟨b, hb⟩)
  have hqc : ∀ b : Bool, (q, b) ∉ FreeGroup.toWord v := by
    intro b hb
    refine hq b ?_
    rwa [toWord_eq_of_decEq' (inferInstance : DecidableEq α) (Classical.decEq α) v] at hb
  calc foxD (K := K) q v = foxD (K := K) q (FreeGroup.mk (FreeGroup.toWord v)) := by
        rw [FreeGroup.mk_toWord]
    _ = 0 := foxWord_eq_zero_of_notMem (by rw [mem_letters]; exact fun ⟨b, hb⟩ => hqc b hb)

/-- **The Fox derivative of `t * (of x * W) ^ k` at a letter `x` occurring neither in `t` nor in
`W`** is the geometric series in `of x * W` multiplied on the left by `of t`:

`∂(t * (of x * W) ^ k)/∂x = of t * ∑_{i < k} (of x * W) ^ i`.

Both componentwise computations hold for the trivial reason that the derivative of a word free of
`x` vanishes: `∂t/∂x = 0` and `∂W/∂x = 0`, so that `∂(of x * W)/∂x = 1`. -/
theorem foxD_mul_geom_pow {α : Type*} [DecidableEq α] {K : Type*} [Ring K]
    (x : α) (t W : FreeGroup α) (ht : x ∉ Work.OROneRel.relatorLetters t)
    (hW : x ∉ Work.OROneRel.relatorLetters W) (k : ℕ) :
    foxD (K := K) x (t * (FreeGroup.of x * W) ^ k) =
      (MonoidAlgebra.of K (FreeGroup α) t) *
        ∑ i ∈ Finset.range k, ((MonoidAlgebra.of K (FreeGroup α)) (FreeGroup.of x * W)) ^ i := by
  have hxW : foxD (K := K) x (FreeGroup.of x * W) = 1 := by
    rw [foxD_mul, foxD_of, if_pos rfl, foxD_eq_zero_of_notMem_relatorLetters' x W hW,
      mul_zero, add_zero]
  rw [foxD_mul, foxD_pow, hxW, mul_one, foxD_eq_zero_of_notMem_relatorLetters' x t ht, zero_add]

/-- **The geometric factorisation of the root Fox vector.**  For `x` a generator occurring in
neither `t` nor `W`, the `x`-component of the Fox vector of the root `u = t * (of x * W) ^ k` of
`r = u ^ l`, pushed into the group algebra `K[⟨α | r⟩]`, is the class of `t` times the geometric
series in the class of `of x * W`:

`(∂u/∂x)_x = of (presentRho r t) * ∑_{i < k} (of (presentRho r (of x * W))) ^ i`.

This is the Fox computation behind the `σ`-grading/geometric-series arguments of the Cohen--Lyndon
induction: the letter `x` occurs exactly in the `k` consecutive positions of the `(of x * W) ^ k`
block of the root, and the derivative collects the partial products of that block. -/
theorem rootVec_geom_factorisation {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    (x : α) (t W : FreeGroup α) (ht : x ∉ Work.OROneRel.relatorLetters t)
    (hW : x ∉ Work.OROneRel.relatorLetters W) (k l : ℕ) (hk : 1 ≤ k) :
    rootVec K ((t * (FreeGroup.of x * W) ^ k) ^ l) (t * (FreeGroup.of x * W) ^ k) x =
      MonoidAlgebra.of K (OneRelatorGroup ((t * (FreeGroup.of x * W) ^ k) ^ l))
          (presentRho ((t * (FreeGroup.of x * W) ^ k) ^ l) t) *
        ∑ i ∈ Finset.range k,
          (MonoidAlgebra.of K (OneRelatorGroup ((t * (FreeGroup.of x * W) ^ k) ^ l))
            (presentRho ((t * (FreeGroup.of x * W) ^ k) ^ l) (FreeGroup.of x * W))) ^ i := by
  rw [rootVec_apply, foxD_mul_geom_pow x t W ht hW k, map_mul, map_sum, presentAlg_of]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [map_pow, presentAlg_of]

end Work.ORLyndon
