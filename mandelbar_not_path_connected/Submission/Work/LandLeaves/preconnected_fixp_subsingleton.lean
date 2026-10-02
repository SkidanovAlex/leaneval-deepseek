import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The fixed points of an iterate of the holomorphic second return map `Tsq c`

`Tsq c z = (z² + c̄)² + c` is a *holomorphic polynomial* map of `z`
(`Work.Landing.Tsq`), of degree `4`.  Hence for any `n` its `n`-th iterate
`(Tsq c)^[n]` is again a polynomial map, of degree `4 ^ n`; we represent it by the
polynomial `iterPoly c n` (obtained by composing `tsqPoly c` with itself `n`
times, starting from `X`), so that `(iterPoly c n).eval z = (Tsq c)^[n] z`.

A polynomial map which is not the identity has finitely many fixed points: its
fixed points are the roots of the polynomial `iterPoly c n - X`, which is nonzero
precisely because `(Tsq c)^[n] ≠ id` for `n > 0` (`Tsq c` is even, so it is not
injective, and neither is any iterate of it).

Since `ℂ` is a metric space, countable subsets of `ℂ` are totally disconnected
(`Set.Countable.isTotallyDisconnected`).  Therefore any preconnected set of
points that are all fixed by `(Tsq c)^[n]` with `n > 0` must be a subsingleton.
That is the content of `preconnected_fixp_subsingleton`, a small but essential
step in the study of the tricorn dynamics: the periodic points of `Tsq c` contain
no nontrivial preconnected continuum.
-/

namespace Work.LandLeaves

open Polynomial

/-- The polynomial representing `Tsq c = (·² + c̄)² + c`. -/
private noncomputable def tsqPoly (c : ℂ) : ℂ[X] :=
  (Polynomial.X ^ 2 + Polynomial.C (star c)) ^ 2 + Polynomial.C c

private lemma tsqPoly_eval (c z : ℂ) : (tsqPoly c).eval z = Work.Landing.Tsq c z := by
  simp [tsqPoly, Work.Landing.Tsq]

/-- `Tsq c` is an even function. -/
private lemma tsq_neg (c z : ℂ) : Work.Landing.Tsq c (-z) = Work.Landing.Tsq c z := by
  simp only [Work.Landing.Tsq, neg_sq]

/-- The polynomial representing the `n`-th iterate of `Tsq c`. -/
private noncomputable def iterPoly (c : ℂ) (n : ℕ) : ℂ[X] :=
  (fun q : ℂ[X] => q.comp (tsqPoly c))^[n] Polynomial.X

private lemma iterPoly_succ (c : ℂ) (n : ℕ) :
    iterPoly c (n + 1) = (iterPoly c n).comp (tsqPoly c) := by
  simp only [iterPoly, Function.iterate_succ_apply']

/-- The polynomial `iterPoly c n` evaluates to the `n`-th iterate of `Tsq c`. -/
private lemma iterPoly_eval (c : ℂ) (n : ℕ) (z : ℂ) :
    (iterPoly c n).eval z = (Work.Landing.Tsq c)^[n] z := by
  induction n generalizing z with
  | zero => simp [iterPoly]
  | succ k ih =>
      rw [iterPoly_succ, Polynomial.eval_comp, tsqPoly_eval, ih,
        Function.iterate_succ_apply]

/-- For `n > 0` the iterate `(Tsq c)^[n]` is not the identity: `Tsq c` is even, so
`(Tsq c)^[n] 1 = (Tsq c)^[n] (-1)`, which the identity would turn into `1 = -1`. -/
private lemma tsq_iterate_ne_id (c : ℂ) (n : ℕ) (hn : 0 < n) :
    ¬ (∀ z : ℂ, (Work.Landing.Tsq c)^[n] z = z) := by
  intro hid
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  have htsq : Work.Landing.Tsq c (1 : ℂ) = Work.Landing.Tsq c (-1) := by
    rw [tsq_neg]
  have key : (Work.Landing.Tsq c)^[k + 1] (1 : ℂ) = (Work.Landing.Tsq c)^[k + 1] (-1) := by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, htsq]
  have h1 : (1 : ℂ) = -1 := by
    calc (1 : ℂ) = (Work.Landing.Tsq c)^[k + 1] 1 := (hid 1).symm
      _ = (Work.Landing.Tsq c)^[k + 1] (-1) := key
      _ = -1 := hid (-1)
  norm_num at h1

/-- A preconnected set of points that are all fixed by the `n`-th iterate of `Tsq c`
(`n > 0`) is a subsingleton. -/
theorem preconnected_fixp_subsingleton (c : ℂ) (n : ℕ) (hn : 0 < n) {A : Set ℂ}
    (hA : IsPreconnected A) (hfix : ∀ z ∈ A, (Work.Landing.Tsq c)^[n] z = z) :
    A.Subsingleton := by
  -- The polynomial `P - X` whose roots are the fixed points of `(Tsq c)^[n]`.
  have hQ : iterPoly c n - Polynomial.X ≠ 0 := by
    intro h
    refine tsq_iterate_ne_id c n hn (fun z => ?_)
    have hz : (iterPoly c n).eval z = z := by
      have h2 : (iterPoly c n).eval z - z = 0 := by
        simpa using congrArg (Polynomial.eval z) h
      exact sub_eq_zero.mp h2
    rw [iterPoly_eval] at hz
    exact hz
  -- Every fixed point is a root of `P - X`.
  have hsub : {z : ℂ | (Work.Landing.Tsq c)^[n] z = z} ⊆
      {z : ℂ | (iterPoly c n - Polynomial.X).IsRoot z} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, iterPoly_eval, Polynomial.eval_X, hz,
      sub_self]
  have hfin : Set.Finite {z : ℂ | (Work.Landing.Tsq c)^[n] z = z} :=
    (Polynomial.finite_setOfPred_isRoot hQ).subset hsub
  -- Countable subsets of `ℂ` are totally disconnected; `A` is such a subset.
  exact (Set.Countable.isTotallyDisconnected hfin.countable) A (fun z hz => hfix z hz) hA

end Work.LandLeaves
