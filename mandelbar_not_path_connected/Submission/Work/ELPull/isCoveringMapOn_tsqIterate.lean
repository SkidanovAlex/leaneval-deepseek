/-
# The `m`-th iterate of `Tsq c` is a covering map off its critical values

`Tsq c z = (z² + c̄)² + c` is the holomorphic second iterate of the tricorn map
`Tantibar c`, hence a polynomial of degree `4`.  This file proves that its `m`-th iterate
`(Tsq c)^[m]`, restricted to the complement of the set of its **critical values**
`((Tsq c)^[m]) '' {z | deriv ((Tsq c)^[m]) z = 0}`, is a covering map (onto its image):
`IsCoveringMapOn ((Tsq c)^[m]) (critVals)ᶜ`.

This is the covering-map input of the pull-back argument (`polyPullback`): over a simply
connected region avoiding the critical values of the iterate, the map is a homeomorphism
onto its image, so the number of sheets is constant.

The proof is by identifying `(Tsq c)^[m]` with the evaluation of a polynomial
(`tsqPoly c` iterated by composition, `polyIter`), and then applying Mathlib's
`Polynomial.isCoveringMapOn_eval`, which states that every polynomial is a covering map on
the complement of the image of its critical points.
-/
import Mathlib
import Submission.Work.ELPull.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Polynomial

namespace Work.ELPull

/-- The polynomial `X ↦ (X² + c̄)² + c` whose evaluation is `Tsq c`. -/
def tsqPoly (c : ℂ) : ℂ[X] := (X ^ 2 + C (star c)) ^ 2 + C c

theorem tsqPoly_eval (c z : ℂ) : (tsqPoly c).eval z = Work.Landing.Tsq c z := by
  simp [tsqPoly, Work.Landing.Tsq]

/-- The `m`-fold composite `p ∘ p ∘ ⋯ ∘ p` (`m` times), as a polynomial; `polyIter p 0 = X`. -/
def polyIter (p : ℂ[X]) (m : ℕ) : ℂ[X] := ((fun q : ℂ[X] => p.comp q)^[m]) X

@[simp] theorem polyIter_zero (p : ℂ[X]) : polyIter p 0 = X := rfl

theorem polyIter_succ (p : ℂ[X]) (m : ℕ) : polyIter p (m + 1) = p.comp (polyIter p m) := by
  simp [polyIter, Function.iterate_succ_apply']

/-- Evaluation of `polyIter p m` is the `m`-th iterate of the evaluation of `p`. -/
theorem polyIter_eval (p : ℂ[X]) (m : ℕ) (z : ℂ) :
    (polyIter p m).eval z = (fun w => p.eval w)^[m] z := by
  induction m with
  | zero => simp [polyIter]
  | succ m ih =>
    rw [Function.iterate_succ_apply', polyIter_succ, Polynomial.eval_comp, ih]

/-- The `m`-th iterate of `Tsq c` is the evaluation of the polynomial `polyIter (tsqPoly c) m`. -/
theorem tsqIterate_eq_polyIter_eval (c : ℂ) (m : ℕ) :
    (Work.Landing.Tsq c)^[m] = fun z => (polyIter (tsqPoly c) m).eval z := by
  funext z
  induction m with
  | zero => simp [polyIter]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, polyIter_succ, Polynomial.eval_comp, tsqPoly_eval]

/-- The `m`-th iterate of `Tsq c` is a covering map off its critical values.  (The set
`((Tsq c)^[m]) '' {z | deriv ((Tsq c)^[m]) z = 0}` is the set of critical values of the
iterate.) -/
theorem isCoveringMapOn_tsqIterate (c : ℂ) (m : ℕ) :
    IsCoveringMapOn ((Work.Landing.Tsq c)^[m])
      (((Work.Landing.Tsq c)^[m]) '' {z : ℂ | deriv ((Work.Landing.Tsq c)^[m]) z = 0})ᶜ := by
  have hfun := tsqIterate_eq_polyIter_eval c m
  have hder : ∀ z : ℂ, deriv ((Work.Landing.Tsq c)^[m]) z
      = (polyIter (tsqPoly c) m).derivative.eval z := by
    intro z
    rw [hfun, Polynomial.deriv]
  have hset : {z : ℂ | deriv ((Work.Landing.Tsq c)^[m]) z = 0}
      = {z : ℂ | (polyIter (tsqPoly c) m).derivative.eval z = 0} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    rw [hder z]
  rw [hset, hfun]
  exact Polynomial.isCoveringMapOn_eval (polyIter (tsqPoly c) m)

/-- The covering property may be restricted to any subset of the regular values. -/
theorem isCoveringMapOn_tsqIterate_mono (c : ℂ) (m : ℕ) {s : Set ℂ}
    (hs : s ⊆
      (((Work.Landing.Tsq c)^[m]) '' {z : ℂ | deriv ((Work.Landing.Tsq c)^[m]) z = 0})ᶜ) :
    IsCoveringMapOn ((Work.Landing.Tsq c)^[m]) s :=
  (isCoveringMapOn_tsqIterate c m).mono hs

/-- Off the critical values, the derivative of the iterate does not vanish. -/
theorem deriv_tsqIterate_ne_zero (c : ℂ) (m : ℕ) {z : ℂ}
    (hz : ((Work.Landing.Tsq c)^[m]) z ∉
      ((Work.Landing.Tsq c)^[m]) '' {w : ℂ | deriv ((Work.Landing.Tsq c)^[m]) w = 0}) :
    deriv ((Work.Landing.Tsq c)^[m]) z ≠ 0 :=
  fun h => hz ⟨z, h, rfl⟩

/-- The iterate is a local homeomorphism off its critical values. -/
theorem isLocalHomeomorphOn_tsqIterate (c : ℂ) (m : ℕ) :
    IsLocalHomeomorphOn ((Work.Landing.Tsq c)^[m])
      (((Work.Landing.Tsq c)^[m]) ⁻¹'
        (((Work.Landing.Tsq c)^[m]) '' {z : ℂ | deriv ((Work.Landing.Tsq c)^[m]) z = 0})ᶜ) :=
  (isCoveringMapOn_tsqIterate c m).isLocalHomeomorphOn

/-- The `F c = (Tsq c)^[5]` form of `isCoveringMapOn_tsqIterate`. -/
theorem isCoveringMapOn_F (c : ℂ) :
    IsCoveringMapOn (F c) ((F c) '' {z : ℂ | deriv (F c) z = 0})ᶜ :=
  isCoveringMapOn_tsqIterate c 5

end Work.ELPull
