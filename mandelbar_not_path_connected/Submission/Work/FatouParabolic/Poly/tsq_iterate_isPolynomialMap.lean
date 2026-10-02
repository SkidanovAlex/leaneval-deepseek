/-
Copyright: subproject `Submission/Work/FatouParabolic/Poly/` of `mandelbar_not_path_connected`.

# `(Tsq c)^[m]` is a polynomial map of degree ≥ 2

The holomorphic second iterate of the antiholomorphic quadratic map `Tantibar c`,
`Tsq c z = (z² + c̄)² + c`, is the evaluation of the polynomial
`(X² + C c̄)² + C c` of degree `4` over `ℂ`.  Consequently every iterate
`(Tsq c)^[m]`, `m ≥ 1`, is a polynomial map of degree `4^m ≥ 4 ≥ 2`, i.e. an
element of the class `Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo`
that `Work.FatouParabolic.FatouParabolicInput` is stated for.

The iterate is realised by composing the polynomial with itself `m` times:
`iterPoly c m = (fun Q ↦ Q.comp (tsqPoly c))^[m] X`, so that
`(iterPoly c m).eval z = (Tsq c)^[m] z` and `(iterPoly c m).natDegree = 4 ^ m`.
-/
import Mathlib
import Submission.Work.FatouParabolic.Defs
import Submission.Work.LANDCL.Critical.not_isRepelling_criticalValue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Polynomial

namespace Work.FatouParabolic.Poly

noncomputable section

/-! ## `Tsq c` and its iterates as polynomials -/

/-- `Tsq c z = (z² + c̄)² + c` as a polynomial: `(X² + C c̄)² + C c`, of degree `4`. -/
def tsqPoly (c : ℂ) : ℂ[X] := (X ^ 2 + C (star c)) ^ 2 + C c

theorem tsqPoly_eval (c z : ℂ) : (tsqPoly c).eval z = Work.Landing.Tsq c z := by
  simp [tsqPoly, Work.Landing.Tsq]

theorem natDegree_tsqPoly (c : ℂ) : (tsqPoly c).natDegree = 4 := by
  have hA : (X ^ 2 + C (star c) : ℂ[X]).natDegree = 2 := by
    rw [natDegree_add_eq_left_of_natDegree_lt]
    · exact natDegree_X_pow 2
    · rw [natDegree_C]; norm_num
  have hpos : (C c : ℂ[X]).natDegree < ((X ^ 2 + C (star c))^2 : ℂ[X]).natDegree := by
    rw [natDegree_C, natDegree_pow, hA]; norm_num
  have hdeg : (tsqPoly c).natDegree = ((X ^ 2 + C (star c))^2 : ℂ[X]).natDegree := by
    unfold tsqPoly
    exact natDegree_add_eq_left_of_natDegree_lt hpos
  rw [hdeg, natDegree_pow, hA]

/-- The `m`-th iterate of `Tsq c`, realised as the `m`-fold self-composition of the polynomial
`tsqPoly c` (starting from `X`). -/
def iterPoly (c : ℂ) (m : ℕ) : ℂ[X] := (fun Q : ℂ[X] => Q.comp (tsqPoly c))^[m] X

theorem iterPoly_succ (c : ℂ) (n : ℕ) :
    iterPoly c (n + 1) = (iterPoly c n).comp (tsqPoly c) := by
  simp only [iterPoly, Function.iterate_succ_apply']

theorem iterPoly_eval (c : ℂ) (m : ℕ) :
    ∀ z : ℂ, (iterPoly c m).eval z = (Work.Landing.Tsq c)^[m] z := by
  induction m with
  | zero => intro z; simp [iterPoly]
  | succ n ih =>
      intro z
      rw [iterPoly_succ, Polynomial.eval_comp, tsqPoly_eval, ih, Function.iterate_succ_apply]

theorem natDegree_iterPoly (c : ℂ) (m : ℕ) : (iterPoly c m).natDegree = 4 ^ m := by
  induction m with
  | zero => simp [iterPoly]
  | succ n ih =>
      rw [iterPoly_succ, natDegree_comp, ih, natDegree_tsqPoly, pow_succ]

/-- **Every iterate `(Tsq c)^[m]`, `m ≥ 1`, is a polynomial map of degree at least two.**
Indeed `(Tsq c)^[m]` is the evaluation of `iterPoly c m`, whose `natDegree` is `4^m ≥ 4`. -/
theorem tsq_iterate_isPolynomialMap (c : ℂ) {m : ℕ} (hm : 1 ≤ m) :
    Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo ((Work.Landing.Tsq c)^[m]) := by
  refine ⟨iterPoly c m, ?_, ?_⟩
  · rw [natDegree_iterPoly]
    calc 2 ≤ 4 := by norm_num
      _ = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  · intro z
    exact (iterPoly_eval c m z).symm

end

end Work.FatouParabolic.Poly
