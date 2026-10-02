import Mathlib
import ChallengeDeps
import Submission.Work.Normal.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The tricorn (mandelbar): holomorphic second iterate

The mandelbar family `T̄_c(z) = (conj z)^2 + c` is antiholomorphic; its second iterate
`T̄_c ∘ T̄_c` is the quartic polynomial map `z ↦ (z^2 + conj c)^2 + c`, which is holomorphic.
Complex dynamics for `T̄_c` (Fatou and Julia sets, normal families) is therefore handled through
the holomorphic map `TantibarSq c`, and `TantibarSq c` is the map usually called `p_c` in the
literature on the tricorn (with `p_c(z) = (z^2 + \bar c)^2 + c`).

The bridge to the benchmark statement is `mandelbar_iff_criticalOrbitBounded`: the mandelbar is
the set of parameters for which the (critical) orbit of `0` under `TantibarSq c` is bounded.
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology Polynomial
open Polynomial

/-- The holomorphic second iterate of the antiholomorphic quadratic map `T̄_c`: the quartic
polynomial map `z ↦ (z^2 + conj c)^2 + c`. -/
def TantibarSq (c : ℂ) (z : ℂ) : ℂ := (z ^ 2 + starRingEnd ℂ c) ^ 2 + c

theorem tantibar_comp_self (c : ℂ) :
    LeanEval.ComplexAnalysis.Tantibar c ∘ LeanEval.ComplexAnalysis.Tantibar c = TantibarSq c := by
  funext z
  simp only [Function.comp_apply, TantibarSq, LeanEval.ComplexAnalysis.Tantibar, map_add, map_pow,
    starRingEnd_apply, star_star]

theorem tantibar_iterate_two (c : ℂ) :
    (LeanEval.ComplexAnalysis.Tantibar c)^[2] = TantibarSq c := by
  have h : (LeanEval.ComplexAnalysis.Tantibar c)^[2]
      = LeanEval.ComplexAnalysis.Tantibar c ∘ LeanEval.ComplexAnalysis.Tantibar c := by
    funext z
    simp [Function.iterate_succ]
  rw [h, tantibar_comp_self]

/-- `TantibarSq c` is a monic polynomial map of degree `4`. -/
theorem isPolynomialMapOfDegree_tantibarSq (c : ℂ) :
    IsPolynomialMapOfDegree 4 (TantibarSq c) := by
  refine ⟨X ^ 4 + C (2 * starRingEnd ℂ c) * X ^ 2
      + C (c + (starRingEnd ℂ c) ^ 2), ?_, ?_⟩
  · compute_degree!
  · intro z
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, TantibarSq]
    ring

/-- The iterates of the antiholomorphic map `T̄_c` at even times are the iterates of the
holomorphic quartic `TantibarSq c`. -/
theorem tantibar_iterate_even (c : ℂ) (n : ℕ) :
    (LeanEval.ComplexAnalysis.Tantibar c)^[2 * n] = (TantibarSq c)^[n] := by
  rw [Function.iterate_mul (f := LeanEval.ComplexAnalysis.Tantibar c) 2 n, tantibar_iterate_two]

/-- The antiholomorphic quadratic map `T̄_c` is continuous and tends to `∞` at `∞`. -/
theorem isCoerciveContinuous_tantibar (c : ℂ) :
    IsCoerciveContinuous (LeanEval.ComplexAnalysis.Tantibar c) := by
  constructor
  · exact (continuous_star.pow 2).add continuous_const
  · intro R
    refine ⟨|R| + ‖c‖ + 1, fun z hz => ?_⟩
    have hz1 : 1 ≤ ‖z‖ := by
      have h : 0 ≤ |R| + ‖c‖ := by positivity
      linarith
    have hnorm : ‖(starRingEnd ℂ z) ^ 2‖ = ‖z‖ ^ 2 := by
      rw [norm_pow, starRingEnd_apply, norm_star]
    have h2 : ‖z‖ ^ 2 ≤ ‖LeanEval.ComplexAnalysis.Tantibar c z‖ + ‖c‖ := by
      have h := norm_sub_le (LeanEval.ComplexAnalysis.Tantibar c z) c
      rw [show LeanEval.ComplexAnalysis.Tantibar c z - c = (starRingEnd ℂ z) ^ 2 from by
        simp [LeanEval.ComplexAnalysis.Tantibar], hnorm] at h
      linarith
    have h3 : ‖z‖ - 1 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z, hz1]
    have h5 : R ≤ |R| := le_abs_self R
    linarith

end Work.Normal
