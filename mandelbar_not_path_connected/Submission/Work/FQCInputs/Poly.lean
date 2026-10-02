/-
# `Work.FQCInputs.Poly` — the tenth iterate `F c` as a polynomial function

The Leau–Fatou input (`SimpleTransfer.lean`) is stated for *polynomial* maps: the global
statement "the parabolic basin has exactly `ν = multiplicity − 1` components accumulating at the
parabolic point" is a theorem about rational (in particular polynomial) maps, whereas for an
arbitrary entire extension of a parabolic germ the global component structure of the basin is
not controlled by the germ.

This file records that `F c = (Tsq c)^[5] = (TsqP c)^[5]` is the value function of an explicit
polynomial, so that the input can be applied to `F c` and to `F c₂`.
-/
import Mathlib
import Submission.Work.FQC.Flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

set_option linter.unusedVariables false

noncomputable section

namespace Work.FQCInputs

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F)

/-- The polynomial whose value function is `Work.FQC.TsqP c`, i.e. the holomorphic second
iterate of the antipolynomial: `z ↦ (z² + conj c)² + c`. -/
def polyTsq (c : ℂ) : Polynomial ℂ :=
  (Polynomial.X ^ 2 + Polynomial.C (star c)) ^ 2 + Polynomial.C c

theorem polyTsq_eval (c : ℂ) (z : ℂ) : (polyTsq c).eval z = Work.FQC.TsqP c z := by
  simp [polyTsq, Work.FQC.TsqP]

/-- **Every iterate of a polynomial value function is a polynomial value function.** -/
theorem exists_poly_iterate (q : Polynomial ℂ) (n : ℕ) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, p.eval z = (fun z => q.eval z)^[n] z := by
  induction n with
  | zero => exact ⟨Polynomial.X, fun z => by simp⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨p.comp q, fun z => by
      rw [Polynomial.eval_comp, hp (q.eval z)]
      simp [Function.iterate_succ_apply]⟩

/-- **`F c` is a polynomial map.** -/
theorem exists_poly_F (c : ℂ) : ∃ p : Polynomial ℂ, F c = fun z => p.eval z := by
  have hfun : (fun z => (polyTsq c).eval z) = Work.FQC.TsqP c := by
    funext z
    exact polyTsq_eval c z
  obtain ⟨p, hp⟩ := exists_poly_iterate (polyTsq c) 5
  refine ⟨p, ?_⟩
  rw [Work.FQC.F_eq_poly c, ← hfun]
  funext z
  exact (hp z).symm

end Work.FQCInputs

end
