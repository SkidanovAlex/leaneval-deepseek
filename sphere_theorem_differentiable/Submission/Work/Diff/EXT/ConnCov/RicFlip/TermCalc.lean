import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.HonestFlip
import Submission.Work.Diff.EXT.ConnCov.RicFlip.HonestTower

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The term calculus for the two-connection flip (honest tower)

This file sets up the *term calculus* which turns the flip identity `pD_flip_full` into a bound.
It is stated for a generic **slot-additive** base `base : AMB.Fam 2` (in the intended application
`base = ric2 (G t)`, or `RicT (G t) i` itself); the invariant carried by every term is
`AMB.SlotAddP (evalT ·)` — slot additivity — together with smoothness on smooth tuples.

A *term* is either

* `leaf i` — the `i`-fold `pD`-iterated tower `pDiter2 (lcOf (G t)) base i : Fam (i+2)`;
* `comp Φ T` — the evaluation of the term `T` on the substitution `Φ` (`O.OSub (n+1) n ord`),
  i.e. `fun F => evalT T (Φ.eval G t F) : Fam (n+1)`.

The two expansion functions are

* `nextT T` — the terms whose evaluations sum to `pD (lcOf (G t)) (evalT T)`; its correctness is the
  **chain rule** (`OSubChainWeak`), used here as an explicit hypothesis `hchain`;
* `insStep T` — the terms whose evaluations sum to `AMB.Ins (deltaTens G t) (evalT T)`
  (`Ins_deltaTens_eq_sum`); here every slot `j : Fin N` occurs.

The hypotheses `hchain`, `hcomp`, `hatom_sm`, `hatom_add` are the four external inputs, each proved
(or being proved) in a sibling module; keeping them as hypotheses makes this file independent of the
order in which those land.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov.RicFlip

open Work.Diff.EXT.ConnCov.AMB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- **The terms** of the flip calculus for a tower of a `Fam 2` base. -/
inductive Term : ℕ → Type where
  | leaf (i : ℕ) : Term (i + 2)
  | comp {A B ord : ℕ} (Ψ : O.OSub A B ord) (T : Term B) : Term A

variable (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)

/-- The evaluation of a term. -/
noncomputable def evalT (base : AMB.Fam (I := I) (M := M) 2) :
    {n : ℕ} → Term n → AMB.Fam (I := I) (M := M) n
  | _, Term.leaf i => pDiter2 (Submission.Diff.lcOf (G t)) base i
  | _, Term.comp Φ T => fun F => evalT base T (Φ.eval G t F)

/-- **The `pD`-expansion of a term** (the "chain rule" step). -/
noncomputable def nextT : {n : ℕ} → Term n → List (Term (n + 1))
  | _, Term.leaf i => [Term.leaf (i + 1)]
  | _, Term.comp Φ T =>
      (nextT T).map (fun T' => Term.comp (O.OSub.shift Φ) T') ++ [Term.comp (O.OSub.deriv Φ) T]

/-- **The insertion expansion of a term**: insert the connection difference into every slot. -/
noncomputable def insStep {n : ℕ} (T : Term n) : List (Term (n + 1)) :=
  (List.finRange n).map (fun j => Term.comp (insSub n j) T)

/-- The evaluation of a list of terms as a sum. -/
noncomputable def evalList (base : AMB.Fam (I := I) (M := M) 2) {n : ℕ} (l : List (Term n)) :
    AMB.Fam (I := I) (M := M) n :=
  fun F x => (l.map (fun T => evalT G t base T F x)).sum

end Work.Diff.EXT.ConnCov.RicFlip
/-! ## The four external inputs

The correctness lemmas of this calculus (`nextT_correct`, `insStep_correct`, `boundT_correct`) are
stated with four explicit hypotheses, each supplied by a sibling module:

* `OSubChainWeak` — the chain rule `pD (Θ ∘ Φ) = (pD Θ) ∘ Φ.shift + Θ ∘ Φ.deriv`
  (hypothesis: `Θ` additive in the atom's slot `Φ.idx` only);
* `Bnd1CompOSub` — `Bnd1 X C → Bnd1 (X ∘ Φ) (C * (1 + V))` given `BndV (deltaTowerM G t ord) V`;
* `atomEval_smE` — smoothness of the atom on smooth fields;
* `deltaTowerM_addArg` — additivity of the `δ`-tower in all its slots (used to transport the
  `SlotAddP` invariant through the substitutions).

The statement of `nextT_correct` is

  `AMB.pD (lcOf (G t)) (evalT base T) F x = evalList base (nextT T) F x`

for `∀ i, SmE (F i)`, together with the invariant `SlotAddP (evalT base T)`; the statement of
`insStep_correct` is

  `AMB.Ins (deltaTens G t) (evalT base T) F x = evalList base (insStep T) F x`,

which is `Ins_deltaTens_eq_sum` followed by the definition of `insStep`.  The bound recursion is
`boundT (leaf i) = R i` and `boundT (comp Ψ T) = boundT T * (1 + Bm (ord Ψ))`, with correctness
`Bnd1 (evalT base T) (boundT T)` by `Bnd1CompOSub` (the leaves being bounded by hypothesis).

-/

