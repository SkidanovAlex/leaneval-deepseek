/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/ConvLev0Defs.lean` — the level-`0` limit package of `E5`

`Work.FTS.StrongEps.ConvLocUnifH6` (`EpsConv.lean`) bundles, for a sequence of profiles `G n`,
the *local uniform convergence of every slot* `mixed j i` of order `j + i ≤ 4`, the `C⁴`-regularity
of the limit and its (honest) `ℋ⁶`-bound.  Its slot clause is what the level-5 a.e. extraction
produces, and it is the natural package for the *single-time* extraction `EpsConvSubseq`.

For the passage from the rational times to *all* fake times (`EpsConvAllH`, `EpsConvLev0`) the
slot-wise clause is expensive: a τ-uniform Lipschitz bound for the slots of order `≤ 4` requires
pointwise control of the slots of the scheme's right-hand side of order `≤ 4`, i.e. (by Morrey)
an `ℋ⁷`-size of the slices, while the design's state space is `ℋ⁶` (`NOTES.md`, addendum of the
sixth stretch, §2).  The *level-`0`* clause, on the other hand, only needs a pointwise bound on the
right-hand side itself, which is priced by `L3Data` at `ℋ³`.

This module therefore records the weaker package

* `ConvLev0H6 α B G f` — local uniform convergence of the *profiles*, `C⁴` of the limit, and its
  `ℋ⁶`-bound (the *honest* one: the sequence's `HkMem`/`HkNorm` data are hypotheses of the lemmas
  that use it, and the bound of the limit is produced by a single-time extraction, hence is not a
  junk clause).

Nothing here is an obligation: the module only fixes the vocabulary.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.EpsConv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The level-`0` limit package.**  The profiles `G n` converge to `f` locally uniformly on the
open quadrant `Q0`, `f` is `C⁴` there, and `HkNorm α 6 f ≤ B`.

This is `ConvLocUnifH6` with the slot clause weakened to the `(0,0)`-slot; it is the package that
the coherent limit *family* of `E5` is built from (the remaining slots are recovered at each fake
time separately, by a fresh extraction). -/
def ConvLev0H6 (α B : ℝ) (G : ℕ → Fn) (f : Fn) : Prop :=
  (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
    TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G n p.1 p.2) (fun p => f p.1 p.2) Filter.atTop K) ∧
  ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 ∧
  Work.Spaces.HkNorm α 6 f ≤ B

/-- The level-`0` convergence clause, unbundled. -/
theorem ConvLev0H6.conv {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLev0H6 α B G f) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G n p.1 p.2) (fun p => f p.1 p.2)
        Filter.atTop K := h.1

/-- The `C⁴`-clause of `ConvLev0H6`. -/
theorem ConvLev0H6.contDiffOn {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLev0H6 α B G f) :
    ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 := h.2.1

/-- The `ℋ⁶`-bound of `ConvLev0H6`. -/
theorem ConvLev0H6.hkNorm_le {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLev0H6 α B G f) :
    Work.Spaces.HkNorm α 6 f ≤ B := h.2.2

/-- `ConvLocUnifH6` is stronger: it implies `ConvLev0H6` (its slot clause at `(0,0)` is the
level-`0` convergence). -/
theorem ConvLocUnifH6.toLev0 {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLocUnifH6 α B G f) :
    ConvLev0H6 α B G f :=
  ⟨fun K hK hKQ => h.1 K hK hKQ 0 0 (by norm_num), h.2.1, h.2.2⟩

end Work.FTS.StrongEps
