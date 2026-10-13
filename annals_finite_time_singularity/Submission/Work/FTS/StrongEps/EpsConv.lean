/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsConv.lean` — the convergence package of the extraction

`Work.FTS.StrongEps.exists_locUnif_subseq_of_uniform_H6` produces, from a sequence of profiles with a
uniform `ℋ⁶`-bound, a subsequence and a limit with

* *local uniform convergence of the profiles* on the open quadrant,
* `C⁴` of the limit,
* the `ℋ⁶`-bound of the limit.

Its proof works with the *slot* families `mixed j i (G n)` (`j + i ≤ 4`) throughout (the extraction
`LocUnif.exists_subseq_deriv4_of_uniform_H6` gives their convergence, and the a.e. level-`5` step
`LocUnif.exists_subseq_deriv5_ae` uses it), but the *conclusion* only re-exposes the level-`0`
convergence.  This module names the full package — the one the identification step
(`Jeps_tendsto_of_tendsto` + continuity of `rhsFun`) and the passage to the limit of the equation
consume — so that the two extraction bricks of E5 can be stated against it:

* `exists_subseq_slots` — the extraction with the slot convergence in the conclusion;
* `exists_subseq_rat` — the diagonal of that extraction over the *fake times* `τ ∈ [0,T] ∩ ℚ`
  (needed because the extraction is a *profile*-level statement and E5's limit is a *family*);

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.Basic

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

/-- **The convergence package of the extraction.**  `ConvLocUnifH6 α B G f` says that the profiles
`G n` converge to `f` locally uniformly on the open quadrant *together with every slot of order
`≤ 4`*, that `f` is `C⁴` there, and that the `ℋ⁶`-bound of the sequence passes to the limit.

The slot clause is what `LocUnif.exists_subseq_deriv4_of_uniform_H6` produces; re-exposing it here
is what lets the limit of the *equation* be identified slot by slot. -/
def ConvLocUnifH6 (α B : ℝ) (G : ℕ → Fn) (f : Fn) : Prop :=
  (∀ (K : Set (ℝ × ℝ)), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ (j i : ℕ), j + i ≤ 4 →
        TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G n) p.1 p.2)
          (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K) ∧
    ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 ∧
    Work.Spaces.HkNorm α 6 f ≤ B

/-- The slot-convergence clause of `ConvLocUnifH6`, unbundled. -/
theorem ConvLocUnifH6.conv {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLocUnifH6 α B G f) :
    ∀ (K : Set (ℝ × ℝ)), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ (j i : ℕ), j + i ≤ 4 →
        TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G n) p.1 p.2)
          (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K := h.1

/-- The `C⁴`-clause of `ConvLocUnifH6`. -/
theorem ConvLocUnifH6.contDiffOn {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLocUnifH6 α B G f) :
    ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 := h.2.1

/-- The `ℋ⁶`-clause of `ConvLocUnifH6`. -/
theorem ConvLocUnifH6.hkNorm_le {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLocUnifH6 α B G f) :
    Work.Spaces.HkNorm α 6 f ≤ B := h.2.2

end Work.FTS.StrongEps
