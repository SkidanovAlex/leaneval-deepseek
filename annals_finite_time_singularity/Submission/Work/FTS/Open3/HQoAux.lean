/-
# `FTS/Open3/HQoAux` — the algebraic closure of the open class `HQo α k`

`HQo α k f = SmoothOpen f ∧ HkMem α k f` (`Work.FTS.VocabO`) is the class on which the corrected
pairing clauses `IPLinHQo` and the corrected regularity hypotheses of the Open3 chain are stated.
Unlike `RegQ α k` (which asks `SmoothQuad`, i.e. `C^∞` through `z = 0`), it is closed under the
algebraic operations of the Galerkin scheme on the `HQo` side of the equation: this module records
that closure, so that consumer code can form `dynLin + dynRHS`, `gdot - RHS`, scalar multiples and
differences without leaving the class.

The `HkMem` half is `Work.FTS.CoercivityFix.Assembly.HkMem_add_open` (which needs the `SmoothOpen`
of both summands) and `Work.FTS.LocData.HkMem_const_mul`; the `SmoothOpen` half is
`Work.FTS.EllipticEst.smoothOpen_add` and `ContDiffOn.const_smul`/`neg`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.Open3.Defs3
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.EllipticEst.HkIntegrand_add_le_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.Open3

open Work.FTS.Nonlin
open Work.FTS.VocabO (HQo)
open Work.FTS.Galerkin (Fn Fam)

set_option autoImplicit false

/-- `SmoothOpen` is preserved by multiplication by a constant. -/
theorem smoothOpen_const_mul {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  have h : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.const_smul c

/-- `HQo` is closed under multiplication by a constant. -/
theorem HQo_const_mul {α : ℝ} {k : ℕ} {f : Fn} (hf : HQo α k f) (c : ℝ) :
    HQo α k (fun z θ => c * f z θ) :=
  ⟨smoothOpen_const_mul hf.1 c, Work.FTS.LocData.HkMem_const_mul α k c hf.2⟩

/-- `HQo` is closed under negation. -/
theorem HQo_neg {α : ℝ} {k : ℕ} {f : Fn} (hf : HQo α k f) : HQo α k (fun z θ => -f z θ) := by
  have hfun : (fun z θ => -f z θ) = fun z θ => (-1 : ℝ) * f z θ := by funext z θ; ring
  rw [hfun]
  exact HQo_const_mul hf (-1)

/-- `HQo` is closed under addition. -/
theorem HQo_add {α : ℝ} {k : ℕ} {f g : Fn} (hf : HQo α k f) (hg : HQo α k g) :
    HQo α k (fun z θ => f z θ + g z θ) :=
  ⟨Work.FTS.EllipticEst.smoothOpen_add hf.1 hg.1,
   Work.FTS.CoercivityFix.Assembly.HkMem_add_open α k hf.1 hg.1 hf.2 hg.2⟩

/-- `HQo` is closed under subtraction. -/
theorem HQo_sub {α : ℝ} {k : ℕ} {f g : Fn} (hf : HQo α k f) (hg : HQo α k g) :
    HQo α k (fun z θ => f z θ - g z θ) := by
  have hfun : (fun z θ => f z θ - g z θ) = fun z θ => f z θ + -g z θ := by funext z θ; ring
  rw [hfun]
  exact HQo_add hf (HQo_neg hg)

/-- The sum of two functions in `HQo` is again in `HQo`, with the summands in the order produced by
the `Finset`-sum bookkeeping of the Galerkin scheme. -/
theorem HQo_finset_sum {α : ℝ} {k : ℕ} {ι : Type*} (s : Finset ι) {F : ι → Fn}
    (hF : ∀ i ∈ s, HQo α k (F i)) : HQo α k (fun z θ => ∑ i ∈ s, F i z θ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun z θ => ∑ i ∈ (∅ : Finset ι), F i z θ) = fun _ _ : ℝ => (0 : ℝ) := by
        funext z θ; simp
      rw [h0]
      exact Work.FTS.OpenPkg.HQo_of_RegQ (Work.FTS.CoercivityFix.Assembly.regQ_zero α k)
  | insert a s ha ih =>
      have ha' : HQo α k (F a) := hF a (Finset.mem_insert_self a s)
      have hs' : HQo α k (fun z θ => ∑ i ∈ s, F i z θ) :=
        ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hsum : (fun z θ => ∑ i ∈ insert a s, F i z θ)
          = fun z θ => F a z θ + ∑ i ∈ s, F i z θ := by
        funext z θ; rw [Finset.sum_insert ha]
      rw [hsum]
      exact HQo_add ha' hs'

end Work.FTS.Open3
