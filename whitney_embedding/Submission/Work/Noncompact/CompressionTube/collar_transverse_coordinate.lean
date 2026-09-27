import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.collar_defs
import Submission.Work.Noncompact.CompressionTube.ctc.final

/-!
# A global transverse coordinate for a properly embedded line

Target: `Work.Noncompact.CompressionTube.collar_transverse_coordinate`.

Given a smooth proper embedding `γ : ℝ → M` of a line into a smooth `n`-manifold (`n ≥ 2`) and a
smooth `g : M → ℝ` with `g (γ s) = s`, we produce a smooth `P : M → ℝ^{n-1}` with `P (γ s) = 0`
whose differential together with `dg` is invertible at every point of the line.

The vocabulary (`Transverse` and the three elementary lemmas about it) lives in `collar_defs`; the
construction itself lives in the `ctc/` modules, which import `collar_defs` only -- this is what
allows the present file to import them without a cycle:

* `ctc.exists_transverse_on_Icc` : global smooth pieces transverse on a prescribed compact interval;
* `ctc.exists_gauge` / `ctc.exists_transverse_blend` : the linear gauge matching two transversals at
  a point, and the blend of two pieces with the same differential at a point;
* `ctc.step_core` : one step of the recursion (blend the current piece with a gauge-corrected raw
  piece, gaining a window of transversality to the right while keeping the old piece on the left);
* `ctc.final` : the raw family, the forward recursion, the reflected recursion (which supplies the
  pieces on the other half of the line), and the final assembly, in which the piece used at a point
  `x` is the one indexed by the integer part of `g x + 1/4`.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function

noncomputable section

theorem collar_transverse_coordinate {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ) (hinj : Function.Injective γ)
    (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv MCreal (MC n) γ s))
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g) (hgcore : ∀ s : ℝ, g (γ s) = s) :
    ∃ P : M → EuclideanSpace ℝ (Fin (n - 1)), ContMDiff (MC n) (MC (n - 1)) smoothOrder P ∧
      (∀ s : ℝ, P (γ s) = 0) ∧
      ∀ s : ℝ, ∀ v : TangentSpace (MC n) (γ s),
        mfderiv (MC n) (MC (n - 1)) P (γ s) v = 0 →
        mfderiv (MC n) MCreal g (γ s) v = 0 → v = 0 := by
  exact exists_global_transverse_coordinate (n := n) hn hγ hinj hprop himm hg hgcore

end

end Work.Noncompact.CompressionTube
