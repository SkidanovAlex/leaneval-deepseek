import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.flatActBasic
import Submission.Work.Mostow.flatSmulLevelIndep
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.horoActTrivId
import Submission.Work.Mostow.nfDefs
import Submission.Work.Mostow.Hyper

/-!
# An isometry fixing a boundary point, a horosphere level and the flat `ξ^⊥` is the identity

Let `g : PO(n,1)` fix `ξ ∈ Sph n` on the boundary (`bd g ξ = ξ`), preserve the horospherical
level (`lev ξ (g • 0) = 1`) and act trivially on the flat coordinate `ξ^⊥`
(`flatAct ξ g y = y` for `y ⊥ ξ`). Then `g = 1`.

The proof reduces to `Work.Mostow.horoActTrivId`, which says that an isometry fixing `ξ`,
preserving every horospherical level at `ξ` and fixing one horosphere pointwise is the identity.
Both hypotheses are immediate here:

* `lev_smul_self` writes `lev ξ (g • u) = lev ξ u * lev ξ (g • 0)`, and the second factor is `1`
  by hypothesis, so the levels are preserved;
* a point `u` with `lev ξ u = 1` is `horoPt ξ (yc ξ u)` (`hptOf_yc`), the level-one horosphere
  point of the flat coordinate `yc ξ u`; `flatAct_horoPt` moves this to
  `horoPt ξ (flatAct ξ g (yc ξ u))`, and `hfix` collapses the flat coordinate back to `yc ξ u`.
-/

namespace Work.Mostow.Margulis

open Submission.Mostow LeanEval.Geometry.MostowRigidity

theorem eq_one_of_flatAct_fix (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n)
    {g : LeanEval.Geometry.MostowRigidity.PO n 1} (hg : Submission.Mostow.bd g ξ = ξ)
    (h0 : Work.Mostow.lev ξ (g • (0 : Submission.Mostow.E n)) = 1)
    (hfix : ∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 → Work.Mostow.flatAct ξ g y = y) :
    g = 1 := by
  have hA' : Work.Mostow.POBasic n := Work.Mostow.POBasic.ofProp hA
  have hI' : Work.Mostow.HypIsoData n := Work.Mostow.HypIsoData.ofProp hI
  -- `g` preserves every horospherical level at `ξ`
  have hlev : ∀ u : Submission.Mostow.E n, Work.Mostow.lev ξ (g • u) = Work.Mostow.lev ξ u := by
    intro u
    rw [Work.Mostow.lev_smul_self hI' hA' ξ hξ g u hg, h0, mul_one]
  -- `g` fixes the level-one horosphere of `ξ` pointwise
  have htriv : ∀ u : Submission.Mostow.E n, Work.Mostow.lev ξ u = 1 → g • u = u := by
    intro u hu
    have hy : inner ℝ (Work.Mostow.yc ξ u) ξ = 0 := Work.Mostow.yc_inner_orth hξ
    have hkey := Work.Mostow.flatAct_horoPt (n := n) hξ hA' hI' hg h0 hy
    rw [hfix (Work.Mostow.yc ξ u) hy] at hkey
    have hu' : u = Work.Mostow.horoPt ξ (Work.Mostow.yc ξ u) := by
      rw [Work.Mostow.horoPt_eq_hptOf]
      exact (Work.Mostow.hptOf_yc ξ hξ 1 one_pos u hu).symm
    rw [hu']
    exact hkey
  exact Work.Mostow.horoActTrivId hA g ξ hξ 1 one_pos hg hlev htriv

end Work.Mostow.Margulis
