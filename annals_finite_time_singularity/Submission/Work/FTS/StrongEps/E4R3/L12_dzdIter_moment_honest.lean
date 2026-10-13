import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.StrongEps.E4R3.Qang_sq_le_const_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3

theorem L12_dzdIter_moment_honest (α : ℝ) {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (h0 : Work.Construction.L12 g 0 = 0) :
    (∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 g z) z
        = - Work.Elliptic.Qang g k z)
    ∧ (∀ b : ℕ, b ≤ 3 → ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z)) z) := by
  -- The index-raising recursion `D_z^{k+1} L₁₂(g) = - Qang g k` (`k ≤ 3`) and the weighted
  -- integrability of `L₁₂(g)² w²` are the output of the open-quadrant `L₁₂`-bundle.  Note
  -- `Work.Construction.L12 = Work.Elliptic.L12` definitionally (`rfl`).
  have hbundle := Work.FTS.OpenPkg.l12_open_bundle α g hα hα1 hsm hmem h0
  have hrec : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 g z) z
        = - Work.Elliptic.Qang g k z :=
    fun k hk z hz => hbundle.1 k hk z hz
  -- `Qang g j` is differentiable on `(0,∞)` for `j ≤ 2`, with `∂_z Qang g j = Qang g (j+1)/z`.
  have hQdiff : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      HasDerivAt (Work.Elliptic.Qang g j) (Work.Elliptic.Qang g (j + 1) z / z) z :=
    (Work.FTS.OpenPkg.QangOpen.QangDiff_open α g hα hα1 hsm hmem).1
  refine ⟨hrec, ?_⟩
  intro b hb3 z hz
  rcases b with _ | c
  · -- `b = 0`: `L₁₂(g)` has derivative `-3·F_*(g)(z)/z` at `z > 0`.
    have hd : HasDerivAt (Work.Elliptic.L12 g) (-(3 * Work.Elliptic.Fstar g z / z)) z :=
      (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 4 g hsm hmem
        (by norm_num)).2 z hz
    exact hd.differentiableAt
  · -- `b = c + 1`, `c ≤ 2`: on the open half-line `D_z^{c+1} L₁₂(g) = - Qang g c`, and the
    -- angular moment `Qang g c` is differentiable there.
    have hc : c ≤ 2 := by omega
    have hev : Work.Elliptic.DzdIter (c + 1) (fun z => Work.Construction.L12 g z)
        =ᶠ[nhds z] fun u => - Work.Elliptic.Qang g c u := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
      exact hrec c (by omega) u hu
    exact ((hQdiff c hc z hz).differentiableAt.neg).congr_of_eventuallyEq hev

end Work.FTS.StrongEps.E4R3
