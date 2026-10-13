import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.H2.QangDiff
import Submission.Work.FTS.H2.QangBox

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.RNP24

/-- **The iterated `z ∂_z` of the angular moment `(g, K)` is the `b`-th angular moment.**

`FK g z = ∫_θ K(θ) g z θ dθ` is `Qang g 0`, and `Qang g j` differentiates to
`Qang g (j+1) z / z` (`Work.FTS.H2.hasDerivAt_Qang`, available for `j ≤ 2` from
`SmoothQuad g` and `HkMem α 4 g` alone — no bound on `α` is needed, since the primitive
identity `Qang_primitive` and the continuity `continuousOn_Qang` are proved in the interior
class).  Hence `Dzd = z ∂_z` raises the angular index by one and the induction on `b ≤ 3`
gives `DzdIter b (FK g) = Qang g b` on `(0,∞)`. -/
theorem dzdIter_FK_eq_qang {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0:ℝ),
      Work.Elliptic.DzdIter b (Work.Construction.FK g) z = Work.Elliptic.Qang g b z := by
  have hcont : ∀ j : ℕ, j ≤ 3 →
      ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0) :=
    fun j hj => Work.FTS.H2.continuousOn_Qang α g hsm hmem hj
  -- `FK g` is the `0`-th angular moment: `Qang g 0 z = ∫_θ Ktheta θ · g z θ dθ`.
  have hFK : ∀ z : ℝ, Work.Construction.FK g z = Work.Elliptic.Qang g 0 z := by
    intro z
    rw [Work.Construction.FK, Work.Elliptic.Qang]
    refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [Work.Elliptic.Ktheta_eq_K]
    simp only [Work.Spaces.DzIter_zero]
    ring
  intro b
  induction b with
  | zero => intro _ z _; exact hFK z
  | succ b ih =>
      intro hb z hz
      have hbz : b ≤ 3 := by omega
      -- the two functions agree on the neighbourhood `Ioi 0` of `z`, hence their derivatives
      -- at `z` agree
      have hderiv : deriv (Work.Elliptic.DzdIter b (Work.Construction.FK g)) z
          = Work.Elliptic.Qang g (b + 1) z / z := by
        have heq : Work.Elliptic.DzdIter b (Work.Construction.FK g) =ᶠ[𝓝 z]
            Work.Elliptic.Qang g b := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
          exact ih hbz w hw
        rw [heq.deriv_eq]
        exact (Work.FTS.H2.hasDerivAt_Qang α g hsm hmem (by omega : b ≤ 2) hz
          (hcont (b+1) (by omega))).deriv
      rw [Work.Elliptic.DzdIter_succ]
      show z * deriv (Work.Elliptic.DzdIter b (Work.Construction.FK g)) z
        = Work.Elliptic.Qang g (b+1) z
      rw [hderiv]
      have hz0 : z ≠ 0 := ne_of_gt hz
      exact mul_div_cancel₀ _ hz0

end Work.FTS.Nonlinear.Pieces.RNP.RNP24
