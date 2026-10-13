import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-- **The recurrence `D_z^{k+1} L₁₂(g) = -Qang g k` up to `k = 6`.**

`L₁₂(g)(z) = ∫_z^∞ L12dens g r dr` and `L12dens g r = Qang g 0 r / r`, so the fundamental
theorem of calculus gives the case `k = 0` (the differentiability of `L₁₂(g)` on `(0,∞)` is
`UopHk.contDiffOn_L12_of_smoothOpen_Hk`, whose only hypotheses are `SmoothOpen g` and
`HkMem α 6 g`), and the induction step differentiates the identity `D_z^{k+1} L₁₂(g) = -Qang g k`
near `z` using the supplied chain rule `∂_z (Qang g k) z = Qang g (k+1) z / z`. -/
theorem L12Rec7 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g)
    (hqder : ∀ j : ℕ, j ≤ 5 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang g j w) (Work.Elliptic.Qang g (j + 1) z / z) z) :
    ∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (fun z => Work.Elliptic.L12 g z) z = - Work.Elliptic.Qang g k z := by
  -- the derivative of `L₁₂(g)`, from `L₁₂(g) = 3 ∫_z^∞ F_*(r)/r dr`
  have hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.L12 g z) (-(Work.Elliptic.L12dens g z)) z := by
    intro z hz
    have h12 := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 6 g hO hmem
      (by norm_num : 2 ≤ 6)).2
    refine (h12 z hz).congr_deriv ?_
    rw [Work.Elliptic.L12dens_eq_three_Fstar_div]
    ring
  intro k
  induction k with
  | zero =>
      intro _ z hz
      have hd : deriv (fun z => Work.Elliptic.L12 g z) z = -(Work.Elliptic.L12dens g z) :=
        (hderiv z hz).deriv
      change z * deriv (fun z => Work.Elliptic.L12 g z) z = - Work.Elliptic.Qang g 0 z
      rw [hd, Work.Elliptic.L12dens_eq_Qang_div, mul_neg, neg_inj,
        mul_div_cancel₀ _ (ne_of_gt hz)]
  | succ n ih =>
      intro hn z hz
      have hev : Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)
          =ᶠ[𝓝 z] (fun z' => - Work.Elliptic.Qang g n z') := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih (by omega) z' hz'
      have hdv : deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)) z
          = - deriv (fun z' => Work.Elliptic.Qang g n z') z := by
        rw [hev.deriv_eq]
        exact deriv.neg
      change z * deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)) z
          = - Work.Elliptic.Qang g (n + 1) z
      rw [hdv, mul_neg, neg_inj, (hqder n (by omega) z hz).deriv,
        mul_div_cancel₀ _ (ne_of_gt hz)]

end Work.FTS.StrongPersist.H6Pair6Aux
