import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E5Aux.contDiffOn_two_of_locUnif_slots
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.mul_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.StrongEps.E5Aux3

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Reduction to *locally uniform* convergence of the jets

The target lemma is the `C²`-clause of the E5 limit extraction: the pointwise limit of the jets
(`mixed j i`, `j + i ≤ 2`) of a sequence of `C^∞` functions on the open quadrant, *together with*
a locally uniform bound on the jets of order `≤ 3`, is `C²`.

The already delivered theorem `Work.FTS.StrongEps.E5Aux.contDiffOn_two_of_locUnif_slots` proves
the corresponding statement for *locally uniform* convergence of the jets (order `≤ 2`).  So it
suffices to upgrade the pointwise convergence of the hypotheses to locally uniform convergence
on compacta.  The point is that the bound on the order-`3` jets makes the order-`≤ 2` jets
*equi-Lipschitz* on compact subsets of the quadrant (the `D_z`/`D_θ`-derivatives of a slot
`D_z^jD_θ^i u` are again slots of `u`, of order `j + i + 1`:
`∂_z(D_z^jD_θ^i u) = D_z^{j+1}D_θ^i u / z` by definition and
`∂_θ(D_z^jD_θ^i u) = D_z^jD_θ^{i+1} u / sin(2θ)` by Clairaut), and equi-Lipschitz plus pointwise
convergence on a compact set gives uniform convergence. -/


/-- `D_z^j` of a product with a function of `θ` alone: the factor comes out. -/
theorem DzIter_theta_mul (c : ℝ → ℝ) (w : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => c θ * w z θ)
      = fun z θ => c θ * Work.Spaces.DzIter j w z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      show z * Work.Spaces.pz (fun z θ => c θ * Work.Spaces.DzIter j w z θ) z θ
        = c θ * (z * Work.Spaces.pz (Work.Spaces.DzIter j w) z θ)
      show z * deriv (fun z' => c θ * Work.Spaces.DzIter j w z' θ) z
        = c θ * (z * deriv (fun z' => Work.Spaces.DzIter j w z' θ) z)
      rw [deriv_const_mul_field]
      ring

/-- The slot `D_z^jD_θ^{i+1} u` written through `D_z^j(∂_θ D_θ^i u)`. -/
theorem mixed_succ_right_eq (u : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j (i + 1) u
      = fun z θ => Real.sin (2 * θ)
          * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i u)) z θ := by
  have h1 : Work.Spaces.mixed j (i + 1) u
      = Work.Spaces.DzIter j (fun z θ => Real.sin (2 * θ)
          * Work.Spaces.pth (Work.Spaces.DthIter i u) z θ) := rfl
  rw [h1, DzIter_theta_mul (fun θ => Real.sin (2 * θ))
    (Work.Spaces.pth (Work.Spaces.DthIter i u)) j]

/-- **`∂_θ` of a slot.**  On the open quadrant, the angular derivative of the slot
`D_z^jD_θ^i u` is the next slot `D_z^jD_θ^{i+1} u` divided by `sin(2θ)`. -/
theorem pth_mixed_eq {u : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen u) (j i : ℕ) :
    ∀ p ∈ Work.FTS.EllipticEst.Q0,
      Work.Spaces.pth (Work.Spaces.mixed j i u) p.1 p.2
        = Work.Spaces.mixed j (i + 1) u p.1 p.2 / Real.sin (2 * p.2) := by
  have hDth : ∀ m : ℕ, ContDiffOn ℝ m (Function.uncurry (Work.Spaces.DthIter i u))
      Work.FTS.EllipticEst.Q0 := fun m => (hsm.DthIter i).forall m
  intro p hp
  have hsin : Real.sin (2 * p.2) ≠ 0 := by
    have hθ := (Work.FTS.EllipticEst.mem_Q0.mp hp).2
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have h1 : Work.Spaces.pth (Work.Spaces.mixed j i u) p.1 p.2
      = Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i u)) p.1 p.2 :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 hDth j hp
  have h2 : Work.Spaces.mixed j (i + 1) u p.1 p.2
      = Real.sin (2 * p.2)
          * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i u)) p.1 p.2 := by
    rw [mixed_succ_right_eq]
  rw [h1, h2, mul_div_cancel_left₀ _ hsin]






end Work.FTS.StrongEps.E5Aux3
