/-
# `StrongEps/EpsRLX/RadBound/radA_dzdIter_expansion_open`

The pointwise Leibniz expansion of the `(z∂_z)`-iterates of the radial transfer profile

  `radA α f z = −ampA α z · L₁₂ f(z) + (ampB α z / c α) · L₁₂(Transport f)(0)`

for orders `q ≤ 4`, under the *open-quadrant* differentiability hypotheses only (no `CoerAdm`,
no `SmoothNbhd`):

  `D_z^q (radA α f)(z) = −Σ_{b≤q} C(q,b)·(D_z^b ampA α)(z)·(D_z^{q−b} L₁₂ f)(z)`
  `                       + (L₁₂(Transport f)(0)/c α)·(D_z^q ampB α)(z)`.

The three inputs are the split `radA = U₁ + U₂` (a `ring` identity after unfolding `radA`), the
additivity of the `D_z`-iterates on a sum (`E1Parts.DzdIter_add_of_diff`, using precisely the two
hypotheses of the statement), and the one-variable Leibniz rule for `D_z`
(`Nonlinear.Pieces.dzdIter_mul_leibniz`).  The only ancillary inputs are the smoothness of the
two profile coefficients, which is proved here (`ampA α` and `ampB α` are rational functions
with a non-vanishing denominator on `(0,∞)`); order `5` suffices, because the Leibniz rule at
order `q ≤ 4` only needs the *differentiability* of the iterates up to order `q − 1 ≤ 3`, i.e.
one order of smoothness more.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.StrongPersist.H6Aux.DzdIter_mul_of_diff
import Submission.Work.FTS.StrongPersist.H6Aux.q0Sm_Corr
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.RadBound

set_option maxHeartbeats 1000000

/-! ## Smoothness of the two profile coefficients on `(0,∞)` -/

/-- `ampA α z = 2z/(c(α)(1+z)²)` is `C^5` on `(0,∞)`. -/
theorem contDiffOn_ampA_five_open (α : ℝ) :
    ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) := by
  rcases eq_or_ne (Work.Spaces.c α) 0 with hc | hc
  · have h0 : Work.FTS.CoercivityFix.Transfer.ampA α = fun _ : ℝ => (0 : ℝ) := by
      funext z
      simp only [Work.FTS.CoercivityFix.Transfer.ampA, hc, zero_mul, div_zero]
    rw [h0]
    exact contDiffOn_const
  · have hnum : ContDiffOn ℝ 5 (fun z : ℝ => 2 * z) (Set.Ioi (0 : ℝ)) :=
      contDiffOn_const.mul contDiffOn_id
    have hden : ContDiffOn ℝ 5 (fun z : ℝ => Work.Spaces.c α * (1 + z) ^ 2)
        (Set.Ioi (0 : ℝ)) :=
      contDiffOn_const.mul ((contDiffOn_const.add contDiffOn_id).pow 2)
    have hne : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Spaces.c α * (1 + z) ^ 2 ≠ 0 := by
      intro z hz
      have h1 : (0 : ℝ) < z := hz
      exact mul_ne_zero hc (pow_ne_zero 2 (by linarith))
    show ContDiffOn ℝ 5
      (fun z : ℝ => 2 * z / (Work.Spaces.c α * (1 + z) ^ 2)) (Set.Ioi (0 : ℝ))
    exact hnum.div hden hne

/-- `ampB α z = 2z²/(1+z)³` is `C^5` on `(0,∞)`. -/
theorem contDiffOn_ampB_five_open (α : ℝ) :
    ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampB α) (Set.Ioi (0 : ℝ)) := by
  have hnum : ContDiffOn ℝ 5 (fun z : ℝ => 2 * z ^ 2) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_const.mul (contDiffOn_id.pow 2)
  have hden : ContDiffOn ℝ 5 (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi (0 : ℝ)) :=
    (contDiffOn_const.add contDiffOn_id).pow 3
  have hne : ∀ z ∈ Set.Ioi (0 : ℝ), (1 + z) ^ 3 ≠ 0 := by
    intro z hz
    have h1 : (0 : ℝ) < z := hz
    exact pow_ne_zero 3 (by linarith)
  show ContDiffOn ℝ 5 (fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) (Set.Ioi (0 : ℝ))
  exact hnum.div hden hne

/-- Every `D_z`-iterate of order `b` of a `C^5`-function on `(0,∞)` is differentiable there. -/
theorem differentiableAt_dzdIter_of_contDiffOn_five {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 5 u (Set.Ioi (0 : ℝ))) {b : ℕ} (hb : b + 1 ≤ 5) {z : ℝ}
    (hz : 0 < z) :
    DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z := by
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
  exact Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
    (hu := hu.of_le (by exact_mod_cast hb)) hz

/-! ## The expansion -/

theorem radA_dzdIter_expansion_open (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : Work.FTS.Galerkin.Fn)
    (hL12diff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z)
    (hAdiff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z
          * Work.Coercivity.L12f f z)) z) :
    ∀ q : ℕ, q ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z
        = -(∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
              * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
              * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)
          + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
              * Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
  intro q hq z hz
  have hA5 : ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_ampA_five_open α
  have hB5 : ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampB α) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_ampB_five_open α
  -- differentiability of the iterates of the two factors of `ampA · L₁₂ f`
  have hAdiffA : ∀ b : ℕ, b < q → ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (Work.FTS.CoercivityFix.Transfer.ampA α)) z' := by
    intro b hb z' hz'
    exact differentiableAt_dzdIter_of_contDiffOn_five hA5 (by omega) hz'
  have hLdiff : ∀ b : ℕ, b < q → ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z' := by
    intro b hb z' hz'
    exact hL12diff b (by omega) z' hz'
  -- the Leibniz expansion of the first summand `-1 * (ampA · L₁₂ f)`
  have hU1z : Work.Elliptic.DzdIter q (fun w : ℝ => -1
        * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w)) z
      = -1 * ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
          * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
              * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) := by
    have h1 : Work.Elliptic.DzdIter q (fun w : ℝ => -1
          * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w))
        = fun w : ℝ => -1 * Work.Elliptic.DzdIter q (fun z : ℝ =>
            Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z) w := by
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter,
        Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul,
        ← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter q
          (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z
            * Work.Coercivity.L12f f z)]
    rw [h1]
    change -1 * Work.Elliptic.DzdIter q (fun z : ℝ =>
        Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z) z
      = -1 * ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
          * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
              * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)
    rw [Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz q
      (Work.FTS.CoercivityFix.Transfer.ampA α) (Work.Coercivity.L12f f) hAdiffA hLdiff z hz]
  -- the second summand is a constant multiple of `ampB`
  have hU2fun : ∀ j : ℕ, Work.Elliptic.DzdIter j (fun w : ℝ =>
        (Work.FTS.CoercivityFix.Transfer.ampB α w / Work.Spaces.c α)
          * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
      = fun w : ℝ => (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
          * Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) w := by
    intro j
    have hfun : (fun w : ℝ => (Work.FTS.CoercivityFix.Transfer.ampB α w / Work.Spaces.c α)
          * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
        = fun w : ℝ => (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
            * Work.FTS.CoercivityFix.Transfer.ampB α w := by
      funext w
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [hfun, Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter,
      Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul,
      ← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j
        (Work.FTS.CoercivityFix.Transfer.ampB α)]
  have hU2z := congrFun (hU2fun q) z
  -- differentiability of the iterates of the two summands of the split
  have hdiff1 : ∀ b : ℕ, b < q → ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (fun w : ℝ => -1
        * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w))) z' := by
    intro b hb z' hz'
    have h1 : Work.Elliptic.DzdIter b (fun w : ℝ => -1
          * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w))
        = fun w : ℝ => -1 * Work.Elliptic.DzdIter b (fun z : ℝ =>
            Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z) w := by
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter,
        Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul,
        ← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b
          (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z
            * Work.Coercivity.L12f f z)]
    rw [h1]
    exact (hAdiff b (by omega) z' hz').const_mul (-1)
  have hdiff2 : ∀ b : ℕ, b < q → ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (fun w : ℝ =>
        (Work.FTS.CoercivityFix.Transfer.ampB α w / Work.Spaces.c α)
          * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) z' := by
    intro b hb z' hz'
    have hd : DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (Work.FTS.CoercivityFix.Transfer.ampB α)) z' :=
      differentiableAt_dzdIter_of_contDiffOn_five hB5 (by omega) hz'
    rw [hU2fun b]
    exact hd.const_mul _
  -- additivity of the `D_z`-iterates on the split
  have hadd : Work.Elliptic.DzdIter q (fun w : ℝ =>
        -1 * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w)
        + (Work.FTS.CoercivityFix.Transfer.ampB α w / Work.Spaces.c α)
          * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z
      = Work.Elliptic.DzdIter q (fun w : ℝ => -1
          * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w)) z
        + Work.Elliptic.DzdIter q (fun w : ℝ =>
            (Work.FTS.CoercivityFix.Transfer.ampB α w / Work.Spaces.c α)
              * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z :=
    Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff q _ _ hdiff1 hdiff2 z hz
  -- the pointwise split of `radA`
  have hsplit : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.FTS.CoercivityFix.Transfer.radA α f w
        = -1 * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w)
          + (Work.FTS.CoercivityFix.Transfer.ampB α w / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := by
    intro w _
    simp only [Work.FTS.CoercivityFix.Transfer.radA]
    ring
  have hcongr : Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z
      = Work.Elliptic.DzdIter q (fun w : ℝ =>
          -1 * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w)
          + (Work.FTS.CoercivityFix.Transfer.ampB α w / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z :=
    Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _ hsplit q z hz
  -- reassociate the summands to match the Leibniz output
  have hsum : (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
        * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
            * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z))
      = ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
        * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z :=
    Finset.sum_congr rfl (fun b _ => by ring)
  rw [hcongr, hadd, hU1z, hU2z, hsum]
  ring

end Work.FTS.StrongEps.EpsRLX.RadBound
