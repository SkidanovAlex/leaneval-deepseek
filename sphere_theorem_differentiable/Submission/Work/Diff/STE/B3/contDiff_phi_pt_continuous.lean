import Mathlib
import Submission.Work.Diff.STE.B3.phi_comp_pt_continuousOn_sigmaClosedBall

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: continuity of `y ↦ Phi D i u k (pt i y)` on the closed `σ`-ball, from `R`-continuity

The sibling `Work.Diff.STE.B3.phi_comp_pt_continuousOn_sigmaClosedBall` proves the same continuity
statement under the hypothesis that the *chart matrices* `D.mat i k a b` are continuous on
`{χ i ≠ 0} ⊇ σ`-ball.  This file derives it from the strictly weaker hypothesis that the
*localised components* `D.R i k a b = ψ i · √(dens i) · mat i k a b` are continuous (globally).

The point is an algebraic collapse on the `σ`-ball, where `χ i = 1` (so `ψ i = ζ i ∘ pt i`):

`Phi D i u k (pt i y) = ζ i (pt i y) · (√(dens i y))⁻¹ · ∑ a b, u a b y · D.mat i k a b y`

and, since `√(dens i y) · √(dens i y) = dens i y ≠ 0`,

`= (∑ a b, u a b y · D.R i k a b y) · (dens i y)⁻¹`.

The right-hand side is continuous on the closed ball: the sum of the (continuous) products
`u a b · R i k a b` is continuous, and `dens i` is continuous and strictly positive on the ball
(its flat coordinate lies in the chart target, `D.htarget`), so its inverse is continuous there.

**The mathematics is nothing but the observation that the cancelling factor `√(dens i)` — which is
`0`-free on the ball — absorbs the two occurrences of `(√(dens i))⁻¹`.**  No hypothesis on the
chart matrices is needed, and in particular neither the density bound `hdens` nor the chart-matrix
continuity of the sibling statement is used.
-/

namespace Work.Diff.STE.B3

theorem contDiff_phi_pt_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Work.Diff.STE.Bil (I := I) (M := M))
    (hu : ∀ a b : Fin (Module.finrank ℝ E), Continuous (u a b))
    (hk : ∀ (a b : Fin (Module.finrank ℝ E)), Continuous (D.R i k a b)) :
    ContinuousOn (fun y => Work.Diff.STE.B3.Phi D i u k (D.pt i y))
      (Work.Diff.STE.B3.sigmaClosedBall D i) := by
  classical
  -- the collapsed expression `(∑ u a b y * R i k a b y) * (dens i y)⁻¹` is continuous on the ball
  have hcont : ContinuousOn (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        u a b y * D.R i k a b y) * (D.dens i y)⁻¹)
      (Work.Diff.STE.B3.sigmaClosedBall D i) := by
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_finsetSum Finset.univ (fun a _ =>
        continuousOn_finsetSum Finset.univ (fun b _ =>
          (hu a b).continuousOn.mul (hk a b).continuousOn))
    · intro y hy
      simp only [Work.Diff.STE.B3.mem_sigmaClosedBall] at hy
      have hz2 : ‖y‖ ≤ 2 * D.σ i := by have h := D.hσ i; linarith
      have htgt := D.htarget i y hz2
      have hd : ContinuousAt (D.dens i) y :=
        Work.Diff.STE.B3.dens_continuousAt_of_mem_target D i htgt
      exact (hd.inv₀
        (ne_of_gt (Work.Diff.STE.B3.dens_pos_of_mem_target D i htgt))).continuousWithinAt
  -- it agrees with `Phi D i u k (pt i ·)` on the ball
  refine hcont.congr fun y hy => ?_
  simp only [Work.Diff.STE.B3.mem_sigmaClosedBall] at hy
  change Work.Diff.STE.B3.Phi D i u k (D.pt i y)
      = (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          u a b y * D.R i k a b y) * (D.dens i y)⁻¹
  have hz2 : ‖y‖ ≤ 2 * D.σ i := by have h := D.hσ i; linarith
  have hchi : D.χ i y = 1 := D.hχ1 i y hy
  -- on the `σ`-ball the localised weight is the normalised weight of chart `i`
  have hpsi : D.psi i y = D.ζ i (D.pt i y) := by
    simp only [Work.Diff.STE.B3Data.psi, hchi, one_mul]
  -- the sum of the components factors the constant `ζ i (pt i y) · √(dens i y)`
  have hsum : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        u a b y * D.R i k a b y)
      = (D.ζ i (D.pt i y) * Real.sqrt (D.dens i y)) *
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          u a b y * D.mat i k a b y) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Work.Diff.STE.B3Data.R, hpsi]
    ring
  rw [hsum, Work.Diff.STE.B3.phi_comp_pt_Phi_pt_eq (i := i) D u k hy]
  -- the density is positive on the ball, so `(√(dens i y))⁻¹ = √(dens i y) · (dens i y)⁻¹`
  have hdpos : 0 < D.dens i y :=
    Work.Diff.STE.B3.dens_pos_of_mem_target D i (D.htarget i y hz2)
  have hs : Real.sqrt (D.dens i y) * Real.sqrt (D.dens i y) = D.dens i y := by
    rw [← pow_two, Real.sq_sqrt hdpos.le]
  have hroot : (Real.sqrt (D.dens i y))⁻¹ = Real.sqrt (D.dens i y) * (D.dens i y)⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_assoc, hs, mul_inv_cancel₀ hdpos.ne']
  rw [hroot]
  ring

end Work.Diff.STE.B3
