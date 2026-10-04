import Mathlib
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.BPairSmooth
import Submission.Work.Diff.STE.B3.integrable_of_continuousOn_of_bound
import Submission.Work.Diff.STE.B3.Rstar_apply
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.B3.phi_comp_pt_continuousOn_sigmaClosedBall

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: integrability of the `j`-th term of the composite pairing (`N`-pair)

This is the third of the three integrability inputs of the B3 adjunction
`D.BPair (D.Rstar i u) k = CPair i u (D.R i k)` (`B3/BPair_Rstar.lean`): the integral over the
`σ i`-ball of

`y ↦ (ζ j (pt i y))^2 * dens i y * Phi D i u k (pt i y)`.

Unlike the other two (`integrableOn_Cpair_term`, `integrableOn_Rpair_term`), this integrand is
**not** supported in the open cube, so the "vanishing outside the domain" trick does not apply;
instead the integrand is shown to be continuous on the *compact* closed flat ball of radius `σ i`
and integrability there is `ContinuousOn.integrableOn_compact`; the open ball follows by
restriction.

The three factors are continuous on the closed `σ i`-ball:

* `ζ j ∘ pt i`, because `pt i` is continuous there (`D.htarget` puts the flat coordinate in the
  chart target) and `ζ j` is `C^∞` — `pt_continuousOn_sigmaClosedBall` below;
* `dens i`, by `Work.Diff.STE.B3.dens_continuousAt_of_mem_target` (the chart matrix is continuous
  and positive definite along the chart, see `B3/dens_bound_sigma.lean`) —
  `dens_continuousOn_sigmaClosedBall` below;
* `Phi D i u k ∘ pt i`, which is `Work.Diff.STE.B3.phi_comp_pt_continuousOn_sigmaClosedBall`
  (proved in the sibling file of the same name); that is where the lower bound `hdens` is used
  (to invert the strictly positive square root of the density).

Nothing here needs `I.Boundaryless`, `T2Space M` or completeness of the chart at a boundary.
-/

namespace Work.Diff.STE.B3

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]

/-- `pt i` is continuous on the closed flat ball of radius `σ i` (on which the chart at `x₀ i` is
genuine, by `D.htarget`, so that the chart inverse is continuous there). -/
private lemma pt_continuousOn_sigmaClosedBall
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    ContinuousOn (fun z => D.pt i z) (sigmaClosedBall (I := I) (M := M) D i) := by
  have hflat : Continuous (flatToE (I := I) (D.x₀ i)) := by
    have h1 : Continuous fun z : Fin (Module.finrank ℝ E) → ℝ =>
        (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)) + z :=
      continuous_const.add continuous_id
    have h2 : Continuous fun w : Fin (Module.finrank ℝ E) → ℝ =>
        (Module.finBasis ℝ E).equivFun.symm w :=
      (((Module.finBasis ℝ E).equivFun.symm :
        (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E).toContinuousLinearMap).continuous
    exact h2.comp h1
  have hsym : ContinuousOn (fun z : E => (extChartAt I (D.x₀ i)).symm z)
      (extChartAt I (D.x₀ i)).target :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ((⊤ : ENat) : WithTop ENat))
      (D.x₀ i)).continuousOn
  have hmaps : Set.MapsTo (flatToE (I := I) (D.x₀ i))
      (sigmaClosedBall (I := I) (M := M) D i) (extChartAt I (D.x₀ i)).target := by
    intro z hz
    refine D.htarget i z ?_
    have hz' : ‖z‖ ≤ D.σ i := hz
    have hσ := D.hσ i
    linarith
  simpa only [B3Data.pt, Function.comp_def] using hsym.comp hflat.continuousOn hmaps

/-- The closed flat ball of radius `σ i` is compact. -/
private lemma isCompact_sigmaClosedBall
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    IsCompact (sigmaClosedBall (I := I) (M := M) D i) := by
  rw [show sigmaClosedBall (I := I) (M := M) D i
      = Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i) from ?_]
  · exact isCompact_closedBall _ _
  · ext z
    simp only [sigmaClosedBall, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]

/-- The volume density is continuous on the closed flat ball of radius `σ i`, because there the
flat coordinate lies in the chart target and the chart matrix is continuous and positive definite
(`Work.Diff.STE.B3.dens_continuousAt_of_mem_target`). -/
private lemma dens_continuousOn_sigmaClosedBall
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    ContinuousOn (D.dens i) (sigmaClosedBall (I := I) (M := M) D i) := by
  intro z hz
  refine (dens_continuousAt_of_mem_target D i ?_).continuousWithinAt
  refine D.htarget i z ?_
  have hz' : ‖z‖ ≤ D.σ i := hz
  have hσ := D.hσ i
  linarith

end Helpers

theorem integrableOn_Npair_term
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Work.Diff.STE.Bil (I := I) (M := M))
    (hu : ∀ a b : Fin (Module.finrank ℝ E), Continuous (u a b))
    (hk : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContinuousOn (D.mat j k a b) {z : Fin (Module.finrank ℝ E) → ℝ | D.χ j z ≠ 0})
    (hdens : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (i : ι₀)
      (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i → c ≤ D.dens i z ∧ D.dens i z ≤ C)
    (j : ι₀) :
    MeasureTheory.IntegrableOn
      (fun y => (D.ζ j (D.pt i y)) ^ 2 * D.dens i y
        * Work.Diff.STE.B3.Phi D i u k (D.pt i y))
      (Work.Diff.STE.B3.sigmaBall D i) MeasureTheory.volume := by
  classical
  have hpt := pt_continuousOn_sigmaClosedBall D i
  have hζ : ContinuousOn (fun y => D.ζ j (D.pt i y))
      (sigmaClosedBall (I := I) (M := M) D i) :=
    (D.hζsm j).continuous.comp_continuousOn hpt
  have hdensc := dens_continuousOn_sigmaClosedBall D i
  have hΦ := phi_comp_pt_continuousOn_sigmaClosedBall D i u k hu hk hdens
  have hf : ContinuousOn (fun y => (D.ζ j (D.pt i y)) ^ 2 * D.dens i y
      * Phi D i u k (D.pt i y)) (sigmaClosedBall (I := I) (M := M) D i) := by
    refine (((hζ.pow 2).mul hdensc).mul hΦ).congr ?_
    intro y _
    simp only [Pi.mul_apply, Pi.pow_apply]
  refine (hf.integrableOn_compact (isCompact_sigmaClosedBall D i)).mono_set ?_
  intro y hy
  exact le_of_lt (show ‖y‖ < D.σ i from hy)

end Work.Diff.STE.B3
