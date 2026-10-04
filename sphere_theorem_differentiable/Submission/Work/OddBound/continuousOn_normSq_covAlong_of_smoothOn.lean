import Mathlib
import Submission.Work.OddBound.Defs
import Submission.SmoothFieldCover
import Submission.EnergyRay
import Submission.BonnetMyers
import Submission.ChartConnection
import Submission.JacobiCoords
import Submission.IntrinsicVariation
import Submission.Commons.Topology.continuousOn_Icc_of_continuousOn_pieces

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Continuity of the squared norm of the covariant derivative of a field smooth along a curve.**
`γ` is `C^∞` with nonvanishing velocity on the slightly larger interval `Ioo (a-1) (b+1)`, and `V` is
smooth along `γ` on `Icc a b`; then `t ↦ ‖∇_{γ'}V(t)‖²` is continuous on `Icc a b`. This is the
`L²`-integrability input for `Work.OddBound.HasSmallCovDeriv`.

Route (same chart cover as in `Work.OddBound.continuousOn_idxAlong_of_smoothOn`): cover `[a,b]` with
`Submission.SmoothFieldCover.exists_partition_smoothField`, giving pieces `[c k, c (k+1)]` with local
intervals `Icc (S k) (En k) ⊆ Ioo (a-1) (b+1)`, `S k < c k`, `c (k+1) < E k`, on which `γ` lies in a
chart `z k`, the chart coordinates `u = chartCoord z γ` and `J = chartCoords z γ V` are `C^∞`, and
`frameVector z (γ ·) (J ·) = V`. For `t ∈ Icc (c k) (c (k+1))` (strictly inside `Icc (S k) (En k)`),
the hypothesis `t ∈ Icc a b` gives `Ioo (t-1) (t+1) ⊆ Ioo (a-1) (b+1)`, so
`Submission.EnergyRay.covAlong_eq_chart_of_data` gives
`covAlong cov V t = frameVector z (γ t) (DtQ cov z u J w J' t)` with `w = deriv u`, `J' = deriv J`;
hence `‖covAlong cov V t‖² = chartGram z (γ t) (DtQ cov z u J w J' t) (DtQ cov z u J w J' t)` by
`Submission.ChartConnection.chartGram_apply` and `real_inner_self_eq_norm_sq`. The right-hand side is
continuous on `Icc (c k) (c (k+1))` by `Submission.BonnetMyers.continuousOn_chartGram_curve`, using
continuity of `γ` and of `DtQ cov z u J w J'` (the latter by
`Submission.BonnetMyers.continuousOn_covDsP_along` with `HasDerivAt.continuousOn` for `u`, `J`,
`w = deriv u`, `J' = deriv J` -- cf. `Submission.IndexCorner` for the same step). Glue with
`Commons.Topology.continuousOn_Icc_of_continuousOn_pieces`. -/
theorem continuousOn_normSq_covAlong_of_smoothOn
    (htor : cov.torsion = 0)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (a - 1) (b + 1)))
    (hne : ∀ t ∈ Ioo (a - 1) (b + 1), curveVelocity (I := I) γ t ≠ 0)
    (hVs : ∀ t ∈ Icc a b, SmoothAlongAt (I := I) γ V t) :
    ContinuousOn (fun t => ‖covAlong cov V t‖ ^ 2) (Icc a b) := by
  classical
  obtain ⟨N, c, S, En, z, hc0, hcN, hmono, hSB, hsrc, hcdU, hcdV, hVfr, hroom⟩ :=
    Submission.SmoothFieldCover.exists_partition_smoothField (I := I) hab hγ hVs
  -- monotonicity of the partition chain
  have hchain : ∀ j, j ≤ N → ∀ i, i ≤ j → c i ≤ c j := by
    intro j
    induction j with
    | zero =>
        intro _ i hi
        obtain rfl : i = 0 := Nat.le_zero.mp hi
        exact le_rfl
    | succ j ih =>
        intro hj i hi
        rcases Nat.lt_or_ge i (j + 1) with hlt | hge
        · exact le_trans (ih (by omega) i (Nat.lt_succ_iff.mp hlt)) (hmono j (by omega)).le
        · obtain rfl : i = j + 1 := by omega
          exact le_rfl
  -- continuity on each chart piece
  have hpiece : ∀ k < N,
      ContinuousOn (fun t => ‖covAlong cov V t‖ ^ 2) (Icc (c k) (c (k + 1))) := by
    intro k hk
    set u : ℝ → E := Submission.IntrinsicVariation.chartCoord (I := I) (z k) γ with hudef
    set J : ℝ → E := Submission.JacobiCoords.chartCoords (I := I) (z k) γ V with hJdef
    have hBsub : Icc (c k) (c (k + 1)) ⊆ Ioo (S k) (En k) := fun t ht =>
      ⟨by linarith [(hSB k hk).1, ht.1], by linarith [ht.2, (hSB k hk).2]⟩
    have hIccsub : Icc (c k) (c (k + 1)) ⊆ Icc (S k) (En k) :=
      fun _ ht => ⟨(hBsub ht).1.le, (hBsub ht).2.le⟩
    have hunt : Icc (S k) (En k) ⊆ Ioo (a - 1) (b + 1) := hroom k hk
    have hak : a ≤ c k := by
      rw [← hc0]; exact hchain k (le_of_lt hk) 0 (Nat.zero_le k)
    have hkb : c (k + 1) ≤ b := by
      rw [← hcN]; exact hchain N le_rfl (k + 1) (Nat.succ_le_of_lt hk)
    have huc : ContinuousOn u (Icc (c k) (c (k + 1))) :=
      (hcdU k hk).continuousOn.mono hIccsub
    have hJc : ContinuousOn J (Icc (c k) (c (k + 1))) :=
      (hcdV k hk).continuousOn.mono hIccsub
    have hUo : ContDiffOn ℝ ∞ u (Ioo (S k) (En k)) :=
      (hcdU k hk).mono (fun t ht => ⟨ht.1.le, ht.2.le⟩)
    have hJo : ContDiffOn ℝ ∞ J (Ioo (S k) (En k)) :=
      (hcdV k hk).mono (fun t ht => ⟨ht.1.le, ht.2.le⟩)
    have hwCd : ContDiffOn ℝ ∞ (deriv u) (Ioo (S k) (En k)) :=
      hUo.deriv_of_isOpen (m := ∞) isOpen_Ioo (le_of_eq (by simp))
    have heCd : ContDiffOn ℝ ∞ (deriv J) (Ioo (S k) (En k)) :=
      hJo.deriv_of_isOpen (m := ∞) isOpen_Ioo (le_of_eq (by simp))
    have hw : ContinuousOn (deriv u) (Icc (c k) (c (k + 1))) := hwCd.continuousOn.mono hBsub
    have he : ContinuousOn (deriv J) (Icc (c k) (c (k + 1))) := heCd.continuousOn.mono hBsub
    have htgt : ∀ t ∈ Icc (c k) (c (k + 1)), u t ∈ (extChartAt I (z k)).target := by
      intro t ht
      exact (extChartAt I (z k)).map_source (by
        rw [extChartAt_source]; exact hsrc k hk _ (hIccsub ht))
    have hQ : ContinuousOn (Submission.BonnetMyers.DtQ cov (z k) u J (deriv u) (deriv J))
        (Icc (c k) (c (k + 1))) := by
      exact Submission.BonnetMyers.continuousOn_covDsP_along (cov := cov) huc hJc hw he htgt
    have hγcont : ContinuousOn γ (Icc (c k) (c (k + 1))) :=
      hγ.continuousOn.mono (fun _ ht => hunt (hIccsub ht))
    have hsrcB : ∀ t ∈ Icc (c k) (c (k + 1)), γ t ∈ (chartAt H (z k)).source :=
      fun _ ht => hsrc k hk _ (hIccsub ht)
    have hcont := Submission.BonnetMyers.continuousOn_chartGram_curve (I := I) (x₀ := z k)
      hγcont hQ hQ hsrcB
    refine hcont.congr (fun t ht => ?_)
    have htIoo : t ∈ Ioo (S k) (En k) := hBsub ht
    have htIcc : t ∈ Icc a b := ⟨le_trans hak ht.1, le_trans ht.2 hkb⟩
    have hγ1 : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)) :=
      hγ.mono fun s hs => ⟨by linarith [hs.1, htIcc.1], by linarith [hs.2, htIcc.2]⟩
    rw [Submission.EnergyRay.covAlong_eq_chart_of_data (cov := cov) htor htIoo (hsrc k hk)
      (hcdU k hk) (hcdV k hk) (hVfr k hk) hγ1 (hne t (hunt (hIccsub ht))) (hVs t htIcc)]
    simp only [hudef, hJdef]
    rw [← real_inner_self_eq_norm_sq, ← Submission.ChartConnection.chartGram_apply]
  exact Commons.Topology.continuousOn_Icc_of_continuousOn_pieces hc0 hcN
    (fun k hk => (hmono k hk).le) hpiece

end Work.OddBound
