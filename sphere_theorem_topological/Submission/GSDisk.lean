import Submission.GSNoCrit
import Submission.ExpBound

/-!
# The metric ball around a point is a topological disk

For every point `x₀` of a compact Riemannian manifold there is `ε > 0` such that the global
exponential map `GExp x₀` is a homeomorphism of the closed ball of radius `ε` in `T_{x₀}M` onto the
closed Riemannian ball of radius `ε` around `x₀`.

Ingredients (all already available):

* `Geodesic.exists_open_contMDiffOn_expMap` — `expMap x₀` is continuous on an open neighbourhood of
  `0`;
* `Geodesic.exists_injOn_expMap_nhds` — `expMap x₀` is injective near `0` (by the inverse function
  theorem at the origin a local diffeomorphism at `0` is injective on a whole neighbourhood of `0`,
  hence on a ball);
* `GlobalExp.exists_pos_GExp_eq_expMap` — `GExp x₀` and `expMap x₀` agree on a small ball;
* `GlobalExp.exists_pos_riemannianEDist_GExp_eq` — `d(x₀, GExp x₀ v) = ‖v‖` for small `v`;
* Hopf–Rinow — every point of the ball is `GExp x₀ v`;
* `ChartBounds.exists_chartGram_bounds` — the fibre norm and the model norm of `E` are equivalent at
  `x₀` (the two balls are measured with these two different norms).

The homeomorphism then follows from the standard compactness argument
(`Continuous.homeoOfEquivCompactToT2`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow
open Submission.Distance
open Submission.ChartConnection
open Submission.ExpBound

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSDisk

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable [PathConnectedSpace M] [RegularSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- The chart metric at the base point, in fibre form. -/
lemma chartGram_self_fibre (x₀ : M) (u : TangentSpace I x₀) :
    chartGram (I := I) x₀ x₀ (u : E) (u : E) = ‖u‖ ^ 2 := by
  rw [chartGram_self_eq_norm_sq (I := I) x₀ (u : E)]

/-- **The metric ball around a point is a topological disk.**  The homeomorphism is the
(exponential) map `u ↦ GExp x₀ u`, so that the sphere of radius `ε` corresponds to the set
`{d(x₀,·) = ε}`. -/
theorem exists_pos_homeo_closedBall
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ e : Metric.closedBall (0 : TangentSpace I x₀) ε ≃ₜ
        {y : M // Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal ε},
      ∀ u : Metric.closedBall (0 : TangentSpace I x₀) ε,
        (e u : M) = GExp (cov := cov) hmet x₀ (u : TangentSpace I x₀) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  haveI hproper : ProperSpace (TangentSpace I x₀) := by
    haveI : FiniteDimensional ℝ (TangentSpace I x₀) := ‹FiniteDimensional ℝ E›
    exact FiniteDimensional.proper ℝ (TangentSpace I x₀)
  obtain ⟨UG, hUGopen, hUG0, hUG⟩ := exists_open_contMDiffOn_expMap (cov := cov) x₀
  obtain ⟨UI, hUIopen, hUI0, hUIinj⟩ := exists_injOn_expMap_nhds (cov := cov) x₀
  obtain ⟨ρG, hρG, hagree⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet x₀
  obtain ⟨ρR, hρR, hminR⟩ := exists_pos_riemannianEDist_GExp_eq (cov := cov) hmet htor x₀
  have hxsrc : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := Submission.ChartBounds.exists_chartGram_bounds (I := I) x₀
    (K := ({x₀} : Set M)) isCompact_singleton ⟨x₀, rfl⟩
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hxsrc)
  have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp ((hUGopen.inter hUIopen).mem_nhds ⟨hUG0, hUI0⟩)
  refine ⟨min ρR (min ρG (Real.sqrt lam * δ)) / 2, by positivity, ?_⟩
  set ε : ℝ := min ρR (min ρG (Real.sqrt lam * δ)) / 2 with hεdef
  have hminpos : 0 < min ρR (min ρG (Real.sqrt lam * δ)) :=
    lt_min hρR (lt_min hρG (mul_pos hsl hδ))
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hερR : ε < ρR := by rw [hεdef]; linarith [min_le_left ρR (min ρG (Real.sqrt lam * δ))]
  have hερG : ε < ρG := by
    rw [hεdef]
    have h := min_le_right ρR (min ρG (Real.sqrt lam * δ))
    have h' := min_le_left ρG (Real.sqrt lam * δ); linarith
  have hεδ : ε < Real.sqrt lam * δ := by
    rw [hεdef]
    have h := min_le_right ρR (min ρG (Real.sqrt lam * δ))
    have h' := min_le_right ρG (Real.sqrt lam * δ); linarith
  -- the model norm of a small fibre vector is small
  have hEbound : ∀ u : TangentSpace I x₀, ‖u‖ ≤ ε → ∀ a : E, a = (u : E) → ‖a‖ < δ := by
    intro u hu a ha
    have h1 : lam * ‖a‖ ^ 2 ≤ chartGram (I := I) x₀ x₀ a a := (hbnd x₀ (by simp) a).1
    have h2 : chartGram (I := I) x₀ x₀ a a = ‖u‖ ^ 2 := by
      rw [ha, chartGram_self_fibre]
    have h3 : (‖u‖ : ℝ) ^ 2 ≤ ε ^ 2 := by nlinarith [hu, norm_nonneg u]
    have h4 : ε ^ 2 < lam * δ ^ 2 := by
      have hs : (Real.sqrt lam) ^ 2 = lam := Real.sq_sqrt hlam.le
      have hc : (0:ℝ) ≤ Real.sqrt lam * δ := mul_nonneg hsl.le hδ.le
      have h5 : ε ^ 2 < (Real.sqrt lam * δ) ^ 2 := by nlinarith [hεδ, hεpos.le, hc]
      nlinarith [h5, hs]
    have h6 : lam * ‖a‖ ^ 2 < lam * δ ^ 2 := by linarith [h1, h2.le, h2.ge, h3, h4]
    have h7 : ‖a‖ ^ 2 < δ ^ 2 := by nlinarith [h6, hlam, hδ]
    nlinarith [h7, norm_nonneg a, hδ]
  have hEball : ∀ a : E, ‖a‖ < δ → a ∈ Metric.ball (0 : E) δ := fun a ha =>
    Metric.mem_ball.mpr (by rw [dist_zero_right]; exact ha)
  have hEcfg : ∀ u : TangentSpace I x₀, ‖u‖ ≤ ε → ∀ a : E, a = (u : E) → a ∈ UG ∩ UI :=
    fun u hu a ha => hδsub (hEball a (hEbound u hu a ha))
  -- the four defining properties
  have hFW : ∀ u : TangentSpace I x₀, ‖u‖ ≤ ε →
      Manifold.riemannianEDist I x₀ (GExp (cov := cov) hmet x₀ u) ≤ ENNReal.ofReal ε := by
    intro u hu
    have hlt : ‖u‖ < ρR := lt_of_le_of_lt hu hερR
    have h := hminR u hlt
    rw [chartGram_self_fibre, Real.sqrt_sq (norm_nonneg u)] at h
    rw [h]
    exact ENNReal.ofReal_le_ofReal hu
  have hinj : ∀ u v : TangentSpace I x₀, ‖u‖ ≤ ε → ‖v‖ ≤ ε →
      GExp (cov := cov) hmet x₀ u = GExp (cov := cov) hmet x₀ v → u = v := by
    intro u v hu hv huv
    have huG : ‖u‖ < ρG := lt_of_le_of_lt hu hερG
    have hvG : ‖v‖ < ρG := lt_of_le_of_lt hv hερG
    have h1 : expMap cov x₀ (u : E) = expMap cov x₀ (v : E) := by
      rw [← hagree u huG, ← hagree v hvG]; exact huv
    have h2 : (u : E) = (v : E) :=
      hUIinj (hEcfg u hu (u : E) rfl).2 (hEcfg v hv (v : E) rfl).2 h1
    exact h2
  have hsurj : ∀ y : {y : M // Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal ε},
      ∃ u : TangentSpace I x₀, ‖u‖ ≤ ε ∧ GExp (cov := cov) hmet x₀ u = (y : M) := by
    intro y
    obtain ⟨v, hvG, hvd⟩ :=
      Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor x₀ (y : M)
    set t : ℝ := ‖v‖ with htdef
    have ht : t ≤ ε := by
      have h := y.2
      rw [hvd] at h
      exact (ENNReal.ofReal_le_ofReal_iff hεpos.le).mp h
    rcases eq_or_lt_of_le (norm_nonneg v) with h0 | h0
    · have hv0 : v = 0 := norm_eq_zero.mp h0.symm
      exact ⟨0, by rw [norm_zero]; exact hεpos.le, by rw [← hv0]; exact hvG⟩
    · have hvne : v ≠ 0 := by
        intro h; rw [h, norm_zero] at h0; exact lt_irrefl 0 h0
      refine ⟨t • unitOf v hvne, ?_, ?_⟩
      · rw [norm_smul, unitOf_norm v hvne, mul_one,
          Real.norm_of_nonneg (by rw [htdef]; exact norm_nonneg v)]
        exact ht
      · rw [show t • unitOf v hvne = v from ?_, hvG]
        rw [htdef, unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvne), one_smul]
  -- the map, its continuity, and the resulting homeomorphism
  have hmemC : ∀ u : Metric.closedBall (0 : TangentSpace I x₀) ε,
      ‖(u : TangentSpace I x₀)‖ ≤ ε := by
    intro u
    have h := u.2
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  let F : Metric.closedBall (0 : TangentSpace I x₀) ε →
      {y : M // Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal ε} := fun u =>
    ⟨GExp (cov := cov) hmet x₀ (u : TangentSpace I x₀), hFW _ (hmemC u)⟩
  let e : Metric.closedBall (0 : TangentSpace I x₀) ε ≃
      {y : M // Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal ε} :=
  { toFun := F
    invFun := fun y => ⟨Classical.choose (hsurj y), by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (Classical.choose_spec (hsurj y)).1⟩
    left_inv := fun u => by
      refine Subtype.ext ?_
      exact hinj _ _ (Classical.choose_spec (hsurj (F u))).1 (hmemC u)
        (Classical.choose_spec (hsurj (F u))).2
    right_inv := fun y => by
      refine Subtype.ext ?_
      exact (Classical.choose_spec (hsurj y)).2 }
  haveI hcomp : CompactSpace (Metric.closedBall (0 : TangentSpace I x₀) ε) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 ε)
  have hcontG : Continuous (fun u : Metric.closedBall (0 : TangentSpace I x₀) ε =>
      GExp (cov := cov) hmet x₀ (u : TangentSpace I x₀)) := by
    have h1 : Continuous (fun u : Metric.closedBall (0 : TangentSpace I x₀) ε =>
        expMap cov x₀ (((u : TangentSpace I x₀)) : E)) :=
      hUG.continuousOn.comp_continuous continuous_subtype_val
        (fun u => (hEcfg _ (hmemC u) _ rfl).1)
    have h2 : (fun u : Metric.closedBall (0 : TangentSpace I x₀) ε =>
        expMap cov x₀ (((u : TangentSpace I x₀)) : E))
        = fun u : Metric.closedBall (0 : TangentSpace I x₀) ε =>
          GExp (cov := cov) hmet x₀ (u : TangentSpace I x₀) := by
      funext u
      exact (hagree _ (lt_of_le_of_lt (hmemC u) hερG)).symm
    rw [← h2]; exact h1
  have hcontF : Continuous F :=
    hcontG.subtype_mk (fun u : Metric.closedBall (0 : TangentSpace I x₀) ε =>
      hFW (u : TangentSpace I x₀) (hmemC u))
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := e) hcontF, fun u => rfl⟩

end

end Submission.GSDisk
