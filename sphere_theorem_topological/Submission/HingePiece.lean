import Submission.HingeUniform
import Submission.GExpRay
import Submission.HingeKey2
import Submission.Commons.Geometry.Manifold.exists_finset_compact_chart_cover

/-!
# The uniform comparison radius of a compact chart piece, and the uniform `GCompHolds`

This file combines

* `Submission.HingeUniform.exists_uniform_chartFlow_comparison_ind` (the model comparison for the
  chart-flow exponential map of a compact chart piece, linearly independent case),
* `Submission.GExpRay.hingeCompG_dependent` (the linearly dependent case at the `GExp` level),

into the **full uniform comparison radius of a compact chart piece**
(`exists_uniform_chartFlow_comparison`), stated at the chart-invariant `GExp` level.  It then
applies the cover `Commons.Geometry.Manifold.exists_finset_compact_chart_cover` to obtain
`∃ ρ > 0, ∀ z : M, GCompHolds hmet z ρ`, the input of `HingeKey2.gcompHolds_pi_of_uniform` (the
global Toponogov hinge comparison).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.GExpFlow
open Submission.ChartFlowVar
open Submission.HingeUniform
open Submission.GExpRay
open Submission.HingeGlobal
open Commons.Geometry.Manifold
open Submission.HingeKey
open Submission.ChartConnection
open Submission.ChartBounds

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.HingePiece

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M] [Nonempty M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable {z₀ : M} {Z : Set M}

/-- **The full uniform comparison radius of a compact chart piece** (in the `GExp` language).
There is `ρ > 0`, independent of `q ∈ Z`, such that for all unit `U V ∈ T_qM` and all
`r₁ r₂ ∈ (0,ρ)` the hinge comparison holds at `q`. -/
theorem exists_uniform_chartFlow_comparison
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (hZ : IsCompact Z) (hZne : Z.Nonempty) (hZsrc : Z ⊆ (chartAt H z₀).source)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ Z, ∀ (r₁ r₂ : ℝ) (U V : TangentSpace I q),
      0 < r₁ → 0 < r₂ → r₁ + r₂ < ρ → ‖U‖ = 1 → ‖V‖ = 1 →
      Manifold.riemannianEDist I (GExp (cov := cov) hmet q (r₁ • U))
          (GExp (cov := cov) hmet q (r₂ • V))
        ≤ ENNReal.ofReal (modelDist1 (hingeAngle U V) r₁ r₂) := by
  classical
  obtain ⟨lam, hlam, Lam, hLam, hgram⟩ := Submission.ChartBounds.exists_chartGram_bounds
    (I := I) (x₀ := z₀) (K := Z) hZ hZne hZsrc
  obtain ⟨ρi, hρi, hρile, hind⟩ := exists_uniform_chartFlow_comparison_ind (cov := cov) (z₀ := z₀)
    (Z := Z) hmet htor hpinch hZsrc hlam (fun q hq w => (hgram q hq w).1) D
  have hslpos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hcpos : 0 < flowScale D := flowScale_pos D
  refine ⟨min ρi Real.pi, lt_min hρi Real.pi_pos, ?_⟩
  intro q hq r₁ r₂ U V hr1 hr2 hrs hU hV
  have hqs : q ∈ (extChartAt I z₀).source := by simpa using hZsrc hq
  have hrs' : r₁ + r₂ < min ρi Real.pi := hrs
  have hle1 : r₁ < ρi := by
    have h : r₁ < min ρi Real.pi := lt_trans (lt_add_of_pos_right r₁ hr2) hrs'
    exact lt_of_lt_of_le h (min_le_left _ _)
  have hle2 : r₂ < ρi := by
    have h : r₂ < min ρi Real.pi := lt_trans (lt_add_of_pos_left r₂ hr1) hrs'
    exact lt_of_lt_of_le h (min_le_left _ _)
  have hsumπ : r₁ + r₂ < Real.pi :=
    lt_of_lt_of_le hrs' (min_le_right _ _)
  set clm : TangentSpace I q →L[ℝ] E :=
    (trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q with hclmdef
  have hle1' : r₁ < Real.sqrt lam * (1 / (2 * flowScale D)) := lt_of_lt_of_le hle1 hρile
  -- phase membership and non-degeneracy for the `GExp`/`chartFlowExp` identification
  have hphase : ∀ {w : TangentSpace I q}, ‖w‖ < Real.sqrt lam * (1 / (2 * flowScale D)) →
      ((extChartAt I z₀) q, flowScale D • (clm w)) ∈ D.O := by
    intro w hw
    refine D.hKO ?_
    refine ⟨⟨q, hq, rfl⟩, ?_⟩
    rw [mem_closedBall, dist_zero_right, hclmdef, norm_smul, Real.norm_eq_abs,
      abs_of_pos hcpos]
    have hcg : lam * ‖clm w‖ ^ 2 ≤ chartGram (I := I) z₀ q (clm w) (clm w) :=
      (hgram q hq (clm w)).1
    have hchart : chartGram (I := I) z₀ q (clm w) (clm w) = ‖w‖ ^ 2 := by
      rw [hclmdef, chartGram_clm (I := I) hqs w w, real_inner_self_eq_norm_sq]
    rw [hchart] at hcg
    have h1 : Real.sqrt lam * ‖clm w‖ ≤ ‖w‖ := by
      have h2 : Real.sqrt (lam * ‖clm w‖ ^ 2) = Real.sqrt lam * ‖clm w‖ := by
        rw [Real.sqrt_mul hlam.le, Real.sqrt_sq (norm_nonneg _)]
      have h3 : Real.sqrt (‖w‖ ^ 2) = ‖w‖ := Real.sqrt_sq (norm_nonneg _)
      rw [← h2, ← h3]
      exact Real.sqrt_le_sqrt hcg
    have h4 : Real.sqrt lam * ‖clm w‖ < Real.sqrt lam * (1 / (2 * flowScale D)) :=
      lt_of_le_of_lt h1 hw
    have h5 : ‖clm w‖ < 1 / (2 * flowScale D) := lt_of_mul_lt_mul_left h4 hslpos.le
    have h6 : flowScale D * ‖clm w‖ < 1 / 2 := by
      rw [lt_div_iff₀ (mul_pos two_pos hcpos)] at h5
      linarith
    linarith
  have hne : ∀ {w : TangentSpace I q}, w ≠ 0 → clm w ≠ 0 := by
    intro w hw0 h0
    apply hw0
    have h1 : inner ℝ w w = 0 := by
      rw [← chartGram_clm (I := I) hqs w w, h0, chartGram_zero]
    rw [real_inner_self_eq_norm_sq] at h1
    exact norm_eq_zero.mp (by nlinarith [h1, norm_nonneg w])
  have hGid : ∀ {w : TangentSpace I q}, w ≠ 0 → ‖w‖ < Real.sqrt lam * (1 / (2 * flowScale D)) →
      GExp (cov := cov) hmet q (frameVector (I := I) z₀ q (clm w))
        = chartFlowExp (cov := cov) D q (clm w) := by
    intro w hw0 hw
    exact GExp_eq_chartFlow (cov := cov) hmet D hqs (clm w) (hphase hw) (hne hw0)
  by_cases hindep : ∀ a b : ℝ, a • U + b • V = 0 → a = 0 ∧ b = 0
  · have hU0 : U ≠ 0 := by rintro rfl; simp at hU
    have hV0 : V ≠ 0 := by rintro rfl; simp at hV
    have hs1 : ‖r₁ • U‖ < Real.sqrt lam * (1 / (2 * flowScale D)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr1, hU, mul_one]
      exact lt_of_lt_of_le hle1 hρile
    have hs2 : ‖r₂ • V‖ < Real.sqrt lam * (1 / (2 * flowScale D)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr2, hV, mul_one]
      exact lt_of_lt_of_le hle2 hρile
    have h := hind q hq r₁ r₂ U V hr1 hle1 hr2 hle2 hU hV hindep
    have e1 : GExp (cov := cov) hmet q (r₁ • U)
        = chartFlowExp (cov := cov) D q (clm (r₁ • U)) := by
      conv_lhs => rw [← frameVector_clm (I := I) hqs (r₁ • U)]
      exact hGid (smul_ne_zero (ne_of_gt hr1) hU0) hs1
    have e2 : GExp (cov := cov) hmet q (r₂ • V)
        = chartFlowExp (cov := cov) D q (clm (r₂ • V)) := by
      conv_lhs => rw [← frameVector_clm (I := I) hqs (r₂ • V)]
      exact hGid (smul_ne_zero (ne_of_gt hr2) hV0) hs2
    rw [e1, e2, modelDist1, cos_hingeAngle hU hV]
    exact h
  · have hdep : ∃ a b : ℝ, a • U + b • V = 0 ∧ (a ≠ 0 ∨ b ≠ 0) := by
      by_contra hcon
      push Not at hcon
      exact hindep fun a b hab => hcon a b hab
    have hab : r₁ + r₂ ≤ Real.pi := le_of_lt hsumπ
    rcases Submission.HingeLocal.eq_or_eq_neg_of_dependent hU hV hdep with hVU | hVU
    · rw [hVU]
      exact hingeCompG_dependent (cov := cov) hmet q hr1 hr2 hab hU hU (Or.inl rfl)
    · rw [hVU]
      exact hingeCompG_dependent (cov := cov) hmet q hr1 hr2 hab hU (by rw [norm_neg]; exact hU)
        (Or.inr rfl)


/-- **The uniform local comparison radius**: there is `ρ > 0` such that the hinge comparison holds
at every point of `M` for hinges of size `< ρ` (in the chart-invariant `GExp` language).  This is
the input of `HingeKey2.gcompHolds_pi_of_uniform` (global Toponogov). -/
theorem exists_uniform_GCompHolds
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : M, GCompHolds (cov := cov) hmet z ρ := by
  classical
  obtain ⟨S, Zc, hSne, hZc_comp, hZc_ne, hZc_mem, hZc_src, hcover⟩ :=
    Commons.Geometry.Manifold.exists_finset_compact_chart_cover (I := I) (M := M)
  have hpiece : ∀ z ∈ S, ∃ (D : ChartFlowData (cov := cov) (I := I) z (Zc z)) (ρ : ℝ),
      0 < ρ ∧ ∀ q ∈ Zc z, ∀ (r₁ r₂ : ℝ) (U V : TangentSpace I q),
        0 < r₁ → 0 < r₂ → r₁ + r₂ < ρ → ‖U‖ = 1 → ‖V‖ = 1 →
        Manifold.riemannianEDist I (GExp (cov := cov) hmet q (r₁ • U))
            (GExp (cov := cov) hmet q (r₂ • V))
          ≤ ENNReal.ofReal (modelDist1 (hingeAngle U V) r₁ r₂) := by
    intro z hz
    obtain ⟨D, -⟩ := exists_chartFlowData (cov := cov) (I := I) (z₀ := z) (Z := Zc z)
      (hZc_comp z hz) (hZc_src z hz)
    obtain ⟨ρ, hρ, hcomp⟩ := exists_uniform_chartFlow_comparison (cov := cov) (z₀ := z) (Z := Zc z)
      hmet htor hpinch (hZc_comp z hz) (hZc_ne z hz) (hZc_src z hz) D
    exact ⟨D, ρ, hρ, hcomp⟩
  choose Df ρf hρf hcompf using hpiece
  let ρa : {z // z ∈ S} → ℝ := fun z => ρf z.1 z.2
  have hne : (S.attach.image ρa).Nonempty := hSne.attach.image ρa
  set ρmin : ℝ := (S.attach.image ρa).min' hne with hρmindef
  have hρmin_pos : 0 < ρmin := by
    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp (Finset.min'_mem (S.attach.image ρa) hne)
    show 0 < (S.attach.image ρa).min' hne
    rw [← hzeq]
    exact hρf z.1 z.2
  refine ⟨ρmin, hρmin_pos, ?_⟩
  intro z a b v w ha hb hab hv hw _ _
  have hfind : ∃ z₀ ∈ S, z ∈ Zc z₀ := by
    have h : z ∈ ⋃ z₀ ∈ (S : Set M), Zc z₀ := by rw [hcover]; trivial
    simpa using h
  obtain ⟨z₀, hz₀S, hzZ⟩ := hfind
  have hρle : ρmin ≤ ρf z₀ hz₀S := by
    show (S.attach.image ρa).min' hne ≤ ρf z₀ hz₀S
    have hmem : (⟨z₀, hz₀S⟩ : {z // z ∈ S}) ∈ S.attach := Finset.mem_attach S _
    have hmem2 : ρf z₀ hz₀S ∈ S.attach.image ρa :=
      (Finset.mem_image (f := ρa) (s := S.attach) (b := ρf z₀ hz₀S)).mpr
        ⟨⟨z₀, hz₀S⟩, hmem, rfl⟩
    exact Finset.min'_le _ _ hmem2
  exact hcompf z₀ hz₀S z hzZ a b v w ha hb (lt_of_lt_of_le hab hρle) hv hw


/-- **Toponogov's hinge comparison** (global form).  On a compact, path-connected manifold of
regular topology with a quarter-pinched metric, the hinge comparison holds at every point for all
hinges of size `< π`.  (The conclusion is the `GExp`-level statement `GCompHolds ... Real.pi`.) -/
theorem gcompHolds_pi
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M] :
    ∀ z : M, GCompHolds (cov := cov) hmet z Real.pi := by
  obtain ⟨ρ, hρ, h⟩ := exists_uniform_GCompHolds (cov := cov) hmet htor hpinch
  exact Submission.HingeKey2.gcompHolds_pi_of_uniform (cov := cov) hmet htor hpinch hρ h


/-- **Toponogov's hinge comparison, applied form.**  The explicit inequality form of
`gcompHolds_pi`, isolated so that consumers do not have to unfold `GCompHolds`. -/
theorem gcompHolds_pi_apply
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {z : M} {a b : ℝ} {v w : TangentSpace I z}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < Real.pi) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hmina : Manifold.riemannianEDist I z (GExp (cov := cov) hmet z (a • v))
      = ENNReal.ofReal a)
    (hminb : Manifold.riemannianEDist I z (GExp (cov := cov) hmet z (b • w))
      = ENNReal.ofReal b) :
    Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v))
        (GExp (cov := cov) hmet z (b • w))
      ≤ ENNReal.ofReal (modelDist1 (hingeAngle v w) a b) :=
  gcompHolds_pi (cov := cov) hmet htor hpinch z a b v w ha hb hab hv hw hmina hminb

end

end Submission.HingePiece
