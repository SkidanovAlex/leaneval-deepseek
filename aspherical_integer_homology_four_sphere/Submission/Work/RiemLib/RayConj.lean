import Submission.Work.RiemLib.RayJacobi
import Submission.Work.RiemLib.RauchK
import Submission.Work.RiemLib.ChartGeoAt
import Submission.Work.RiemLib.GExpLocalInj
import Submission.Work.RiemLib.CutStep3
import Submission.Work.RiemLib.KlingenbergLoop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.RauchGlobal
open Submission.GeodesicExtend
open Submission.RauchK
open Submission.ChartConnection
open Submission.Distance
open Submission.ChartBounds
open Submission.CutStep2
open Submission.InjRadius

namespace Submission.RayConj

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {K : ℝ}
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

include I in
/-- An injective continuous linear map `E → T_qM` is invertible (finite dimensions). -/
theorem isInvertible_of_injective {q : M} {A : E →L[ℝ] TangentSpace I q}
    (h : Function.Injective A) : A.IsInvertible := by
  have hsurj : Function.Surjective A := (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp h
  refine ⟨(LinearEquiv.ofBijective A.toLinearMap ⟨h, hsurj⟩).toContinuousLinearEquiv, ?_⟩
  ext x
  rfl

/-- **A singular differential has a non-zero kernel vector.** -/
theorem exists_ne_zero_apply_eq_zero {q : M} {A : E →L[ℝ] TangentSpace I q}
    (h : ¬ A.IsInvertible) : ∃ ξ : E, ξ ≠ 0 ∧ A ξ = 0 := by
  have hnotinj : ¬ Function.Injective A := fun hinj => h (isInvertible_of_injective hinj)
  obtain ⟨a, b, hval, hab⟩ := Function.not_injective_iff.mp hnotinj
  exact ⟨a - b, sub_ne_zero.mpr hab, by rw [map_sub, hval, sub_self]⟩

/-- **(C)**: a singular differential of the exponential map at `w ≠ 0` forces `π/√K ≤ ‖w‖`. -/
theorem pi_div_sqrt_le_of_singular_mfderiv
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K) (hKpos : 0 < K) :
    ∀ (q : M) (w : TangentSpace I q), w ≠ 0 →
      ¬ (mfderiv 𝓘(ℝ, E) I
          (fun u : E => GExp (cov := cov) hmet q (show TangentSpace I q from u))
          (show E from w)).IsInvertible →
      Real.pi / Real.sqrt K ≤ ‖w‖ := by
  intro q w hw hsing
  by_contra hcon
  rw [not_le] at hcon
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  -- the kernel vector
  obtain ⟨ξ, hξ0, hξker⟩ := exists_ne_zero_apply_eq_zero (I := I) (q := q) (A := mfderiv 𝓘(ℝ, E) I
    (fun u : E => GExp (cov := cov) hmet q (show TangentSpace I q from u)) (show E from w)) hsing
  -- the unit direction and the perturbation
  set u : TangentSpace I q := ‖w‖⁻¹ • w with hu_def
  have hu1 : ‖u‖ = 1 := by
    rw [hu_def, norm_smul]
    rw [show ‖(‖w‖⁻¹ : ℝ)‖ * ‖w‖ = 1 from by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwpos),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]]
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0] at hu1; simp at hu1
  have hw_eq : ‖w‖ • u = w := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw), one_smul]
  set η : TangentSpace I q := ‖w‖⁻¹ • ξ with heta_def
  have heta0 : η ≠ 0 := by
    rw [heta_def]
    exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hw)) hξ0
  have heta_eq : ‖w‖ • η = ξ := by
    rw [heta_def, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw), one_smul]
  set uE : E := u with huE_def
  set ηE : E := η with hηE_def
  -- the ray and the variation field
  set γ : ℝ → M := fun s => GExp (cov := cov) hmet q (s • u) with hγ_def
  set J : (s : ℝ) → TangentSpace I (γ s) := fun s =>
    curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet q (s • (u + r • η))) 0 with hJ_def
  have hJac : ∀ t : ℝ, IsJacobiAt cov γ J t := fun t =>
    Submission.RayJacobi.isJacobiAt_GExp_variation (cov := cov) hmet htor hu0 hu1 t
  -- `J 0 = 0`
  have hJ0 : J 0 = 0 := by
    have hev : (fun r : ℝ => GExp (cov := cov) hmet q ((0:ℝ) • (u + r • η))) =ᶠ[𝓝 (0:ℝ)]
        (fun _ : ℝ => q) := by
      filter_upwards with r
      rw [zero_smul, GlobalExp.GExp_zero]
    rw [hJ_def]
    change curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet q ((0:ℝ) • (u + r • η))) 0 = 0
    rw [Submission.RayJacobi.curveVelocity_congr (I := I) hev]
    exact curveVelocity_const (I := I) q 0
  -- `J ‖w‖ = 0`, by the chain rule and the kernel condition
  have hpt : ‖w‖ • (u + (0:ℝ) • η) = w := by
    rw [zero_smul, add_zero]
    exact hw_eq
  have hJt : J ‖w‖ = 0 := by
    have h1 : HasDerivAt (fun r : ℝ => u + r • η) η (0:ℝ) := by
      have h := (hasDerivAt_id (0:ℝ)).smul_const η
      simpa using h.const_add u
    have hσ : HasDerivAt (fun r : ℝ => ‖w‖ • (u + r • η)) ξ (0:ℝ) := by
      have h2 : HasDerivAt (fun r : ℝ => ‖w‖ • (u + r • η)) (‖w‖ • η) (0:ℝ) := h1.const_smul ‖w‖
      rw [heta_eq] at h2
      exact h2
    have hsm : MDifferentiableAt 𝓘(ℝ, E) I
        (fun v : E => GExp (cov := cov) hmet q (show TangentSpace I q from v))
        (‖w‖ • (u + (0:ℝ) • η)) := by
      have h := Submission.GExpLocalInj.contMDiffAt_GExp_one (cov := cov) hmet q (‖w‖ • u)
      have h' : MDifferentiableAt 𝓘(ℝ, E) I
          (fun v : E => GExp (cov := cov) hmet q (show TangentSpace I q from v))
          (show E from (‖w‖ • u)) := h.mdifferentiableAt (by norm_num)
      simpa using h'
    have hchain := Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp (I := I)
      (f := fun v : E => GExp (cov := cov) hmet q (show TangentSpace I q from v))
      (σ := fun r : ℝ => ‖w‖ • (u + r • η)) (σ' := fun _ : ℝ => ξ)
      (γ := fun r : ℝ => GExp (cov := cov) hmet q (‖w‖ • (u + r • η))) hσ hsm
      (Filter.Eventually.of_forall (fun r => rfl))
    rw [hJ_def]
    change curveVelocity (I := I)
      (fun r : ℝ => GExp (cov := cov) hmet q (‖w‖ • (u + r • η))) 0 = 0
    rw [hchain]
    rw [hpt]
    exact hξker
  have hnontriv : ∃ s : ℝ, s ∈ Ioo (0:ℝ) ‖w‖ ∧ J s ≠ 0 := by    -- nontriviality: a positive parameter small enough for every input
    obtain ⟨ρe, hρe, hGExp_eq⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet q
    obtain ⟨ρj, hρj, hjac⟩ := Submission.FlowJacobi.exists_expMap_mfderiv_eq_jacobiTensor (cov := cov) htor q
    obtain ⟨ρc, hρc, hρcsm⟩ := exists_radius_contMDiffAt_expMap (cov := cov) q
    obtain ⟨ρs, hρs, hρssrc⟩ : ∃ ρ > (0:ℝ), ∀ σ : ℝ, |σ| < ρ →
        GExp (cov := cov) hmet q (σ • u) ∈ (chartAt H q).source := by
      have hcont : ContinuousAt (fun σ : ℝ => GExp (cov := cov) hmet q (σ • u)) 0 := by
        have hsm : ContMDiffOn 𝓘(ℝ) I ∞ (fun σ : ℝ => GExp (cov := cov) hmet q (σ • u)) univ :=
          Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hu0
        exact (hsm.contMDiffAt (Filter.univ_mem)).continuousAt
      have hmem : (fun σ : ℝ => GExp (cov := cov) hmet q (σ • u)) 0 ∈ (chartAt H q).source := by
        rw [show (fun σ : ℝ => GExp (cov := cov) hmet q (σ • u)) 0 = q from by
          simp [GlobalExp.GExp_zero]]
        exact mem_chart_source H q
      obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
        (hcont.preimage_mem_nhds ((chartAt H q).open_source.mem_nhds hmem))
      refine ⟨ε/2, by linarith, fun σ hσ => hεsub ?_⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [abs_lt.mp hσ]
    set C : ℝ := ‖uE‖ + 1 with hC_def
    have hCpos : 0 < C := by rw [hC_def]; positivity
    set s : ℝ := min (‖w‖ / 2)
      (min (ρe / 2) (min (ρj / (2 * C)) (min (ρc / (2 * C)) (ρs / 2)))) with hs_def
    have hs_le_t1 : s ≤ ‖w‖ / 2 := by rw [hs_def]; exact min_le_left _ _
    have hs_le_e : s ≤ ρe / 2 := by
      rw [hs_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hs_le_j : s ≤ ρj / (2 * C) := by
      rw [hs_def]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hs_le_c : s ≤ ρc / (2 * C) := by
      rw [hs_def]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hs_le_s : s ≤ ρs / 2 := by
      rw [hs_def]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hspos : 0 < s := by
      rw [hs_def]
      exact lt_min (by linarith) (lt_min (by linarith) (lt_min (div_pos hρj (by positivity))
        (lt_min (div_pos hρc (by positivity)) (by linarith))))
    have hst1 : s < ‖w‖ := by linarith
    have hsρe : s < ρe := by linarith
    have hsρs : s < ρs := by linarith
    have hmodel_eq : ‖(s : ℝ) • uE‖ = s * ‖uE‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
    have hmodel : ‖(s : ℝ) • uE‖ < min ρj ρc := by
      rw [hmodel_eq, lt_min_iff]
      constructor
      · have h1 : s * ‖uE‖ ≤ (ρj / (2 * C)) * ‖uE‖ :=
          mul_le_mul_of_nonneg_right hs_le_j (norm_nonneg uE)
        have h3 : (ρj / (2 * C)) * ‖uE‖ < ρj := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [hCpos, norm_nonneg uE, hC_def]
        linarith
      · have h1 : s * ‖uE‖ ≤ (ρc / (2 * C)) * ‖uE‖ :=
          mul_le_mul_of_nonneg_right hs_le_c (norm_nonneg uE)
        have h3 : (ρc / (2 * C)) * ‖uE‖ < ρc := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [hCpos, norm_nonneg uE, hC_def]
        linarith
    have hsρj : ‖(s : ℝ) • uE‖ < ρj := lt_of_lt_of_le hmodel (min_le_left _ _)
    have hsρc : ‖(s : ℝ) • uE‖ < ρc := lt_of_lt_of_le hmodel (min_le_right _ _)
    -- the fibre norm of `s • u` is `s`
    have hfib : ‖(s : ℝ) • u‖ = s := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos, hu1, mul_one]
    have hspi : Real.sqrt (chartGram (I := I) q q ((s : ℝ) • u) ((s : ℝ) • u)) < Real.pi / Real.sqrt K := by
      have hcg : chartGram (I := I) q q ((s : ℝ) • u) ((s : ℝ) • u) = s ^ 2 := by
        rw [chartGram_self_apply, real_inner_self_eq_norm_sq, hfib]
      rw [hcg, Real.sqrt_sq hspos.le]
      exact lt_of_lt_of_le hst1 hcon.le
    -- the Jacobi tensor at the velocity `s • u`
    obtain ⟨ut, wt, Y, U, hgc, hexp, hY0, hU0, hY, hU, hmf⟩ := hjac ((s : ℝ) • uE) hsρj ((s : ℝ) • ηE)
    have hv0' : ((s : ℝ) • uE) ≠ 0 := by
      intro h0
      refine (smul_ne_zero hspos.ne' hu0) ?_
      rw [huE_def]
      exact h0
    have hvinj : Function.Injective (Y 1) :=
      Submission.RauchK.jacobiTensor_injective_of_norm_lt_pi_div_sqrt_of_curvLe (cov := cov)
        htor hmet hK hKpos (x₀ := q) (v := ((s : ℝ) • uE)) hv0' hspi hgc hY hU hY0 hU0
    -- the chart source of the endpoint
    have hsrc : GExp (cov := cov) hmet q ((s : ℝ) • u) ∈ (chartAt H q).source := by
      refine hρssrc s ?_
      rw [abs_of_pos hspos]
      exact hsρs
    -- the key identity for `J s`
    have hJs_eq : J s = frameVector (I := I) q (GExp (cov := cov) hmet q ((s : ℝ) • u)) ((Y 1) ((s : ℝ) • η)) := by
      have hnb : ∀ᶠ r : ℝ in 𝓝 (0:ℝ), ‖(s : ℝ) • (u + r • η)‖ < ρe := by
        have hc : Continuous (fun r : ℝ => (s : ℝ) • (u + r • η)) := by fun_prop
        have hcont : ContinuousAt (fun r : ℝ => ‖(s : ℝ) • (u + r • η)‖) 0 := hc.continuousAt.norm
        have h0lt : ‖(s : ℝ) • (u + (0:ℝ) • η)‖ < ρe := by
          rw [zero_smul, add_zero, hfib]
          exact hsρe
        exact hcont.eventually (isOpen_Iio.mem_nhds h0lt)
      have hev : (fun r : ℝ => GExp (cov := cov) hmet q ((s : ℝ) • (u + r • η)))
          =ᶠ[𝓝 (0:ℝ)] (fun r : ℝ => expMap cov q ((s : ℝ) • (u + r • η))) := by
        filter_upwards [hnb] with r hr
        exact hGExp_eq ((s : ℝ) • (u + r • η)) hr
      have hder : HasDerivAt (fun r : ℝ => u + r • η) η (0:ℝ) := by
        have h := (hasDerivAt_id (0:ℝ)).smul_const η
        simpa using h.const_add u
      rw [hJ_def]
      change curveVelocity (I := I)
        (fun r : ℝ => GExp (cov := cov) hmet q ((s : ℝ) • (u + r • η))) 0 = _
      rw [Submission.RayJacobi.curveVelocity_congr (I := I) hev]
      have hσ : HasDerivAt (fun r : ℝ => (s : ℝ) • (u + r • η)) ((s : ℝ) • η) (0:ℝ) :=
        hder.const_smul s
      have hsm : MDifferentiableAt 𝓘(ℝ, E) I (fun v : E => expMap cov q v)
          ((s : ℝ) • (u + (0:ℝ) • η)) := by
        have h := hρcsm ((s : ℝ) • uE) hsρc
        have h' : MDifferentiableAt 𝓘(ℝ, E) I (fun v : E => expMap cov q v) ((s : ℝ) • uE) :=
          h.mdifferentiableAt (by norm_num)
        simpa using h'
      have hchain := Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp (I := I)
        (f := fun v : E => expMap cov q v) (σ := fun r : ℝ => (s : ℝ) • (u + r • η))
        (σ' := fun _ : ℝ => (s : ℝ) • η)
        (γ := fun r : ℝ => expMap cov q ((s : ℝ) • (u + r • η))) hσ hsm
        (Filter.Eventually.of_forall (fun r => rfl))
      rw [hchain]
      rw [show ((s : ℝ) • (u + (0:ℝ) • η)) = (s : ℝ) • u from by rw [zero_smul, add_zero]]
      have key : (mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov q v) ((s : ℝ) • u)) ((s : ℝ) • η)
          = frameVector (I := I) q (expMap cov q ((s : ℝ) • u)) ((Y 1) ((s : ℝ) • η)) := by
        simpa [huE_def, hηE_def] using hmf
      rw [key, ← hGExp_eq ((s : ℝ) • u) (by rw [hfib]; exact hsρe)]
    -- `J s ≠ 0`
    refine ⟨s, ⟨hspos, hst1⟩, ?_⟩
    intro hJs0
    rw [hJs_eq] at hJs0
    have hz : (Y 1) ((s : ℝ) • η) = 0 :=
      (Submission.ChartBounds.frameVector_eq_zero_iff (I := I) hsrc ((Y 1) ((s : ℝ) • η))).mp hJs0
    have hz2 : (s : ℝ) • η = 0 := hvinj (by rw [hz, map_zero])
    exact (smul_ne_zero hspos.ne' heta0) hz2


  -- Rauch's theorem gives the contradiction
  obtain ⟨s, hs, hsne⟩ := hnontriv
  have hz := Submission.RauchK.eqOn_zero_of_jacobi_of_curvLe (cov := cov)
    ‹ContMDiffCovariantDerivative cov ∞› hmet hK hKpos htor
    (show (-1 : ℝ) < 0 by norm_num) (show ‖w‖ < ‖w‖ + 1 by linarith)
    (fun t _ => hJac t) hwpos hcon hJ0 hJt
  exact hsne (hz s ⟨hs.1.le, hs.2.le⟩)

/-- **The exponential map is locally injective below the conjugate radius.**  This is the
`hloc_sphere` input of the cut-point step (`Submission/Roadmap.lean` §73.4, §84.5): for `sec ≤ K` and
`‖v‖ < π/√K`, `GExp p` is injective on a neighbourhood of `v`. -/
theorem locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : CurvLe cov K) (hKpos : 0 < K)
    {p : M} {v : TangentSpace I p} (hv0 : v ≠ 0)
    (hv : ‖v‖ < Real.pi / Real.sqrt K) :
    LocallyInjectiveAtGExp (I := I) hmet p v :=
  Submission.GExpLocalInj.locallyInjectiveAtGExp_of_lt_pi_div_sqrt (cov := cov) hmet
    (pi_div_sqrt_le_of_singular_mfderiv (cov := cov) htor hmet hK hKpos) hv0 hv

/-- **The cut-point step below the conjugate radius.**  If `sec ≤ K`, `0 < K`, `0 < m < π/√K` and
`m` is the injectivity radius of `p` (`InjAtLeast hmet p m` and maximal, `hfail`), then there are two
*distinct* tangent vectors of norm `m` with the same exponential image and
`d(p, GExp p u) = m`.

This is the hypothesis-free form of `CutStep3.exists_two_minimising_of_hloc_sphere`: the local
injectivity hypothesis on the sphere `‖w‖ = m` is now supplied by
`locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt` whenever `m < π/√K`. -/
theorem exists_two_minimising_of_injAtLeast_of_lt_pi_div_sqrt
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : CurvLe cov K) (hKpos : 0 < K)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hmpos : 0 < m) (hmπ : m < Real.pi / Real.sqrt K)
    (hinj : InjAtLeast hmet p m)
    (hfail : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r) :
    ∃ u v : TangentSpace I p, u ≠ v ∧
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v ∧
      ‖u‖ = m ∧ ‖v‖ = m ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal m := by
  refine Submission.CutStep3.exists_two_minimising_of_hloc_sphere (cov := cov) hmet htor hinj hfail ?_
  intro w hw
  refine locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt (cov := cov) hmet htor hK hKpos ?_ ?_
  · intro h0
    rw [h0, norm_zero] at hw
    linarith
  · rw [hw]
    exact hmπ

/-- **The broken minimising geodesic loop of length `2m`, below the conjugate radius.**  Under
`sec ≤ K`, `0 < K`, `0 < m < π/√K`, with `m` the (maximal) injectivity radius of `p`, the cut-point
step produces two distinct minimising rays of length `m` from `p` with a common endpoint, i.e. a
**broken minimising geodesic loop of length `2m`** through `p` (the classical Klingenberg loop). -/
theorem exists_broken_minimising_loop_of_injAtLeast_of_lt_pi_div_sqrt
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : CurvLe cov K) (hKpos : 0 < K)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hmpos : 0 < m) (hmπ : m < Real.pi / Real.sqrt K)
    (hinj : InjAtLeast hmet p m)
    (hfail : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r) :
    ∃ ξ η : TangentSpace I p, ‖ξ‖ = 1 ∧ ‖η‖ = 1 ∧ ξ ≠ η ∧
      GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η) ∧
      (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) 0 = p ∧
      (fun s : ℝ => GExp (cov := cov) hmet p ((m - s) • η)) 0
        = GExp (cov := cov) hmet p (m • ξ) ∧
      (fun s : ℝ => GExp (cov := cov) hmet p ((m - s) • η)) m = p ∧
      (∀ t ∈ Ioo (0 : ℝ) m, IsGeodesicAt cov (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t) ∧
      (∀ t ∈ Ioo (0 : ℝ) m,
        IsGeodesicAt cov (fun s : ℝ => GExp (cov := cov) hmet p ((m - s) • η)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) m,
        Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ)) = ENNReal.ofReal t) ∧
      (∀ t ∈ Icc (0 : ℝ) m,
        Manifold.riemannianEDist I p (GExp (cov := cov) hmet p ((m - t) • η))
          = ENNReal.ofReal (m - t)) := by
  obtain ⟨u, v, huv, hG, hu, hv, hmin⟩ :=
    exists_two_minimising_of_injAtLeast_of_lt_pi_div_sqrt (cov := cov) hmet htor hK hKpos
      hmpos hmπ hinj hfail
  exact Submission.KlingenbergLoop.exists_broken_minimising_loop (cov := cov) hmet htor hmpos hu hv
    huv hG hmin

end

end Submission.RayConj
