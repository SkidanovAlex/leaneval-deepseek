import Mathlib
import Submission.Work.RiemLib.Commons.Analysis.ODE.contDiffOn_infty_of_hasDerivAt
import Submission.Work.RiemLib.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Geometry.Manifold

open scoped _root_.Manifold _root_.ContDiff Topology Bundle
open _root_.Set _root_.Filter _root_.Bundle

theorem contMDiffAt_of_isMIntegralCurve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [I.Boundaryless] {v : (x : M) → TangentSpace I x} (hv : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : M => (⟨x, v x⟩ : TangentBundle I M))) {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) (t : ℝ) : ContMDiffAt (modelWithCornersSelf ℝ ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) γ t := by
  let x₀ : M := γ t
  let e : PartialEquiv M E := extChartAt I x₀
  let F : E → E := fun y =>
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (e.symm y) (v (e.symm y))
  -- step 0: smoothness of the chart representative `F` on the chart target
  have hv_on : ContMDiffOn I (I.prod (modelWithCornersSelf ℝ E)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) univ := hv.contMDiffOn
  have hg : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun q => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ q (v q))
      ((chartAt H x₀).source) := by
    simpa only [univ_inter] using
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiffOn_continuousLinearMapAt_section
        x₀ hv_on
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target :=
    contMDiffOn_extChartAt_symm x₀
  have hmaps : e.target ⊆ e.symm ⁻¹' (chartAt H x₀).source := by
    intro y hy
    rw [mem_preimage, ← extChartAt_source (I := I) x₀]
    exact e.map_target hy
  have hF_smooth : ContDiffOn ℝ ∞ F e.target := by
    have hcomp := hg.comp hsymm hmaps
    have h := (contMDiffOn_iff_contDiffOn).mp hcomp
    simpa only [Function.comp_def, F, e] using h
  -- step 1: find a small closed time interval around `t` on which `γ` stays in the chart source
  have hγc : Continuous γ := hγ.continuous
  have hsrc_nhds : γ ⁻¹' e.source ∈ 𝓝 t := by
    apply hγc.continuousAt.preimage_mem_nhds
    exact extChartAt_source_mem_nhds (I := I) x₀
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hsrc_nhds
  set a : ℝ := t - δ / 2 with ha
  set b : ℝ := t + δ / 2 with hb
  have hat : a < t := by rw [ha]; linarith
  have htb : t < b := by rw [hb]; linarith
  have hab : a < b := lt_trans hat htb
  have ht_ab : t ∈ Ioo a b := ⟨hat, htb⟩
  have hIcc_sub : Icc a b ⊆ γ ⁻¹' e.source := by
    intro s hs
    apply hδ
    rw [Real.ball_eq_Ioo, mem_Ioo]
    refine ⟨?_, ?_⟩
    · have h1 := hs.1; rw [ha] at h1; linarith
    · have h2 := hs.2; rw [hb] at h2; linarith
  -- step 2: the chart curve solves the ODE given by `F`
  have hode : ∀ s ∈ Icc a b, HasDerivAt (fun r => e (γ r)) (F (e (γ s))) s := by
    intro s hs
    have hsrc : γ s ∈ (extChartAt I x₀).source := hIcc_sub hs
    have hsrc' : γ s ∈ (chartAt H x₀).source := by
      rwa [extChartAt_source (I := I) x₀] at hsrc
    have hdw : HasDerivWithinAt (e ∘ γ)
        ((tangentCoordChange I (γ s) x₀ (γ s)) (v (γ s))) univ s :=
      (hγ.isMIntegralCurveOn univ).hasDerivWithinAt (t₀ := t) (t := s) (mem_univ s) hsrc
    rw [hasDerivWithinAt_univ] at hdw
    have hval : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ s)
        = tangentCoordChange I (γ s) x₀ (γ s) :=
      TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) hsrc'
    have hleft : e.symm (e (γ s)) = γ s := e.left_inv (hIcc_sub hs)
    have hder : F (e (γ s)) = (tangentCoordChange I (γ s) x₀ (γ s)) (v (γ s)) := by
      dsimp only [F]
      rw [hleft, hval]
      rfl
    rw [← hder] at hdw
    exact hdw
  -- step 3: continuity of the chart curve
  have hcont : ContinuousOn (fun r => e (γ r)) (Icc a b) := by
    have h1 : ContinuousOn (extChartAt I x₀) (extChartAt I x₀).source :=
      continuousOn_extChartAt x₀
    have h2 : ContinuousOn γ (Icc a b) := hγc.continuousOn
    have h3 : MapsTo γ (Icc a b) (extChartAt I x₀).source := fun s hs => hIcc_sub hs
    simpa only [e, Function.comp_def] using h1.comp h2 h3
  -- step 4: bootstrap
  have hmem : ∀ s ∈ Icc a b, (fun r => e (γ r)) s ∈ e.target := fun s hs =>
    e.map_source (hIcc_sub hs)
  have hboot : ContDiffOn ℝ ∞ (fun r => e (γ r)) (Icc a b) :=
    Commons.Analysis.ODE.contDiffOn_infty_of_hasDerivAt hab hF_smooth hmem hode hcont
  have hIcc_nhds : Icc a b ∈ 𝓝 t :=
    mem_of_superset (Ioo_mem_nhds ht_ab.1 ht_ab.2) Ioo_subset_Icc_self
  have hy_at : ContDiffAt ℝ ∞ (fun r => e (γ r)) t := hboot.contDiffAt hIcc_nhds
  -- step 5: transport back to the manifold
  have h1 : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun r => e (γ r)) t := hy_at.contMDiffAt
  have h2 : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm (e (γ t)) := by
    have htarget : (extChartAt I x₀).target ∈ 𝓝 (extChartAt I x₀ x₀) := by
      have h := extChartAt_target_mem_nhdsWithin (I := I) x₀
      rwa [ModelWithCorners.range_eq_univ, nhdsWithin_univ] at h
    exact (contMDiffWithinAt_extChartAt_symm_target_self (I := I) (x := x₀) (n := ∞)).contMDiffAt
      htarget
  have h3 : ContMDiffAt 𝓘(ℝ) I ∞ ((extChartAt I x₀).symm ∘ (fun r => e (γ r))) t :=
    h2.comp t h1
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [hsrc_nhds] with s hs
  exact (e.left_inv hs).symm

end Commons.Geometry.Manifold
