import Mathlib
import Submission.Work.LeviCivita.ChartMetric
import Submission.Work.Curvature.Bridge
import Submission.Work.RiemLib.Distance

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LeviCivita

open scoped Manifold ContDiff Bundle Topology in
theorem chartDg_eq_chartGram_chrB
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (x₀ p : M) (hp : p ∈ (chartAt H x₀).source) (v a b : E) :
    Work.Curvature.chartDg (I := I) x₀ p v a b =
      Submission.ChartConnection.chartGram (I := I) x₀ p
          (Submission.ChartCurv.chrB cov x₀ p a v) b
        + Submission.ChartConnection.chartGram (I := I) x₀ p a
          (Submission.ChartCurv.chrB cov x₀ p b v) := by
  have hx₁ : extChartAt I x₀ p ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hp)
  have hep : (extChartAt I x₀).symm (extChartAt I x₀ p) = p :=
    (extChartAt I x₀).left_inv (by rw [extChartAt_source]; exact hp)
  -- differentiability of the chart metric pulled back to the model space `E`
  have he : ContMDiffAt 𝓘(ℝ, E) I ∞ (fun q : E => (extChartAt I x₀).symm q)
      (extChartAt I x₀ p) :=
    (contMDiffWithinAt_extChartAt_symm_range x₀ hx₁).contMDiffAt
      (by rw [ModelWithCorners.range_eq_univ]; exact Filter.univ_mem)
  have hc : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q : M => Submission.ChartConnection.chartGram (I := I) x₀ q a b)
      ((extChartAt I x₀).symm (extChartAt I x₀ p)) := by
    rw [hep]
    exact Submission.Distance.contMDiffAt_chartGram x₀ a b hp
  have hge : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      ((fun q : M => Submission.ChartConnection.chartGram (I := I) x₀ q a b) ∘
        (fun q : E => (extChartAt I x₀).symm q)) (extChartAt I x₀ p) :=
    hc.comp (extChartAt I x₀ p) he
  have hgdiff : DifferentiableAt ℝ
      (fun q : E =>
        Submission.ChartConnection.chartGram (I := I) x₀ ((extChartAt I x₀).symm q) a b)
      (extChartAt I x₀ p) :=
    ((contMDiffAt_iff_contDiffAt).mp hge).differentiableAt (by simp)
  have hF := hgdiff.hasFDerivAt
  -- the line through the chart image of `p` in direction `v`
  have hu : HasDerivAt (fun s : ℝ => extChartAt I x₀ p + s • v) v 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • v) v 0 := by
      simpa using (hasDerivAt_id' (0 : ℝ)).smul_const v
    simpa using h1.const_add (extChartAt I x₀ p)
  have htgt : (fun s : ℝ => extChartAt I x₀ p + s • v) 0 ∈ (extChartAt I x₀).target := by
    simpa using hx₁
  have hstay : ∀ᶠ s in 𝓝 (0 : ℝ),
      (fun s : ℝ => extChartAt I x₀ p + s • v) s ∈ (extChartAt I x₀).target := by
    have hcont : ContinuousAt (fun s : ℝ => extChartAt I x₀ p + s • v) 0 :=
      continuousAt_const.add (continuousAt_id.smul continuousAt_const)
    exact hcont.preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds (x := (fun s : ℝ => extChartAt I x₀ p + s • v) 0)
        (by simpa using hx₁))
  have hcurve := Submission.ChartConnection.hasDerivAt_chartGram_const_curve
    cov hmet x₀ a b hu htgt hstay
  have hF' : HasFDerivAt
      (fun q : E =>
        Submission.ChartConnection.chartGram (I := I) x₀ ((extChartAt I x₀).symm q) a b)
      (fderiv ℝ (fun q : E =>
        Submission.ChartConnection.chartGram (I := I) x₀ ((extChartAt I x₀).symm q) a b)
        (extChartAt I x₀ p))
      ((fun s : ℝ => extChartAt I x₀ p + s • v) 0) := by
    simpa using hF
  have hchain := hF'.comp_hasDerivAt 0 hu
  have hkey := hchain.unique hcurve
  have hsym : (extChartAt I x₀).symm ((fun s : ℝ => extChartAt I x₀ p + s • v) 0) = p := by
    rw [show (fun s : ℝ => extChartAt I x₀ p + s • v) 0 = extChartAt I x₀ p by simp]
    exact hep
  rw [hsym, ← Submission.ChartCurv.chrB_apply cov x₀ p a v,
    ← Submission.ChartCurv.chrB_apply cov x₀ p b v] at hkey
  change fderiv ℝ (fun q : E =>
      Submission.ChartConnection.chartGram (I := I) x₀ ((extChartAt I x₀).symm q) a b)
      (extChartAt I x₀ p) v = _
  exact hkey

end Work.LeviCivita
