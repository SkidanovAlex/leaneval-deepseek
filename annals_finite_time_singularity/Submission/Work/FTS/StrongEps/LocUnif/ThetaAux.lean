import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.StrongEps.LocUnif.volume_box_sdiff_openBox

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option maxHeartbeats 1000000

/-! ## Helper lemmas for the `θ`-direction local-uniformity estimate -/

theorem Ioo_prod_ae_eq_Icc_prod (a b c d : ℝ) :
    (Set.Ioo a b ×ˢ Set.Ioo c d : Set (ℝ × ℝ)) =ᵐ[MeasureTheory.volume]
      (Set.Icc a b ×ˢ Set.Icc c d) := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, volume_box_sdiff_openBox a b c d⟩
  have hempty : ((Set.Ioo a b ×ˢ Set.Ioo c d : Set (ℝ × ℝ)) \
      (Set.Icc a b ×ˢ Set.Icc c d)) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
    exact hp.2 ⟨⟨le_of_lt hp.1.1.1, le_of_lt hp.1.1.2⟩,
      ⟨le_of_lt hp.1.2.1, le_of_lt hp.1.2.2⟩⟩
  rw [hempty, measure_empty]

theorem aemeasurable_of_continuousOn_openBox {a b c d : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo a b ×ˢ Set.Ioo c d)) :
    AEMeasurable f (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
  have h1 : AEMeasurable f (MeasureTheory.volume.restrict (Set.Ioo a b ×ˢ Set.Ioo c d)) :=
    hf.aemeasurable (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  convert h1 using 1
  exact (MeasureTheory.Measure.restrict_congr_set (Ioo_prod_ae_eq_Icc_prod a b c d)).symm

theorem continuousOn_pth_of_contDiffOn_one {a b c d : ℝ} {u : ℝ → ℝ → ℝ}
    (h1 : ContDiffOn ℝ 1 (Function.uncurry u) (Set.Ioo a b ×ˢ Set.Ioo c d)) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (fun θ' => u p.1 θ') p.2)
      (Set.Ioo a b ×ˢ Set.Ioo c d) := by
  have hV : IsOpen (Set.Ioo a b ×ˢ Set.Ioo c d) := isOpen_Ioo.prod isOpen_Ioo
  have hfd : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry u) p (0, 1))
      (Set.Ioo a b ×ˢ Set.Ioo c d) :=
    (h1.continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const
  refine hfd.congr fun p hp => ?_
  simpa only [Work.Spaces.pth] using
    (Work.Spaces.pth_eq_fderiv ((h1.differentiableOn (by simp)).differentiableAt
      (hV.mem_nhds hp)))

theorem aemeasurable_pth_sq_mul {a b c d : ℝ} {u w : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 (Function.uncurry u) (Set.Ioo a b ×ˢ Set.Ioo c d))
    (hw : ContinuousOn (Function.uncurry w) (Set.Icc a b ×ˢ Set.Icc c d)) :
    AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((deriv (fun θ' => u p.1 θ') p.2) ^ 2 * (w p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (deriv (fun θ' => u p.1 θ') p.2) ^ 2 * (w p.1 p.2) ^ 2)
      (Set.Ioo a b ×ˢ Set.Ioo c d) := by
    have h2 : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Set.Ioo a b ×ˢ Set.Ioo c d) :=
      hw.mono fun p hp => ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩,
        ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩⟩
    exact ((continuousOn_pth_of_contDiffOn_one hu).pow 2).mul (h2.pow 2)
  have h3 := aemeasurable_of_continuousOn_openBox hcont
  have h4a : AEMeasurable (fun p : ℝ × ℝ =>
      ‖(deriv (fun θ' => u p.1 θ') p.2) ^ 2 * (w p.1 p.2) ^ 2‖ₑ)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    AEStronglyMeasurable.enorm h3.aestronglyMeasurable
  refine AEMeasurable.congr h4a (Eventually.of_forall fun p => ?_)
  exact Real.enorm_eq_ofReal (by positivity)

theorem rho_bounds_theta {a b c d : ℝ} {ρ : ℝ → ℝ → ℝ}
    (hρc : ContinuousOn (Function.uncurry ρ) (Set.Icc a b ×ˢ Set.Icc c d)) :
    ∀ ε > 0, ∃ δ > 0, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ∀ y ∈ Set.Icc c d,
      |θ - y| < δ → |ρ z θ - ρ z y| < ε := by
  intro ε hε
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) :=
    (isCompact_Icc (a := a) (b := b)).prod (isCompact_Icc (a := c) (b := d))
  have hunif : UniformContinuousOn (Function.uncurry ρ) (Set.Icc a b ×ˢ Set.Icc c d) :=
    hK.uniformContinuousOn_of_continuous hρc
  obtain ⟨δ, hδ, hδ'⟩ := (Metric.uniformContinuousOn_iff.mp hunif) ε hε
  refine ⟨δ, hδ, fun z hz θ hθ y hy hθy => ?_⟩
  have hd : dist (z, θ) (z, y) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Real.dist_eq]
    exact hθy
  have hres := hδ' (z, θ) ⟨hz, hθ⟩ (z, y) ⟨hz, hy⟩ hd
  rwa [Real.dist_eq] at hres

theorem liminf_le_liminf_of_le' {u v : ℕ → ℝ≥0∞} (h : ∀ j, u j ≤ v j) :
    Filter.liminf u Filter.atTop ≤ Filter.liminf v Filter.atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
  refine iSup_le fun n => ?_
  refine le_trans ?_ (le_iSup (fun n => ⨅ i, ⨅ (_ : i ≥ n), v i) n)
  refine le_iInf fun i => le_iInf fun hi => ?_
  exact le_trans (le_trans (iInf_le _ i) (iInf_le _ hi)) (h i)

theorem liminf_le_of_eventually_le_const {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞} {K : ℕ}
    (h : ∀ j ≥ K, u j ≤ c) : Filter.liminf u Filter.atTop ≤ c := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat]
  refine iSup_le fun n => ?_
  rcases le_or_gt n K with hn | hn
  · refine le_trans ?_ (h K le_rfl)
    exact le_trans (iInf_le _ K) (iInf_le _ (le_trans hn le_rfl))
  · exact le_trans (le_trans (iInf_le _ n) (iInf_le _ le_rfl)) (h n (le_of_lt hn))

theorem liminf_const_mul_of_ne_top {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) (x : ℕ → ℝ≥0∞) :
    Filter.liminf (fun n => c * x n) Filter.atTop = c * Filter.liminf x Filter.atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat, ENNReal.mul_iSup]
  refine iSup_congr fun n => ?_
  rw [iInf_subtype' (p := fun i : ℕ => i ≥ n) (f := fun i _ => c * x i),
    iInf_subtype' (p := fun i : ℕ => i ≥ n) (f := fun i _ => x i),
    ENNReal.mul_iInf_of_ne hc0 hct]

theorem setLIntegral_mono_subset {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α}
    {f : α → ℝ≥0∞} (hsm : MeasurableSet s) (htm : MeasurableSet t) (h : s ⊆ t) :
    ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ := by
  rw [← MeasureTheory.lintegral_indicator hsm f, ← MeasureTheory.lintegral_indicator htm f]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (h hx)]
  · rw [Set.indicator_of_notMem hx]
    exact bot_le

end Work.FTS.StrongEps.LocUnif
