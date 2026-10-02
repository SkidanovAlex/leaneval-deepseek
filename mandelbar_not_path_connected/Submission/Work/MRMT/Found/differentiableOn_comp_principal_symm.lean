import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.lintegralAbsDbar_comp_eq
import Submission.Work.MRMT.Found.differentiableOn_of_tendstoLocallyUniformly_of_lintegral_tendsto
import Submission.Work.MRMT.Found.differentiableOn_of_tendstoLocallyUniformlyOn_of_lintegral_tendsto
import Submission.Work.MRMT.Found.tendsto_lintegral_ofReal_mul_of_ae_tendsto_zero
import Submission.Work.MRMT.QC.lintegral_norm_dz_le_volume_image
import Submission.Work.MRMT.QC.locallyIntegrableOn_dz_of_lipschitzOnWith

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

lemma norm_dz_le_of_lipschitzOnWith {g : ℂ → ℂ} {s : Set ℂ} {z : ℂ} (hs : s ∈ 𝓝 z) {C : NNReal}
    (h : LipschitzOnWith C g s) : ‖dz g z‖ ≤ (C : ℝ) :=
  Work.MRMT.QC.norm_dz_le_of_norm_fderiv_le (norm_fderiv_le_of_lipschitzOn ℝ hs h)

lemma lintegral_norm_dz_sq_le_volume_image_aux {φ μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hμ : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hrel : ∀ᵐ z ∂(volume : Measure ℂ), dzbar φ z = μ z * dz φ z)
    (hφ : ContDiff ℝ 1 φ) (hinj : Function.Injective φ) {K : Set ℂ} (hK : IsCompact K) :
    ∫⁻ z in K, ENNReal.ofReal (‖dz φ z‖ ^ 2)
      ≤ ENNReal.ofReal ((1 - k ^ 2)⁻¹) * (volume (φ '' K) : ℝ≥0∞) := by
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hae := Work.MRMT.QC.ofReal_normSq_dz_le_det (φ := φ) (μ := μ) hk hk1 hμ hrel
  have hderiv : ∀ x ∈ K, HasFDerivWithinAt φ (fderiv ℝ φ x) K x := fun x _ =>
    (hφ.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  have hinjK : Set.InjOn φ K := hinj.injOn
  have hcov : ∫⁻ x in K, ENNReal.ofReal |(fderiv ℝ φ x).det|
      = (volume (φ '' K) : ℝ≥0∞) :=
    lintegral_abs_det_fderiv_eq_addHaar_image (f := φ) (f' := fun z => fderiv ℝ φ z) volume
      hKmeas hderiv hinjK
  have hstep1 : ∫⁻ z in K, ENNReal.ofReal (‖dz φ z‖ ^ 2)
      ≤ ∫⁻ z in K, ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ENNReal.ofReal |(fderiv ℝ φ z).det| :=
    setLIntegral_mono_ae' hKmeas (hae.mono (fun z hz _ => hz))
  have hconst : ∫⁻ z in K, ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ENNReal.ofReal |(fderiv ℝ φ z).det|
      = ENNReal.ofReal ((1 - k ^ 2)⁻¹) * ∫⁻ z in K, ENNReal.ofReal |(fderiv ℝ φ z).det| :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [hconst, hcov] at hstep1
  exact hstep1


private theorem tendsto_lintegralAbsDbar_comp_symm {μ : ℂ → ℂ} (hμ : Admissible μ) (d : PrincipalData μ)
    {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ} (hg : LocallyLipschitzOn U g)
    (hrel : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U → dzbar g z = μ z * dz g z)
    {z : ℂ} {ρ : ℝ} (hρU : Metric.closedBall z ρ ⊆ U)
    {L : Set ℂ} (hL : IsCompact L) (hLsub : L ⊆ (d.φ : ℂ → ℂ) '' Metric.ball z ρ) :
    Tendsto (fun n => lintegralAbsDbar (g ∘ ((d.Fn n).symm : ℂ → ℂ)) L) atTop (nhds 0) := by
  set A : Set ℂ := Metric.closedBall z ρ with hAdef
  have hAcpt : IsCompact A := isCompact_closedBall z ρ
  have hAU : A ⊆ U := hρU
  obtain ⟨ε, hεpos, hεU⟩ := hAcpt.exists_cthickening_subset_open hU hAU
  set Ω : Set ℂ := Metric.cthickening ε A with hΩdef
  set Ωc : Set ℂ := Metric.thickening ε A with hΩcdef
  have hΩcpt : IsCompact Ω := hAcpt.cthickening
  have hΩU : Ω ⊆ U := hεU
  have hΩcΩ : Ωc ⊆ Ω := Metric.thickening_subset_cthickening ε A
  have hΩcop : IsOpen Ωc := Metric.isOpen_thickening
  have hΩcfin : (volume Ωc : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top hΩcpt.measure_lt_top.ne (measure_mono hΩcΩ)
  have hΩcU : Ωc ⊆ U := hΩcΩ.trans hΩU
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hΩcpt (hg.mono hΩU)
  have hCΩc : LipschitzOnWith C g Ωc := hC.mono hΩcΩ
  have hk0 : 0 ≤ d.k := le_trans (norm_nonneg ((d.μn 0) 0)) (d.norm_μn 0 0)
  have hk1 : d.k < 1 := d.hk
  have hpos : 0 < 1 - d.k ^ 2 := by nlinarith [hk0, hk1]
  have hUnif : TendstoUniformlyOn (fun n => ((d.Fn n).symm : ℂ → ℂ)) ((d.φ.symm) : ℂ → ℂ) atTop L :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp d.tendsto_symm_Fn) L hL
  have hφL : ∀ x ∈ L, (d.φ.symm : ℂ → ℂ) x ∈ A := by
    intro x hx
    obtain ⟨b, hb, hbx⟩ := hLsub hx
    rw [← hbx]
    simpa [A] using Metric.ball_subset_closedBall hb
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, ∀ x ∈ L, dist ((d.φ.symm : ℂ → ℂ) x) ((d.Fn n).symm x) < ε :=
    Filter.eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hUnif) ε hεpos)
  have hKL : ∀ n ≥ N, ((d.Fn n).symm : ℂ → ℂ) '' L ⊆ Ωc := by
    intro n hn x hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Metric.mem_thickening_iff]
    exact ⟨(d.φ.symm : ℂ → ℂ) y, hφL y hy, by rw [dist_comm]; exact hN n hn y hy⟩
  have himg : ∀ n, (d.Fn n : ℂ → ℂ) '' (((d.Fn n).symm : ℂ → ℂ) '' L) = L := by
    intro n
    rw [Set.image_image]
    have h : (fun x => (d.Fn n) ((d.Fn n).symm x)) = id := by
      funext x; exact Homeomorph.apply_symm_apply _ x
    rw [h, Set.image_id]
  have hJac : ∀ n, ∫⁻ w in (((d.Fn n).symm : ℂ → ℂ) '' L),
      ENNReal.ofReal (‖dz ((d.Fn n) : ℂ → ℂ) w‖ ^ 2)
      ≤ ENNReal.ofReal ((1 - d.k ^ 2)⁻¹) * (volume L : ℝ≥0∞) := by
    intro n
    have hKc : IsCompact (((d.Fn n).symm : ℂ → ℂ) '' L) := hL.image ((d.contDiff_symm_Fn n).continuous)
    have h := lintegral_norm_dz_sq_le_volume_image_aux (φ := ((d.Fn n) : ℂ → ℂ)) (μ := d.μn n)
      hk0 hk1 (Eventually.of_forall (d.norm_μn n)) (Eventually.of_forall (d.beltrami_Fn n))
      (d.contDiff_Fn n) (d.Fn n).injective hKc
    rw [himg n] at h
    exact h
  set b' : ℕ → ℂ → ℂ := fun n => (((d.Fn n).symm : ℂ → ℂ) '' L).indicator
      (fun w => dz ((d.Fn n) : ℂ → ℂ) w) with hb'def
  have hb'meas : ∀ n, AEStronglyMeasurable (b' n) volume := by
    intro n
    have hKm : MeasurableSet (((d.Fn n).symm : ℂ → ℂ) '' L) :=
      (hL.image ((d.contDiff_symm_Fn n).continuous)).measurableSet
    exact (Work.MRMT.QC.measurable_dz ((d.Fn n) : ℂ → ℂ)).aestronglyMeasurable.indicator hKm
  have hνmeas : ∀ n, AEStronglyMeasurable (fun w => μ w - d.μn n w) volume := by
    intro n
    exact (hμ.meas.aemeasurable.sub
      ((d.contDiff_μn n).continuous.measurable.aemeasurable)).aestronglyMeasurable
  have hν0 : ∀ᵐ w ∂(volume : Measure ℂ),
      Tendsto (fun n => μ w - d.μn n w) atTop (𝓝 0) := by
    filter_upwards [d.tendsto_μn] with w hw
    have h1 : Tendsto (fun n => μ w - d.μn n w) atTop (𝓝 (μ w - μ w)) :=
      tendsto_const_nhds.sub hw
    simpa only [sub_self] using h1
  have hνb : ∀ n, ∀ᵐ w ∂(volume : Measure ℂ), ‖μ w - d.μn n w‖ ≤ 2 := by
    intro n
    obtain ⟨k0, hk0lt, hk0b⟩ := hμ.bound
    filter_upwards [hk0b] with w hw
    calc ‖μ w - d.μn n w‖ ≤ ‖μ w‖ + ‖d.μn n w‖ := norm_sub_le _ _
      _ ≤ k0 + d.k := add_le_add hw (d.norm_μn n w)
      _ ≤ 2 := by linarith
  have hbbnd : ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      ∫⁻ w in Ωc, ENNReal.ofReal (‖b' n w‖ ^ 2) ≤ ENNReal.ofReal (B ^ 2) := by
    refine ⟨Real.sqrt ((1 - d.k ^ 2)⁻¹ * (volume L).toReal), Real.sqrt_nonneg _, fun n => ?_⟩
    have hKm : MeasurableSet (((d.Fn n).symm : ℂ → ℂ) '' L) :=
      (hL.image ((d.contDiff_symm_Fn n).continuous)).measurableSet
    have hpt : ∀ w, ENNReal.ofReal (‖b' n w‖ ^ 2)
        = ((((d.Fn n).symm : ℂ → ℂ) '' L).indicator
            (fun w => ENNReal.ofReal (‖dz ((d.Fn n) : ℂ → ℂ) w‖ ^ 2))) w := by
      intro w
      rw [hb'def]
      by_cases hw : w ∈ (((d.Fn n).symm : ℂ → ℂ) '' L)
      · simp [Set.indicator_of_mem hw]
      · simp [Set.indicator_of_notMem hw]
    rw [lintegral_congr hpt]
    rw [setLIntegral_indicator hKm]
    have h1 : ∫⁻ w in (((d.Fn n).symm : ℂ → ℂ) '' L) ∩ Ωc,
        ENNReal.ofReal (‖dz ((d.Fn n) : ℂ → ℂ) w‖ ^ 2)
        ≤ ∫⁻ w in (((d.Fn n).symm : ℂ → ℂ) '' L),
        ENNReal.ofReal (‖dz ((d.Fn n) : ℂ → ℂ) w‖ ^ 2) :=
      lintegral_mono_set Set.inter_subset_left
    refine h1.trans ?_
    rw [Real.sq_sqrt (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_toReal hL.measure_lt_top.ne]
    exact hJac n
  have hmain := tendsto_lintegral_ofReal_mul_of_ae_tendsto_zero (Ω := Ωc) hΩcop.measurableSet
    hΩcfin C.coe_nonneg hνmeas hb'meas hν0 hνb hbbnd
  have hadv : ∀ᶠ n in atTop, lintegralAbsDbar (g ∘ ((d.Fn n).symm : ℂ → ℂ)) L
      ≤ ∫⁻ w in Ωc, ENNReal.ofReal ((C : ℝ) * ‖μ w - d.μn n w‖ * ‖b' n w‖) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hKc : IsCompact (((d.Fn n).symm : ℂ → ℂ) '' L) := hL.image ((d.contDiff_symm_Fn n).continuous)
    have hKsub : ((d.Fn n).symm : ℂ → ℂ) '' L ⊆ Ω := (hKL n hn).trans hΩcΩ
    have hLipK : LipschitzOnWith C g (((d.Fn n).symm : ℂ → ℂ) '' L) := hC.mono hKsub
    have hcov := lintegralAbsDbar_comp_eq (F := d.Fn n) (μF := d.μn n) (H := g)
      (K := ((d.Fn n).symm : ℂ → ℂ) '' L) hKc (d.contDiff_Fn n) (d.contDiff_symm_Fn n)
      (d.beltrami_Fn n) C hLipK
    rw [himg n] at hcov
    rw [hcov]
    unfold lintegralAbsBeltrami
    have hbound : ∀ᵐ w ∂(volume : Measure ℂ), w ∈ (((d.Fn n).symm : ℂ → ℂ) '' L) →
        ENNReal.ofReal (‖dzbar g w - d.μn n w * dz g w‖
            * ‖dz ((d.Fn n) : ℂ → ℂ) w‖)
          ≤ ENNReal.ofReal ((C : ℝ) * ‖μ w - d.μn n w‖
            * ‖dz ((d.Fn n) : ℂ → ℂ) w‖) := by
      filter_upwards [hrel] with w hw hwK
      have hwU : w ∈ U := hΩcU (hKL n hn hwK)
      have hdz : ‖dz g w‖ ≤ (C : ℝ) :=
        norm_dz_le_of_lipschitzOnWith (hΩcop.mem_nhds (hKL n hn hwK)) hCΩc
      rw [hw hwU, ← sub_mul, norm_mul]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : ‖μ w - d.μn n w‖ * ‖dz g w‖ ≤ (C : ℝ) * ‖μ w - d.μn n w‖ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hdz (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have hstep := setLIntegral_mono_ae' hKc.measurableSet hbound
    refine hstep.trans (le_of_eq ?_)
    have hpt2 : ∀ w, ENNReal.ofReal ((C : ℝ) * ‖μ w - d.μn n w‖ * ‖b' n w‖)
        = ((((d.Fn n).symm : ℂ → ℂ) '' L).indicator
            (fun w => ENNReal.ofReal ((C : ℝ) * ‖μ w - d.μn n w‖
              * ‖dz ((d.Fn n) : ℂ → ℂ) w‖))) w := by
      intro w
      rw [hb'def]
      by_cases hw : w ∈ (((d.Fn n).symm : ℂ → ℂ) '' L)
      · simp [Set.indicator_of_mem hw]
      · simp [Set.indicator_of_notMem hw]
    rw [lintegral_congr hpt2]
    rw [setLIntegral_indicator hKc.measurableSet]
    rw [Set.inter_eq_left.mpr (hKL n hn)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmain ?_ hadv
  filter_upwards with n
  exact bot_le


lemma TendstoLocallyUniformlyOn.comp_add {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {s : Set ℂ}
    (h : TendstoLocallyUniformlyOn F f atTop s) (N : ℕ) :
    TendstoLocallyUniformlyOn (fun n => F (n + N)) f atTop s := by
  intro u hu x hx
  obtain ⟨t, ht, H⟩ := h u hu x hx
  refine ⟨t, ht, ?_⟩
  rw [Filter.eventually_atTop] at H ⊢
  obtain ⟨M, hM⟩ := H
  exact ⟨M, fun n hn y hy => hM (n + N) (by omega) y hy⟩

lemma locallyLipschitzOn_of_lipschitzOnWith_of_isOpen {s : Set ℂ} (hs : IsOpen s) {K : NNReal}
    {f : ℂ → ℂ} (h : LipschitzOnWith K f s) : LocallyLipschitzOn s f :=
  fun x hx => ⟨K, s, by
    rw [nhdsWithin_eq_nhds.mpr (hs.mem_nhds hx)]
    exact hs.mem_nhds hx, h⟩

private theorem differentiableOn_comp_principal_symm_local {μ : ℂ → ℂ} (hμ : Admissible μ)
    (d : PrincipalData μ) {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ} (hg : LocallyLipschitzOn U g)
    (hrel : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U → dzbar g z = μ z * dz g z)
    {z : ℂ} {ρ : ℝ} (hρpos : 0 < ρ) (hρU : Metric.closedBall z ρ ⊆ U) :
    DifferentiableOn ℂ (g ∘ ((d.φ).symm : ℂ → ℂ)) ((d.φ : ℂ → ℂ) '' Metric.ball z ρ) := by
  set φ := d.φ
  set B : Set ℂ := Metric.ball z ρ with hBdef
  set A : Set ℂ := Metric.closedBall z ρ with hAdef
  set W : Set ℂ := (φ : ℂ → ℂ) '' B with hWdef
  have hWopen : IsOpen W := φ.isOpenMap B Metric.isOpen_ball
  have hclW : closure W = (φ : ℂ → ℂ) '' A := by
    rw [hWdef, hBdef, hAdef, ← φ.image_closure, closure_ball z hρpos.ne']
  have hAcpt : IsCompact A := isCompact_closedBall z ρ
  have hclWcpt : IsCompact (closure W) := by rw [hclW]; exact hAcpt.image φ.continuous
  obtain ⟨ε, hεpos, hεU⟩ := hAcpt.exists_cthickening_subset_open hU hρU
  set Ωc : Set ℂ := Metric.thickening ε A with hΩcdef
  set Ω : Set ℂ := Metric.cthickening ε A with hΩdef
  have hΩcpt : IsCompact Ω := hAcpt.cthickening
  have hΩcΩ : Ωc ⊆ Ω := Metric.thickening_subset_cthickening ε A
  have hΩU : Ω ⊆ U := hεU
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hΩcpt (hg.mono hΩU)
  have hCΩc : LipschitzOnWith C g Ωc := hC.mono hΩcΩ
  have hUnif : TendstoUniformlyOn (fun n => ((d.Fn n).symm : ℂ → ℂ)) ((φ.symm) : ℂ → ℂ) atTop (closure W) :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp d.tendsto_symm_Fn) (closure W) hclWcpt
  have hφcl : ∀ x ∈ closure W, (φ.symm : ℂ → ℂ) x ∈ A := by
    intro x hx
    rw [hclW] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simpa using ha
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, ∀ x ∈ closure W, dist ((φ.symm : ℂ → ℂ) x) ((d.Fn n).symm x) < ε :=
    Filter.eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hUnif) ε hεpos)
  have hKN : ∀ n ≥ N, ((d.Fn n).symm : ℂ → ℂ) '' (closure W) ⊆ Ωc := by
    intro n hn x hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Metric.mem_thickening_iff]
    exact ⟨(φ.symm : ℂ → ℂ) y, hφcl y hy, by rw [dist_comm]; exact hN n hn y hy⟩
  have hGn : ∀ n, LocallyLipschitzOn W (fun w => g ((d.Fn (n + N)).symm w)) := by
    intro n
    obtain ⟨Ln, hLn⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hclWcpt
      ((d.contDiff_symm_Fn (n + N)).locallyLipschitz.locallyLipschitzOn)
    have hmap : Set.MapsTo ((d.Fn (n + N)).symm : ℂ → ℂ) (closure W) Ω := fun x hx =>
      hΩcΩ (hKN (n + N) (by omega) (Set.mem_image_of_mem _ hx))
    have hcomp : LipschitzOnWith (C * Ln) (fun w => g ((d.Fn (n + N)).symm w)) (closure W) :=
      LipschitzOnWith.comp hC hLn hmap
    exact locallyLipschitzOn_of_lipschitzOnWith_of_isOpen hWopen (hcomp.mono subset_closure)
  have hconv : TendstoLocallyUniformlyOn (fun n => (fun w => g ((d.Fn (n + N)).symm w)))
      (fun w => g ((φ.symm : ℂ → ℂ) w)) atTop W := by
    have hinner0 : TendstoLocallyUniformlyOn (fun n => ((d.Fn n).symm : ℂ → ℂ)) (φ.symm) atTop W :=
      d.tendsto_symm_Fn.tendstoLocallyUniformlyOn
    have hinner : TendstoLocallyUniformlyOn (fun n => ((d.Fn (n + N)).symm : ℂ → ℂ)) (φ.symm) atTop W :=
      TendstoLocallyUniformlyOn.comp_add hinner0 N
    refine UniformContinuousOn.comp_tendstoLocallyUniformlyOn (g := g) (t := Ω)
      hC.uniformContinuousOn hinner ?_ ?_
    · intro x hx
      rw [hWdef] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hΩcΩ (Metric.self_subset_thickening hεpos A
        (Metric.ball_subset_closedBall (by simpa [hBdef] using hy)))
    · filter_upwards with n
      intro x hx
      exact hΩcΩ (hKN (n + N) (by omega) (Set.mem_image_of_mem _ (subset_closure hx)))
  have h0 : ∀ L : Set ℂ, IsCompact L → L ⊆ W →
      Tendsto (fun n => lintegralAbsDbar (fun w => g ((d.Fn (n + N)).symm w)) L) atTop (nhds 0) := by
    intro L hL hLW
    have hLW' : L ⊆ (d.φ : ℂ → ℂ) '' Metric.ball z ρ := by
      rwa [hWdef, hBdef] at hLW
    have hEst := tendsto_lintegralAbsDbar_comp_symm hμ d hU hg hrel hρU hL hLW'
    exact hEst.comp (tendsto_add_atTop_nat N)
  have hres := differentiableOn_of_tendstoLocallyUniformlyOn_of_lintegral_tendsto hWopen hGn hconv h0
  simpa only [hWdef, hBdef, Function.comp_def] using hres


theorem differentiableOn_comp_principal_symm {μ : ℂ → ℂ} (hμ : Admissible μ) (d : PrincipalData μ)
    {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ} (hg : LocallyLipschitzOn U g)
    (hrel : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), z ∈ U → dzbar g z = μ z * dz g z) :
    DifferentiableOn ℂ (g ∘ ((d.φ).symm : ℂ → ℂ)) ((d.φ : ℂ → ℂ) '' U) := by
  refine differentiableOn_of_locally_differentiableOn (s := (d.φ : ℂ → ℂ) '' U) fun w hw => ?_
  obtain ⟨u, huU, huw⟩ := hw
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds huU)
  refine ⟨(d.φ : ℂ → ℂ) '' Metric.ball u (δ/2),
    d.φ.isOpenMap (Metric.ball u (δ/2)) Metric.isOpen_ball, ?_, ?_⟩
  · refine ⟨u, ?_, huw⟩
    simp only [Metric.mem_ball, dist_self]
    linarith
  · have hloc := differentiableOn_comp_principal_symm_local hμ d hU hg hrel
      (by linarith : (0:ℝ) < δ/2)
      ((Metric.closedBall_subset_ball (by linarith : δ/2 < δ)).trans hδ)
    exact hloc.mono Set.inter_subset_right

end Work.MRMT.Found
