import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.lintegralAbsDbar_comp_eq
import Submission.Work.MRMT.Found.differentiableOn_of_tendstoLocallyUniformly_of_lintegral_tendsto
import Submission.Work.MRMT.Found.tendsto_lintegral_ofReal_mul_of_ae_tendsto_zero
import Submission.Work.MRMT.Found.differentiableOn_comp_principal_symm
import Submission.Work.MRMT.Found.exists_bound_volume_image_Fn
import Submission.Work.MRMT.Found.comp_l2_bound
import Submission.Work.MRMT.Found.tendstoLocallyUniformly_conj
import Submission.Work.MRMT.Found.tendsto_lintegralAbsDbar_conj
import Submission.Work.MRMT.Found.coeff_conj_comp_le
import Submission.Work.MRMT.Found.lintegral_normSq_dz_conj_comp_le
import Submission.Work.MRMT.Wirtinger.beltramiOf_comp_antiholo
import Submission.Work.MRMT.AhlforsBers.null_preimage_entire

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

/-! ## The Wirtinger derivatives of a function composed with `star` -/

lemma dz_star_comp' {G : ℂ → ℂ} {w : ℂ} (hG : DifferentiableAt ℝ G w) :
    dz (star ∘ G) w = star (dzbar G w) := by
  rw [Work.MRMT.Wirtinger.dz_comp (g := (star : ℂ → ℂ)) (f := G)
      (Work.MRMT.Wirtinger.differentiableAt_star (G w)) hG,
    Work.MRMT.Wirtinger.dz_star, Work.MRMT.Wirtinger.dzbar_star]
  simp

lemma dzbar_star_comp' {G : ℂ → ℂ} {w : ℂ} (hG : DifferentiableAt ℝ G w) :
    dzbar (star ∘ G) w = star (dz G w) := by
  rw [Work.MRMT.Wirtinger.dzbar_comp (g := (star : ℂ → ℂ)) (f := G)
      (Work.MRMT.Wirtinger.differentiableAt_star (G w)) hG,
    Work.MRMT.Wirtinger.dz_star, Work.MRMT.Wirtinger.dzbar_star]
  simp

/-- For a holomorphic `g`, the Wirtinger derivative `dz` is the complex derivative. -/
lemma dz_eq_deriv {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ g z) : dz g z = deriv g z := by
  rw [dz, Work.MRMT.QC.fderiv_real_eq_smul_one hg]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul, mul_one]
  rw [← mul_assoc, mul_comm Complex.I (deriv g z), mul_assoc, Complex.I_mul_I]
  ring

/-- `dzbar f = star ∘ deriv (star ∘ f)` for an anti-holomorphic `f`. -/
lemma dzbar_antiholo {f : ℂ → ℂ} (hf : Differentiable ℂ (star ∘ f)) (z : ℂ) :
    dzbar f z = star (deriv (star ∘ f) z) := by
  have h1 : f = star ∘ (star ∘ f) := by funext w; simp
  have h2 : DifferentiableAt ℝ (star ∘ f) z := (hf z).restrictScalars ℝ
  conv_lhs => rw [h1]
  rw [dzbar_star_comp' h2, dz_eq_deriv (hf z)]

/-- `dzbar f` is continuous for an anti-holomorphic `f`. -/
lemma continuous_dzbar_antiholo {f : ℂ → ℂ} (hf : Differentiable ℂ (star ∘ f)) :
    Continuous (dzbar f) := by
  have hcont : Continuous (deriv (star ∘ f)) := (hf.contDiff.continuous_deriv le_rfl)
  have h1 : dzbar f = fun z => star (deriv (star ∘ f) z) := funext fun z => dzbar_antiholo hf z
  rw [h1]
  exact continuous_star.comp hcont

/-! ## The main theorem -/


theorem antiholo_conj {μ : ℂ → ℂ} (hμ : Admissible μ) (d : PrincipalData μ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ (star ∘ f))
    (hinv : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      μ z = star (μ (f z)) * dzbar f z / star (dzbar f z)) :
    Differentiable ℂ (star ∘ (d.φ : ℂ → ℂ) ∘ f ∘ ((d.φ).symm : ℂ → ℂ)) := by
  classical
  have hfcont : Continuous f := by
    have h1 : f = star ∘ (star ∘ f) := by funext w; simp
    rw [h1]; exact continuous_star.comp hf.continuous
  have hstar_contDiff : ContDiff ℝ 1 (star : ℂ → ℂ) := by
    have h1 : (star : ℂ → ℂ) = ⇑Complex.conjCLE := by funext w; simp
    rw [h1]; exact Complex.conjCLE.contDiff
  have hfcd : ContDiff ℝ 1 f := by
    have h1 : f = star ∘ (star ∘ f) := by funext w; simp
    rw [h1]
    exact hstar_contDiff.comp ((hf.contDiff (n := 1)).restrict_scalars ℝ)
  have hdzbarcont : Continuous (dzbar f) := continuous_dzbar_antiholo hf
  by_cases hconst : ∃ c : ℂ, ∀ z, f z = c
  · obtain ⟨c, hc⟩ := hconst
    have hGeq : (star ∘ (d.φ : ℂ → ℂ) ∘ f ∘ ((d.φ).symm : ℂ → ℂ))
        = fun _ => star ((d.φ : ℂ → ℂ) c) := by
      funext w; simp only [Function.comp_apply, hc]
    rw [hGeq]; exact differentiable_const _
  · set F : ℂ → ℂ := star ∘ f with hFdef
    have hF : Differentiable ℂ F := hf
    have hFnc : ¬ ∃ c : ℂ, ∀ z, F z = c := by
      rintro ⟨c, hc⟩
      refine hconst ⟨star c, fun z => ?_⟩
      have h := congrArg star (hc z)
      simpa [hFdef, Function.comp_apply] using h
    set Z : Set ℂ := {z | deriv F z = 0} with hZdef
    have hZclosed : IsClosed Z := by
      rw [hZdef]
      exact isClosed_eq (hF.contDiff.continuous_deriv le_rfl) continuous_const
    have hZdis : IsDiscrete Z := by
      have hderivne : ∃ z, deriv F z ≠ 0 := by
        by_contra h
        push Not at h
        exact hFnc ⟨F 0, fun z => is_const_of_deriv_eq_zero hF h z 0⟩
      obtain ⟨x, hx⟩ := hderivne
      have han : AnalyticOnNhd ℂ (deriv F) Set.univ :=
        hF.deriv.differentiableOn.analyticOnNhd isOpen_univ
      have hcod : Zᶜ ∈ Filter.codiscrete ℂ := by
        have h := han.preimage_zero_mem_codiscrete (x := x) hx
        simpa [hZdef, Set.preimage, Set.compl_ofPred] using h
      exact (compl_mem_codiscrete_iff.mp hcod).2
    set V : Set ℂ := ((d.φ : ℂ → ℂ) '' Z)ᶜ with hVdef
    have hVopen : IsOpen V := by
      rw [hVdef]
      refine isOpen_compl_iff.mpr ?_
      have himg : (d.φ : ℂ → ℂ) '' Z = ((d.φ).symm : ℂ → ℂ) ⁻¹' Z := by
        ext w
        simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨z, hz, rfl⟩; rwa [Homeomorph.symm_apply_apply]
        · intro h; exact ⟨((d.φ).symm : ℂ → ℂ) w, h, Homeomorph.apply_symm_apply _ w⟩
      rw [himg]
      exact hZclosed.preimage (d.φ.symm.continuous)
    set G : ℂ → ℂ := star ∘ (d.φ : ℂ → ℂ) ∘ f ∘ ((d.φ).symm : ℂ → ℂ) with hGdef
    set Gn : ℕ → ℂ → ℂ :=
      fun n => star ∘ ((d.Fn n : ℂ → ℂ)) ∘ f ∘ ((d.Fn n).symm : ℂ → ℂ) with hGndef
    have hGnlip : ∀ n, LocallyLipschitzOn V (Gn n) := by
      intro n
      have h1 : ContDiff ℝ 1 (star ∘ ((d.Fn n : ℂ → ℂ))) :=
        hstar_contDiff.comp (d.contDiff_Fn n)
      have h2 : ContDiff ℝ 1 ((d.Fn n).symm : ℂ → ℂ) := d.contDiff_symm_Fn n
      have h3 : ContDiff ℝ 1 (star ∘ ((d.Fn n : ℂ → ℂ)) ∘ f ∘ ((d.Fn n).symm : ℂ → ℂ)) :=
        (h1.comp hfcd).comp h2
      have h4 : ContDiff ℝ 1 (Gn n) := h3
      exact h4.locallyLipschitz.locallyLipschitzOn
    have hconv : TendstoLocallyUniformly Gn G Filter.atTop :=
      tendstoLocallyUniformly_conj d hfcont
    have hGncont : ∀ n, Continuous (Gn n) := by
      intro n
      have h1 : ContDiff ℝ 1 (star ∘ ((d.Fn n : ℂ → ℂ))) :=
        hstar_contDiff.comp (d.contDiff_Fn n)
      have h2 : ContDiff ℝ 1 ((d.Fn n).symm : ℂ → ℂ) := d.contDiff_symm_Fn n
      exact ((h1.comp hfcd).comp h2).continuous
    -- the key integral estimate, delegated to `tendsto_lintegralAbsDbar_conj`
    have hkey : ∀ L : Set ℂ, IsCompact L → L ⊆ V →
        Tendsto (fun n => lintegralAbsDbar (Gn n) L) Filter.atTop (nhds 0) := by
      intro L hL hLV
      have hLZ : L ⊆ ((d.φ : ℂ → ℂ) '' {z : ℂ | deriv (star ∘ f) z = 0})ᶜ := by
        intro z hz
        have h1 : z ∈ V := hLV hz
        rw [hVdef] at h1
        intro hcon
        refine h1 ?_
        rwa [hZdef, hFdef]
      simpa only [hGndef] using
        tendsto_lintegralAbsDbar_conj hμ d hf hinv hL hLZ
    have hGdiffV : DifferentiableOn ℂ G V :=
      differentiableOn_of_tendstoLocallyUniformly_of_lintegral_tendsto hVopen hGnlip hconv hkey
    have hGcont : Continuous G := by
      rw [hGdef]
      exact continuous_star.comp (d.φ.continuous.comp (hfcont.comp d.φ.symm.continuous))
    -- differentiable everywhere, including on the countable exceptional set
    have hext : ∀ x : ℂ, DifferentiableAt ℂ G x := by
      intro x
      by_cases hx : x ∈ V
      · exact hGdiffV.differentiableAt (hVopen.mem_nhds hx)
      · have hxZ : x ∈ (d.φ : ℂ → ℂ) '' Z := by
          by_contra h
          exact hx (by rw [hVdef]; exact h)
        have hdisφ : IsDiscrete ((d.φ : ℂ → ℂ) '' Z) :=
          hZdis.image_of_isOpenMap d.φ.isOpenMap d.φ.injective
        obtain ⟨u, huopen, hu⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hdisφ x hxZ
        have hxu : x ∈ u :=
          (show x ∈ u ∩ ((d.φ : ℂ → ℂ) '' Z) by rw [hu]; exact Set.mem_singleton x).1
        obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp (huopen.mem_nhds hxu)
        have hsub : DifferentiableOn ℂ G (Metric.ball x r \ {x}) := by
          refine hGdiffV.mono ?_
          intro y hy
          rw [hVdef]
          rw [Set.mem_compl_iff]
          rintro hyZ
          have hyu : y ∈ u := hrsub hy.1
          have : y ∈ u ∩ ((d.φ : ℂ → ℂ) '' Z) := ⟨hyu, hyZ⟩
          rw [hu] at this
          exact hy.2 (Set.mem_singleton_iff.mp this)
        have hcl : ContinuousAt G x := hGcont.continuousAt
        have hball : DifferentiableOn ℂ G (Metric.ball x r) :=
          (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
            (f := G) (s := Metric.ball x r) (c := x)
            (Metric.ball_mem_nhds x hrpos)).mp ⟨hsub, hcl⟩
        exact hball.differentiableAt (Metric.ball_mem_nhds x hrpos)
    exact hext

end Work.MRMT.Found
