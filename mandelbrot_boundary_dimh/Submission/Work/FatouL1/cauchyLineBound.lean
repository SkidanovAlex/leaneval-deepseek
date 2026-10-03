import Mathlib
import Submission.Work.FatouL1.DefsLower
import Submission.Work.FatouL1.rectWinding
import Submission.Work.FatouL1.lineLintegral

namespace Work.FatouL1
open Set MeasureTheory Filter intervalIntegral
open scoped Topology

noncomputable section

lemma rectB_eq_rect (a b Y : ℝ) (f : ℂ → ℂ) :
    rectB a b Y f =
      (∫ x : ℝ in (⟨a,-Y⟩ : ℂ).re..(⟨b,Y⟩ : ℂ).re, f ((x : ℂ) + (⟨a,-Y⟩ : ℂ).im * Complex.I)) -
      (∫ x : ℝ in (⟨a,-Y⟩ : ℂ).re..(⟨b,Y⟩ : ℂ).re, f ((x : ℂ) + (⟨b,Y⟩ : ℂ).im * Complex.I)) +
      Complex.I • (∫ y : ℝ in (⟨a,-Y⟩ : ℂ).im..(⟨b,Y⟩ : ℂ).im, f ((⟨b,Y⟩ : ℂ).re + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in (⟨a,-Y⟩ : ℂ).im..(⟨b,Y⟩ : ℂ).im, f ((⟨a,-Y⟩ : ℂ).re + y * Complex.I)) := by
  simp only [rectB, ← Complex.ofReal_neg, smul_eq_mul]

lemma norm_rectB_le (a b Y : ℝ) (f : ℂ → ℂ) :
    ‖rectB a b Y f‖ ≤ ‖∫ x : ℝ in a..b, f ((x : ℂ) + (-Y) * Complex.I)‖
      + ‖∫ x : ℝ in a..b, f ((x : ℂ) + Y * Complex.I)‖
      + ‖∫ y : ℝ in (-Y)..Y, f ((b : ℂ) + y * Complex.I)‖
      + ‖∫ y : ℝ in (-Y)..Y, f ((a : ℂ) + y * Complex.I)‖ := by
  simp only [rectB]
  set A := ∫ x : ℝ in a..b, f ((x : ℂ) + (-Y) * Complex.I) with hA
  set B := ∫ x : ℝ in a..b, f ((x : ℂ) + Y * Complex.I) with hB
  set C := ∫ y : ℝ in (-Y)..Y, f ((b : ℂ) + y * Complex.I) with hC
  set D := ∫ y : ℝ in (-Y)..Y, f ((a : ℂ) + y * Complex.I) with hD
  have e1 := norm_sub_le (A - B + Complex.I * C) (Complex.I * D)
  have e2 := norm_add_le (A - B) (Complex.I * C)
  have e3 := norm_sub_le A B
  have e4 : ‖Complex.I * C‖ = ‖C‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have e5 : ‖Complex.I * D‖ = ‖D‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  linarith

theorem rectCauchy {h : ℂ → ℂ} {a b Y : ℝ} {z : ℂ}
    (haz : a < z.re) (hzb : z.re < b) (hYl : -Y < z.im) (hYr : z.im < Y)
    (hhol : DifferentiableOn ℂ h (Set.uIcc a b ×ℂ Set.uIcc (-Y) Y)) :
    rectB a b Y (fun ζ => h ζ / (ζ - z)) = 2 * Real.pi * Complex.I * h z := by
  have hab : a < b := lt_trans haz hzb
  have hYpos : -Y < Y := lt_trans hYl hYr
  have hsub : Set.Ioo a b ×ℂ Set.Ioo (-Y) Y ⊆ Set.uIcc a b ×ℂ Set.uIcc (-Y) Y := by
    rw [Complex.reProdIm_subset_iff]
    exact Set.prod_mono (Ioo_subset_Icc_self.trans Icc_subset_uIcc)
      (Ioo_subset_Icc_self.trans Icc_subset_uIcc)
  have hmem : Set.uIcc a b ×ℂ Set.uIcc (-Y) Y ∈ 𝓝 z :=
    mem_of_superset ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds ⟨⟨haz,hzb⟩,⟨hYl,hYr⟩⟩) hsub
  have hcont : ContinuousOn (dslope h z) (Set.uIcc a b ×ℂ Set.uIcc (-Y) Y) :=
    (continuousOn_dslope hmem).2 ⟨hhol.continuousOn, hhol.differentiableAt hmem⟩
  have hdiff : ∀ x ∈ Set.Ioo (min a b) (max a b) ×ℂ Set.Ioo (min (-Y) Y) (max (-Y) Y) \ {z},
      DifferentiableAt ℂ (dslope h z) x := by
    intro x hx
    rw [Set.mem_sdiff] at hx
    have hxz : x ≠ z := by simpa using hx.2
    simp only [min_eq_left hab.le, max_eq_right hab.le, min_eq_left hYpos.le,
      max_eq_right hYpos.le] at hx
    have hxmem : Set.uIcc a b ×ℂ Set.uIcc (-Y) Y ∈ 𝓝 x :=
      mem_of_superset ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hx.1) hsub
    exact (differentiableAt_dslope_of_ne hxz).2 (hhol.differentiableAt hxmem)
  have key := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    (dslope h z) (⟨a,-Y⟩ : ℂ) (⟨b,Y⟩ : ℂ) {z} (Set.countable_singleton z) hcont hdiff
  have hu : rectB a b Y (dslope h z) = 0 := by
    rw [rectB_eq_rect]; exact key
  have hne_bot : ∀ x : ℝ, ((x : ℂ) + (-Y) * Complex.I) ≠ z := by
    intro x hcon
    have h := congrArg Complex.im hcon
    simp at h
    linarith
  have hne_top : ∀ x : ℝ, ((x : ℂ) + Y * Complex.I) ≠ z := by
    intro x hcon
    have h := congrArg Complex.im hcon
    simp at h
    linarith
  have hne_right : ∀ y : ℝ, ((b : ℂ) + y * Complex.I) ≠ z := by
    intro y hcon
    have h := congrArg Complex.re hcon
    simp at h
    linarith
  have hne_left : ∀ y : ℝ, ((a : ℂ) + y * Complex.I) ≠ z := by
    intro y hcon
    have h := congrArg Complex.re hcon
    simp at h
    linarith
  have hsplit : ∀ ζ : ℂ, ζ ≠ z → h ζ / (ζ - z) = dslope h z ζ + h z * (ζ - z)⁻¹ := by
    intro ζ hζ
    have hz' : ζ - z ≠ 0 := sub_ne_zero.mpr hζ
    rw [dslope_of_ne h hζ, slope_fun_def_field h z]
    field_simp
    ring
  have hpiece : ∀ (p q : ℝ) (φ : ℝ → ℂ)
      (hmap : MapsTo φ (Set.uIcc p q) (Set.uIcc a b ×ℂ Set.uIcc (-Y) Y)),
      ContinuousOn φ (Set.uIcc p q) → (∀ t ∈ Set.uIcc p q, φ t ≠ z) →
      (∫ t : ℝ in p..q, (fun ζ => h ζ / (ζ - z)) (φ t)) =
      (∫ t : ℝ in p..q, dslope h z (φ t)) + h z * (∫ t : ℝ in p..q, (φ t - z)⁻¹) := by
    intro p q φ hmap hφc hφne
    have hI1 : IntervalIntegrable (fun t : ℝ => dslope h z (φ t)) volume p q :=
      (hcont.comp hφc hmap).intervalIntegrable
    have hI2' : IntervalIntegrable (fun t : ℝ => h z * (φ t - z)⁻¹) volume p q :=
      (continuousOn_const.mul ((hφc.sub continuousOn_const).inv₀
        (fun t ht => sub_ne_zero.mpr (hφne t ht)))).intervalIntegrable
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hI1 hI2']
    exact intervalIntegral.integral_congr (fun t ht => hsplit (φ t) (hφne t ht))
  have hmap_bot : MapsTo (fun t : ℝ => (t : ℂ) + (-Y) * Complex.I) (Set.uIcc a b)
      (Set.uIcc a b ×ℂ Set.uIcc (-Y) Y) := by
    intro t ht
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using ht, by simpa using Set.left_mem_uIcc (a := -Y) (b := Y)⟩
  have hmap_top : MapsTo (fun t : ℝ => (t : ℂ) + Y * Complex.I) (Set.uIcc a b)
      (Set.uIcc a b ×ℂ Set.uIcc (-Y) Y) := by
    intro t ht
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using ht, by simpa using Set.right_mem_uIcc (a := -Y) (b := Y)⟩
  have hmap_right : MapsTo (fun t : ℝ => (b : ℂ) + t * Complex.I) (Set.uIcc (-Y) Y)
      (Set.uIcc a b ×ℂ Set.uIcc (-Y) Y) := by
    intro t ht
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using Set.right_mem_uIcc (a := a) (b := b), by simpa using ht⟩
  have hmap_left : MapsTo (fun t : ℝ => (a : ℂ) + t * Complex.I) (Set.uIcc (-Y) Y)
      (Set.uIcc a b ×ℂ Set.uIcc (-Y) Y) := by
    intro t ht
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using Set.left_mem_uIcc (a := a) (b := b), by simpa using ht⟩
  have hbot := hpiece a b (fun t : ℝ => (t : ℂ) + (-Y) * Complex.I) hmap_bot
    ((Complex.continuous_ofReal.add continuous_const).continuousOn)
    (fun t _ => hne_bot t)
  have htop := hpiece a b (fun t : ℝ => (t : ℂ) + Y * Complex.I) hmap_top
    ((Complex.continuous_ofReal.add continuous_const).continuousOn)
    (fun t _ => hne_top t)
  have hright := hpiece (-Y) Y (fun t : ℝ => (b : ℂ) + t * Complex.I) hmap_right
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn)
    (fun t _ => hne_right t)
  have hleft := hpiece (-Y) Y (fun t : ℝ => (a : ℂ) + t * Complex.I) hmap_left
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn)
    (fun t _ => hne_left t)
  have hmain : rectB a b Y (fun ζ => h ζ / (ζ - z))
      = rectB a b Y (dslope h z) + h z * rectB a b Y (fun ζ => (ζ - z)⁻¹) := by
    simp only [rectB]
    rw [hbot, htop, hright, hleft]
    ring
  rw [hmain, hu, rectWinding haz hzb hYl hYr]
  ring

theorem cauchyLineBound {a b : ℝ} (hab : a < b) {h : ℂ → ℂ} {M ε : ℝ} (hε : 0 ≤ ε)
    (hhol : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b})
    (hbdd : ∀ z : ℂ, a < z.re → z.re < b → ‖h z‖ ≤ M)
    (hline : ∀ x ∈ Set.Ioo a b,
      ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal ε)
    {z : ℂ} (hz : a < z.re) (hz' : z.re < b) :
    ‖h z‖ ≤ ε / (2 * Real.pi) * (1 / (z.re - a) + 1 / (b - z.re)) := by
  have step1 : ∀ a' ∈ Set.Ioo a z.re, ∀ b' ∈ Set.Ioo z.re b,
      ‖h z‖ ≤ ε / (2 * Real.pi) * (1 / (z.re - a') + 1 / (b' - z.re)) := by
    intro a' ha' b' hb'
    obtain ⟨haa', ha'z⟩ := ha'
    obtain ⟨hzb', hb'b⟩ := hb'
    have hpa : 0 < z.re - a' := by linarith
    have hpb : 0 < b' - z.re := by linarith
    have hab' : a' < b' := lt_trans ha'z hzb'
    have key : 2 * Real.pi * ‖h z‖ ≤ ε / (z.re - a') + ε / (b' - z.re) := by
      have htend : Tendsto (fun Y : ℝ => 2 * (b' - a') * M / (Y - |z.im|)
            + (ε / (z.re - a') + ε / (b' - z.re))) atTop
          (𝓝 (ε / (z.re - a') + ε / (b' - z.re))) := by
        have hg : Tendsto (fun Y : ℝ => Y - |z.im|) atTop atTop := by
          rw [tendsto_atTop]
          intro c
          filter_upwards [eventually_ge_atTop (c + |z.im|)] with Y hY
          linarith
        have hlim := (tendsto_const_nhds (x := 2 * (b' - a') * M)).div_atTop hg
        simpa using hlim.add_const (ε / (z.re - a') + ε / (b' - z.re))
      refine ge_of_tendsto htend ?_
      filter_upwards [eventually_gt_atTop (|z.im|)] with Y hY
      have hYl : -Y < z.im := by have := neg_abs_le z.im; linarith
      have hYr : z.im < Y := by have := le_abs_self z.im; linarith
      have hY0 : 0 ≤ Y := by have := abs_nonneg z.im; linarith
      have hYm : 0 < Y - |z.im| := by linarith
      have hhol' : DifferentiableOn ℂ h (Set.uIcc a' b' ×ℂ Set.uIcc (-Y) Y) := by
        refine hhol.mono ?_
        intro ζ hζ
        rw [Complex.mem_reProdIm] at hζ
        have h1 : a' ≤ ζ.re := by
          have hh := hζ.1; rw [Set.uIcc_of_le hab'.le, Set.mem_Icc] at hh; exact hh.1
        have h2 : ζ.re ≤ b' := by
          have hh := hζ.1; rw [Set.uIcc_of_le hab'.le, Set.mem_Icc] at hh; exact hh.2
        exact ⟨lt_of_lt_of_le haa' h1, lt_of_le_of_lt h2 hb'b⟩
      have hrect := rectCauchy ha'z hzb' hYl hYr hhol'
      have hpt1 : ∀ x ∈ Set.uIoc a' b',
          ‖(fun ζ => h ζ / (ζ - z)) ((x : ℂ) + (-Y) * Complex.I)‖ ≤ M / (Y - |z.im|) := by
        intro x hx
        have hxI : x ∈ Set.Icc a' b' := by
          have h := Set.uIoc_subset_uIcc hx
          rwa [Set.uIcc_of_le hab'.le] at h
        have hre : ((x : ℂ) + (-Y) * Complex.I).re = x := by simp
        have him : ((x : ℂ) + (-Y) * Complex.I).im = -Y := by simp
        have hh : ‖h ((x : ℂ) + (-Y) * Complex.I)‖ ≤ M :=
          hbdd _ (by rw [hre]; linarith [hxI.1]) (by rw [hre]; linarith [hxI.2])
        have hden : Y - |z.im| ≤ ‖((x : ℂ) + (-Y) * Complex.I) - z‖ := by
          have h := Complex.abs_im_le_norm (((x : ℂ) + (-Y) * Complex.I) - z)
          have him2 : (((x : ℂ) + (-Y) * Complex.I) - z).im = -Y - z.im := by
            rw [Complex.sub_im, him]
          rw [him2, abs_of_nonpos (by linarith : -Y - z.im ≤ 0)] at h
          linarith [neg_abs_le z.im]
        calc ‖(fun ζ => h ζ / (ζ - z)) ((x : ℂ) + (-Y) * Complex.I)‖
            = ‖h ((x : ℂ) + (-Y) * Complex.I)‖ / ‖((x : ℂ) + (-Y) * Complex.I) - z‖ := norm_div _ _
          _ ≤ M / (Y - |z.im|) :=
              le_trans (div_le_div_of_nonneg_left (norm_nonneg _) hYm hden)
                (div_le_div_of_nonneg_right hh hYm.le)
      have h1 : ‖∫ x : ℝ in a'..b', (fun ζ => h ζ / (ζ - z)) ((x : ℂ) + (-Y) * Complex.I)‖
          ≤ M / (Y - |z.im|) * (b' - a') := by
        have hc := intervalIntegral.norm_integral_le_of_norm_le_const hpt1
        simpa [abs_of_pos (by linarith : (0 : ℝ) < b' - a')] using hc
      have hpt2 : ∀ x ∈ Set.uIoc a' b',
          ‖(fun ζ => h ζ / (ζ - z)) ((x : ℂ) + Y * Complex.I)‖ ≤ M / (Y - |z.im|) := by
        intro x hx
        have hxI : x ∈ Set.Icc a' b' := by
          have h := Set.uIoc_subset_uIcc hx
          rwa [Set.uIcc_of_le hab'.le] at h
        have hre : ((x : ℂ) + Y * Complex.I).re = x := by simp
        have him : ((x : ℂ) + Y * Complex.I).im = Y := by simp
        have hh : ‖h ((x : ℂ) + Y * Complex.I)‖ ≤ M :=
          hbdd _ (by rw [hre]; linarith [hxI.1]) (by rw [hre]; linarith [hxI.2])
        have hden : Y - |z.im| ≤ ‖((x : ℂ) + Y * Complex.I) - z‖ := by
          have h := Complex.abs_im_le_norm (((x : ℂ) + Y * Complex.I) - z)
          have him2 : (((x : ℂ) + Y * Complex.I) - z).im = Y - z.im := by
            rw [Complex.sub_im, him]
          rw [him2, abs_of_pos (by linarith [le_abs_self z.im] : (0 : ℝ) < Y - z.im)] at h
          linarith [le_abs_self z.im]
        calc ‖(fun ζ => h ζ / (ζ - z)) ((x : ℂ) + Y * Complex.I)‖
            = ‖h ((x : ℂ) + Y * Complex.I)‖ / ‖((x : ℂ) + Y * Complex.I) - z‖ := norm_div _ _
          _ ≤ M / (Y - |z.im|) :=
              le_trans (div_le_div_of_nonneg_left (norm_nonneg _) hYm hden)
                (div_le_div_of_nonneg_right hh hYm.le)
      have h2 : ‖∫ x : ℝ in a'..b', (fun ζ => h ζ / (ζ - z)) ((x : ℂ) + Y * Complex.I)‖
          ≤ M / (Y - |z.im|) * (b' - a') := by
        have hc := intervalIntegral.norm_integral_le_of_norm_le_const hpt2
        simpa [abs_of_pos (by linarith : (0 : ℝ) < b' - a')] using hc
      have hcontb : Continuous (fun y : ℝ => h ((b' : ℂ) + y * Complex.I)) :=
        hhol.continuousOn.comp_continuous
          (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
          (fun y => by constructor <;> simp <;> linarith)
      have hdenc : Continuous (fun y : ℝ => ((b' : ℂ) + y * Complex.I) - z) :=
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const
      have hne : ∀ y : ℝ, ‖((b' : ℂ) + y * Complex.I) - z‖ ≠ 0 := by
        intro y hh
        have h := congrArg Complex.re (norm_eq_zero.mp hh)
        simp at h
        linarith
      have hI1 : IntervalIntegrable
          (fun y : ℝ => ‖h ((b' : ℂ) + y * Complex.I)‖ / ‖((b' : ℂ) + y * Complex.I) - z‖) volume (-Y) Y :=
        (hcontb.norm.div hdenc.norm hne).intervalIntegrable (-Y) Y
      have hI2 : IntervalIntegrable
          (fun y : ℝ => ‖h ((b' : ℂ) + y * Complex.I)‖ * (b' - z.re)⁻¹) volume (-Y) Y :=
        (hcontb.norm.mul continuous_const).intervalIntegrable (-Y) Y
      have h3 : ‖∫ y : ℝ in (-Y)..Y, (fun ζ => h ζ / (ζ - z)) ((b' : ℂ) + y * Complex.I)‖
          ≤ ε / (b' - z.re) := by
        have hs1 : ‖∫ y : ℝ in (-Y)..Y, (fun ζ => h ζ / (ζ - z)) ((b' : ℂ) + y * Complex.I)‖
            ≤ ∫ y : ℝ in (-Y)..Y, ‖h ((b' : ℂ) + y * Complex.I)‖ / ‖((b' : ℂ) + y * Complex.I) - z‖ := by
          have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (by linarith : -Y ≤ Y)
            (f := fun y : ℝ => (fun ζ => h ζ / (ζ - z)) ((b' : ℂ) + y * Complex.I))
          simpa only [norm_div] using h
        have hs2 : (∫ y : ℝ in (-Y)..Y, ‖h ((b' : ℂ) + y * Complex.I)‖ / ‖((b' : ℂ) + y * Complex.I) - z‖)
            ≤ ∫ y : ℝ in (-Y)..Y, ‖h ((b' : ℂ) + y * Complex.I)‖ * (b' - z.re)⁻¹ := by
          refine intervalIntegral.integral_mono_on (by linarith : -Y ≤ Y) hI1 hI2 ?_
          intro y _
          have hden : b' - z.re ≤ ‖((b' : ℂ) + y * Complex.I) - z‖ := by
            have h := Complex.abs_re_le_norm (((b' : ℂ) + y * Complex.I) - z)
            have hre2 : (((b' : ℂ) + y * Complex.I) - z).re = b' - z.re := by simp [Complex.mul_re]
            rw [hre2, abs_of_pos hpb] at h
            exact h
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ hpb hden) (norm_nonneg _)
        have hs4 : ∫ y : ℝ in (-Y)..Y, ‖h ((b' : ℂ) + y * Complex.I)‖ ≤ ε :=
          lineLintegral hcontb hε (hline b' ⟨lt_trans haa' hab', hb'b⟩) hY0
        calc ‖∫ y : ℝ in (-Y)..Y, (fun ζ => h ζ / (ζ - z)) ((b' : ℂ) + y * Complex.I)‖
            ≤ ∫ y : ℝ in (-Y)..Y, ‖h ((b' : ℂ) + y * Complex.I)‖ / ‖((b' : ℂ) + y * Complex.I) - z‖ := hs1
          _ ≤ ∫ y : ℝ in (-Y)..Y, ‖h ((b' : ℂ) + y * Complex.I)‖ * (b' - z.re)⁻¹ := hs2
          _ = (b' - z.re)⁻¹ * ∫ y : ℝ in (-Y)..Y, ‖h ((b' : ℂ) + y * Complex.I)‖ := by
                rw [intervalIntegral.integral_mul_const, mul_comm]
          _ ≤ (b' - z.re)⁻¹ * ε := mul_le_mul_of_nonneg_left hs4 (inv_nonneg.mpr hpb.le)
          _ = ε / (b' - z.re) := by rw [div_eq_mul_inv, mul_comm]
      have hconta : Continuous (fun y : ℝ => h ((a' : ℂ) + y * Complex.I)) :=
        hhol.continuousOn.comp_continuous
          (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
          (fun y => by constructor <;> simp <;> linarith)
      have hdenca : Continuous (fun y : ℝ => ((a' : ℂ) + y * Complex.I) - z) :=
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const
      have hnea : ∀ y : ℝ, ‖((a' : ℂ) + y * Complex.I) - z‖ ≠ 0 := by
        intro y hh
        have h := congrArg Complex.re (norm_eq_zero.mp hh)
        simp at h
        linarith
      have hI1a : IntervalIntegrable
          (fun y : ℝ => ‖h ((a' : ℂ) + y * Complex.I)‖ / ‖((a' : ℂ) + y * Complex.I) - z‖) volume (-Y) Y :=
        (hconta.norm.div hdenca.norm hnea).intervalIntegrable (-Y) Y
      have hI2a : IntervalIntegrable
          (fun y : ℝ => ‖h ((a' : ℂ) + y * Complex.I)‖ * (z.re - a')⁻¹) volume (-Y) Y :=
        (hconta.norm.mul continuous_const).intervalIntegrable (-Y) Y
      have h4 : ‖∫ y : ℝ in (-Y)..Y, (fun ζ => h ζ / (ζ - z)) ((a' : ℂ) + y * Complex.I)‖
          ≤ ε / (z.re - a') := by
        have hs1 : ‖∫ y : ℝ in (-Y)..Y, (fun ζ => h ζ / (ζ - z)) ((a' : ℂ) + y * Complex.I)‖
            ≤ ∫ y : ℝ in (-Y)..Y, ‖h ((a' : ℂ) + y * Complex.I)‖ / ‖((a' : ℂ) + y * Complex.I) - z‖ := by
          have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (by linarith : -Y ≤ Y)
            (f := fun y : ℝ => (fun ζ => h ζ / (ζ - z)) ((a' : ℂ) + y * Complex.I))
          simpa only [norm_div] using h
        have hs2 : (∫ y : ℝ in (-Y)..Y, ‖h ((a' : ℂ) + y * Complex.I)‖ / ‖((a' : ℂ) + y * Complex.I) - z‖)
            ≤ ∫ y : ℝ in (-Y)..Y, ‖h ((a' : ℂ) + y * Complex.I)‖ * (z.re - a')⁻¹ := by
          refine intervalIntegral.integral_mono_on (by linarith : -Y ≤ Y) hI1a hI2a ?_
          intro y _
          have hden : z.re - a' ≤ ‖((a' : ℂ) + y * Complex.I) - z‖ := by
            have h := Complex.abs_re_le_norm (((a' : ℂ) + y * Complex.I) - z)
            have hre2 : (((a' : ℂ) + y * Complex.I) - z).re = a' - z.re := by simp [Complex.mul_re]
            rw [hre2, abs_of_neg (by linarith : a' - z.re < 0)] at h
            linarith
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ hpa hden) (norm_nonneg _)
        have hs4 : ∫ y : ℝ in (-Y)..Y, ‖h ((a' : ℂ) + y * Complex.I)‖ ≤ ε :=
          lineLintegral hconta hε (hline a' ⟨haa', lt_trans hab' hb'b⟩) hY0
        calc ‖∫ y : ℝ in (-Y)..Y, (fun ζ => h ζ / (ζ - z)) ((a' : ℂ) + y * Complex.I)‖
            ≤ ∫ y : ℝ in (-Y)..Y, ‖h ((a' : ℂ) + y * Complex.I)‖ / ‖((a' : ℂ) + y * Complex.I) - z‖ := hs1
          _ ≤ ∫ y : ℝ in (-Y)..Y, ‖h ((a' : ℂ) + y * Complex.I)‖ * (z.re - a')⁻¹ := hs2
          _ = (z.re - a')⁻¹ * ∫ y : ℝ in (-Y)..Y, ‖h ((a' : ℂ) + y * Complex.I)‖ := by
                rw [intervalIntegral.integral_mul_const, mul_comm]
          _ ≤ (z.re - a')⁻¹ * ε := mul_le_mul_of_nonneg_left hs4 (inv_nonneg.mpr hpa.le)
          _ = ε / (z.re - a') := by rw [div_eq_mul_inv, mul_comm]
      have hle := norm_rectB_le a' b' Y (fun ζ => h ζ / (ζ - z))
      have hsum : 2 * Real.pi * ‖h z‖ ≤ M / (Y - |z.im|) * (b' - a') + M / (Y - |z.im|) * (b' - a')
          + ε / (b' - z.re) + ε / (z.re - a') := by
        calc 2 * Real.pi * ‖h z‖ = ‖rectB a' b' Y (fun ζ => h ζ / (ζ - z))‖ := by
              rw [hrect]; simp [Complex.norm_I]
          _ ≤ ‖∫ x : ℝ in a'..b', (fun ζ => h ζ / (ζ - z)) ((x : ℂ) + (-Y) * Complex.I)‖
              + ‖∫ x : ℝ in a'..b', (fun ζ => h ζ / (ζ - z)) ((x : ℂ) + Y * Complex.I)‖
              + ‖∫ y : ℝ in (-Y)..Y, (fun ζ => h ζ / (ζ - z)) ((b' : ℂ) + y * Complex.I)‖
              + ‖∫ y : ℝ in (-Y)..Y, (fun ζ => h ζ / (ζ - z)) ((a' : ℂ) + y * Complex.I)‖ := hle
          _ ≤ M / (Y - |z.im|) * (b' - a') + M / (Y - |z.im|) * (b' - a') + ε / (b' - z.re) + ε / (z.re - a') :=
              by linarith [h1, h2, h3, h4]
      calc 2 * Real.pi * ‖h z‖ ≤ M / (Y - |z.im|) * (b' - a') + M / (Y - |z.im|) * (b' - a')
            + ε / (b' - z.re) + ε / (z.re - a') := hsum
        _ = 2 * (b' - a') * M / (Y - |z.im|) + (ε / (z.re - a') + ε / (b' - z.re)) := by ring
    have h2pi : 0 < 2 * Real.pi := by positivity
    have hrhs : 2 * Real.pi * (ε / (2 * Real.pi) * (1 / (z.re - a') + 1 / (b' - z.re)))
        = ε / (z.re - a') + ε / (b' - z.re) := by
      have h1 : z.re - a' ≠ 0 := ne_of_gt hpa
      have h2 : b' - z.re ≠ 0 := ne_of_gt hpb
      have h3 : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt h2pi
      field_simp
    refine le_of_mul_le_mul_left ?_ h2pi
    rw [hrhs]
    exact key
  have hza : 0 < z.re - a := by linarith
  have hzb : 0 < b - z.re := by linarith
  have hdiv2 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    push_cast
    linarith
  have hA : Tendsto (fun n : ℕ => (z.re - a) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    hdiv2.const_div_atTop (z.re - a)
  have hB : Tendsto (fun n : ℕ => (b - z.re) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    hdiv2.const_div_atTop (b - z.re)
  have hAn : Tendsto (fun n : ℕ => a + (z.re - a) / ((n : ℝ) + 2)) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add hA
  have hBn : Tendsto (fun n : ℕ => b - (b - z.re) / ((n : ℝ) + 2)) atTop (𝓝 b) := by
    simpa using tendsto_const_nhds.sub hB
  have hden1 : Tendsto (fun n : ℕ => z.re - (a + (z.re - a) / ((n : ℝ) + 2))) atTop (𝓝 (z.re - a)) := by
    simpa using tendsto_const_nhds.sub hAn
  have hden2 : Tendsto (fun n : ℕ => (b - (b - z.re) / ((n : ℝ) + 2)) - z.re) atTop (𝓝 (b - z.re)) := by
    simpa using hBn.sub tendsto_const_nhds
  have hlim : Tendsto (fun n : ℕ => ε / (2 * Real.pi) *
        (1 / (z.re - (a + (z.re - a) / ((n : ℝ) + 2)))
          + 1 / ((b - (b - z.re) / ((n : ℝ) + 2)) - z.re))) atTop
      (𝓝 (ε / (2 * Real.pi) * (1 / (z.re - a) + 1 / (b - z.re)))) := by
    have h1 : Tendsto (fun n : ℕ => (z.re - (a + (z.re - a) / ((n : ℝ) + 2)))⁻¹) atTop
        (𝓝 ((z.re - a)⁻¹)) := hden1.inv₀ (by linarith)
    have h2 : Tendsto (fun n : ℕ => ((b - (b - z.re) / ((n : ℝ) + 2)) - z.re)⁻¹) atTop
        (𝓝 ((b - z.re)⁻¹)) := hden2.inv₀ (by linarith)
    have h3 := (tendsto_const_nhds (x := ε / (2 * Real.pi))).mul (h1.add h2)
    simpa only [one_div] using h3
  refine ge_of_tendsto' hlim (fun n => step1 _ ?_ _ ?_)
  · refine ⟨?_, ?_⟩
    · have : 0 < (z.re - a) / ((n : ℝ) + 2) := div_pos hza (by positivity)
      linarith
    · have hk : (1 : ℝ) < (n : ℝ) + 2 := by
        have := Nat.cast_nonneg (α := ℝ) n; linarith
      have := div_lt_self hza hk
      linarith
  · refine ⟨?_, ?_⟩
    · have hk : (1 : ℝ) < (n : ℝ) + 2 := by
        have := Nat.cast_nonneg (α := ℝ) n; linarith
      have := div_lt_self hzb hk
      linarith
    · have : 0 < (b - z.re) / ((n : ℝ) + 2) := div_pos hzb (by positivity)
      linarith

end
end Work.FatouL1