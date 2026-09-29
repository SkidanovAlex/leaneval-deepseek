import Mathlib
import Submission.Work.TMComp.Kotani.RectDefs
import Submission.Work.TMComp.Kotani.rectBdIntegral_split
import Submission.Work.TMComp.RedC8.rectBdIntegral_cauchy
import Submission.Work.TMComp.RedC8.vertical_slab_bound
import Submission.Work.TMComp.RedC8.differentiableOn_rectBdIntegral

open MeasureTheory intervalIntegral Set Filter
open scoped Interval Topology

namespace Work.TMComp.RedC8

open Work.TMComp.Kotani (rectBdIntegral)

lemma aeStronglyMeasurable_edge {a b h : ℝ} (hh : 0 < h) {g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U)
    (hUrect : ∀ z : ℂ, z.re ∈ Set.Icc a b → z.im ∈ Set.Icc (-h) h → z.im ≠ 0 → z ∈ U)
    (hhol : DifferentiableOn ℂ g U) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    AEStronglyMeasurable (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * Complex.I))
      (volume.restrict (Set.uIoc (-h) h)) := by
  have hg : ContinuousOn g U := hhol.continuousOn
  have hφ : Continuous (fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) :=
    continuous_const.add ((Complex.continuous_ofReal).mul continuous_const)
  have hmap : MapsTo (fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) (Set.uIcc (-h) h \ {0}) U := by
    intro y hy
    refine hUrect _ ?_ ?_ ?_
    · simpa using hx
    · simpa [Set.uIcc_of_le (by linarith : (-h:ℝ) ≤ h), Set.mem_Icc] using hy.1
    · simpa [Set.mem_singleton_iff] using hy.2
  have hcont : ContinuousOn (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * Complex.I))
      (Set.uIcc (-h) h \ {0}) :=
    hg.comp hφ.continuousOn hmap
  have h1 : AEStronglyMeasurable (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * Complex.I))
      (volume.restrict (Set.uIcc (-h) h \ {0})) :=
    hcont.aestronglyMeasurable (measurableSet_uIcc.diff (measurableSet_singleton 0))
  have h2 : AEStronglyMeasurable (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * Complex.I))
      (volume.restrict ({0} : Set ℝ)) := by
    rw [Measure.restrict_eq_zero.mpr Real.volume_singleton]
    exact aestronglyMeasurable_zero_measure _
  have h3 : AEStronglyMeasurable (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * Complex.I))
      (volume.restrict ((Set.uIcc (-h) h \ {0}) ∪ {0})) :=
    aestronglyMeasurable_union_iff.mpr ⟨h1, h2⟩
  rw [sdiff_union_of_subset (by
    intro y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    rw [Set.uIcc_of_le (by linarith : (-h:ℝ) ≤ h), Set.mem_Icc]; exact ⟨by linarith, le_of_lt hh⟩)] at h3
  refine h3.mono_set ?_
  intro y hy
  rw [Set.uIcc_of_le (by linarith : (-h:ℝ) ≤ h), Set.mem_Icc]
  rw [Set.uIoc_of_le (by linarith : (-h:ℝ) ≤ h), Set.mem_Ioc] at hy
  exact ⟨le_of_lt hy.1, hy.2⟩

lemma intervalIntegrable_edge {a b h M : ℝ} (hh : 0 < h) {g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U)
    (hUrect : ∀ z : ℂ, z.re ∈ Set.Icc a b → z.im ∈ Set.Icc (-h) h → z.im ≠ 0 → z ∈ U)
    (hhol : DifferentiableOn ℂ g U)
    (hbound : ∀ z : ℂ, z.re ∈ Set.Icc a b → z.im ∈ Set.Icc (-h) h → z.im ≠ 0 → ‖g z‖ ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc a b) {z : ℂ} (hz : (x : ℝ) ≠ z.re) :
    IntervalIntegrable
      (fun y : ℝ => (((x:ℂ) + (y:ℂ) * Complex.I) - z)⁻¹ * g ((x:ℂ) + (y:ℂ) * Complex.I))
      volume (-h) h := by
  have hne0 : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 0 := by
    rw [MeasureTheory.ae_iff]; simpa using Real.volume_singleton (a := (0:ℝ))
  have hgm : AEStronglyMeasurable (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * Complex.I))
      (volume.restrict (Set.uIoc (-h) h)) :=
    aeStronglyMeasurable_edge hh hU hUrect hhol hx
  have hcm : AEStronglyMeasurable (fun y : ℝ => (((x:ℂ) + (y:ℂ) * Complex.I) - z)⁻¹)
      (volume.restrict (Set.uIoc (-h) h)) := by
    have hc : Continuous (fun y : ℝ => (((x:ℂ) + (y:ℂ) * Complex.I) - z)⁻¹) := by
      refine Continuous.inv₀ ?_ ?_
      · fun_prop
      · intro y h
        have hre : (((x:ℂ) + (y:ℂ) * Complex.I) - z).re = (x:ℝ) - z.re := by simp
        have : ((x:ℝ) - z.re) = 0 := by rw [← hre, h]; simp
        exact hz (by linarith)
    exact hc.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => (((x:ℂ) + (y:ℂ) * Complex.I) - z)⁻¹ * g ((x:ℂ) + (y:ℂ) * Complex.I))
      (volume.restrict (Set.uIoc (-h) h)) := hcm.mul hgm
  have hbd : (fun y : ℝ => ‖(((x:ℂ) + (y:ℂ) * Complex.I) - z)⁻¹ * g ((x:ℂ) + (y:ℂ) * Complex.I)‖)
      ≤ᵐ[volume.restrict (Set.uIoc (-h) h)] (fun _ => |(x:ℝ) - z.re|⁻¹ * |M|) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hne0] with y hyne hymem
    have hyicc : y ∈ Set.Icc (-h) h := by
      rw [Set.uIoc_of_le (by linarith : (-h:ℝ) ≤ h), Set.mem_Ioc] at hymem
      exact ⟨le_of_lt hymem.1, hymem.2⟩
    have hgb := hbound ((x:ℂ) + (y:ℂ) * Complex.I) (by simpa using hx) (by simpa using hyicc)
      (by simpa using hyne)
    have hden : |(x:ℝ) - z.re| ≤ ‖(((x:ℂ) + (y:ℂ) * Complex.I) - z)‖ := by
      have hre : (((x:ℂ) + (y:ℂ) * Complex.I) - z).re = (x:ℝ) - z.re := by simp
      calc |(x:ℝ) - z.re| = |(((x:ℂ) + (y:ℂ) * Complex.I) - z).re| := by rw [hre]
        _ ≤ ‖(((x:ℂ) + (y:ℂ) * Complex.I) - z)‖ := Complex.abs_re_le_norm _
    have hdenpos : 0 < |(x:ℝ) - z.re| := abs_pos.mpr (sub_ne_zero.mpr hz)
    have hinv : ‖(((x:ℂ) + (y:ℂ) * Complex.I) - z)⁻¹‖ ≤ |(x:ℝ) - z.re|⁻¹ := by
      rw [norm_inv]
      exact (inv_le_inv₀ (lt_of_lt_of_le hdenpos hden) hdenpos).mpr hden
    calc ‖(((x:ℂ) + (y:ℂ) * Complex.I) - z)⁻¹ * g ((x:ℂ) + (y:ℂ) * Complex.I)‖
        ≤ ‖(((x:ℂ) + (y:ℂ) * Complex.I) - z)⁻¹‖ * ‖g ((x:ℂ) + (y:ℂ) * Complex.I)‖ := norm_mul_le _ _
      _ ≤ |(x:ℝ) - z.re|⁻¹ * M :=
          mul_le_mul hinv hgb (norm_nonneg _) (by positivity)
      _ ≤ |(x:ℝ) - z.re|⁻¹ * |M| :=
          mul_le_mul_of_nonneg_left (le_abs_self M) (by positivity)
  exact IntervalIntegrable.mono_fun' (intervalIntegrable_const (c := |(x:ℝ) - z.re|⁻¹ * |M|))
    hmeas hbd

lemma intervalIntegrable_edge_sub {a b h M c d : ℝ} (hh : 0 < h) {g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U)
    (hUrect : ∀ z : ℂ, z.re ∈ Set.Icc a b → z.im ∈ Set.Icc (-h) h → z.im ≠ 0 → z ∈ U)
    (hhol : DifferentiableOn ℂ g U)
    (hbound : ∀ z : ℂ, z.re ∈ Set.Icc a b → z.im ∈ Set.Icc (-h) h → z.im ≠ 0 → ‖g z‖ ≤ M)
    (hcd : Set.uIcc c d ⊆ Set.uIcc (-h) h)
    {x : ℝ} (hx : x ∈ Set.Icc a b) {z : ℂ} (hz : (x : ℝ) ≠ z.re) :
    IntervalIntegrable
      (fun y : ℝ => (((x:ℂ) + (y:ℂ) * Complex.I) - z)⁻¹ * g ((x:ℂ) + (y:ℂ) * Complex.I))
      volume c d :=
  (intervalIntegrable_edge hh hU hUrect hhol hbound hx hz).mono_set hcd

lemma uIcc_subset_of {h c d : ℝ} (hc : -h ≤ c) (hd : d ≤ h) (hcd : c ≤ d) :
    Set.uIcc c d ⊆ Set.uIcc (-h) h := by
  intro y hy
  rw [Set.uIcc_of_le hcd, Set.mem_Icc] at hy
  rw [Set.uIcc_of_le (by linarith : (-h:ℝ) ≤ h), Set.mem_Icc]
  exact ⟨le_trans hc hy.1, le_trans hy.2 hd⟩

lemma rectBdIntegral_eq_zero_of_differentiableOn {a b c d : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    rectBdIntegral a b c d f = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) + (c : ℂ) * Complex.I) ((b : ℂ) + (d : ℂ) * Complex.I) (by
        simpa [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] using hf)
  simpa only [rectBdIntegral, smul_eq_mul, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, sub_zero, add_zero, zero_add] using h

lemma inv_norm_le_im_self {z w : ℂ} {ε : ℝ} (hε0 : 0 < ε) (hεz : 2 * ε < |z.im|)
    (hw : |w.im| ≤ ε) : ‖(w - z)⁻¹‖ ≤ 2 / |z.im| := by
  have hzim : (0:ℝ) < |z.im| := by linarith
  have h1 : |z.im| - |w.im| ≤ |(w - z).im| := by
    have h1a : |z.im| - |w.im| ≤ |z.im - w.im| :=
      abs_sub_abs_le_abs_sub z.im w.im
    rw [Complex.sub_im, abs_sub_comm]
    exact h1a
  have h4 : |z.im| / 2 < |(w - z).im| := by linarith
  have h5 : |z.im| / 2 < ‖w - z‖ := lt_of_lt_of_le h4 (Complex.abs_im_le_norm _)
  calc ‖(w - z)⁻¹‖ = 1 / ‖w - z‖ := by rw [norm_inv, one_div]
    _ ≤ 1 / (|z.im| / 2) := one_div_le_one_div_of_le (by linarith) (le_of_lt h5)
    _ = 2 / |z.im| := by rw [one_div, inv_div]

lemma norm_inv_sub_le_self {z v w : ℂ} {ε : ℝ} (hε0 : 0 < ε) (hεz : 2 * ε < |z.im|)
    (hv : |v.im| ≤ ε) (hw : |w.im| ≤ ε) (hd : ‖v - w‖ ≤ 2 * ε) :
    ‖(v - z)⁻¹ - (w - z)⁻¹‖ ≤ 8 * ε / |z.im| ^ 2 := by
  have hzim : (0:ℝ) < |z.im| := by linarith
  have hvc : ‖(v - z)⁻¹‖ ≤ 2 / |z.im| := inv_norm_le_im_self hε0 hεz hv
  have hwc : ‖(w - z)⁻¹‖ ≤ 2 / |z.im| := inv_norm_le_im_self hε0 hεz hw
  have hvz : v - z ≠ 0 := by
    intro h
    have hveq : v = z := sub_eq_zero.mp h
    have hz : |z.im| ≤ ε := by rw [← hveq]; exact hv
    linarith
  have hwz : w - z ≠ 0 := by
    intro h
    have hweq : w = z := sub_eq_zero.mp h
    have hz : |z.im| ≤ ε := by rw [← hweq]; exact hw
    linarith
  have heq : (v - z)⁻¹ - (w - z)⁻¹ = (w - v) * ((v - z)⁻¹ * (w - z)⁻¹) := by
    field_simp
    ring
  have hdw : ‖w - v‖ ≤ 2 * ε := by rw [norm_sub_rev]; exact hd
  rw [heq]
  calc ‖(w - v) * ((v - z)⁻¹ * (w - z)⁻¹)‖
      ≤ ‖w - v‖ * ‖(v - z)⁻¹ * (w - z)⁻¹‖ := norm_mul_le _ _
    _ ≤ ‖w - v‖ * (‖(v - z)⁻¹‖ * ‖(w - z)⁻¹‖) := by
        apply mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (2 * ε) * ((2 / |z.im|) * (2 / |z.im|)) := by
        apply mul_le_mul hdw
        · exact mul_le_mul hvc hwc (norm_nonneg _) (by positivity)
        · positivity
        · positivity
    _ = 8 * ε / |z.im| ^ 2 := by field_simp; ring

lemma continuousOn_edge_self {a b h : ℝ} {g : ℂ → ℂ} {t : ℝ}
    (hgc : ContinuousOn g {w : ℂ | w.re ∈ Set.Icc a b ∧ w.im ∈ Set.Icc (-h) h ∧ w.im ≠ 0})
    (ht : t ∈ Set.Icc (-h) h) (ht0 : t ≠ 0) :
    ContinuousOn (fun x : ℝ => g ((x : ℂ) + (t : ℂ) * Complex.I)) (Set.Icc a b) := by
  have hf : ContinuousOn (fun x : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) (Set.Icc a b) := by
    fun_prop
  refine hgc.comp hf ?_
  intro x hx
  exact ⟨by simpa using hx, by simpa using ht, by simpa using ht0⟩

lemma continuousOn_inv_sub_self {a b : ℝ} {z : ℂ} {t : ℝ}
    (hden : ∀ x ∈ Set.Icc a b, (x : ℂ) + (t : ℂ) * Complex.I - z ≠ 0) :
    ContinuousOn (fun x : ℝ => ((x : ℂ) + (t : ℂ) * Complex.I - z)⁻¹) (Set.Icc a b) := by
  refine ContinuousOn.inv₀ ?_ ?_
  · fun_prop
  · intro x hx; exact hden x hx

lemma horizontal_slab_bound_self {a b h M : ℝ} (hab : a < b) {g : ℂ → ℂ} {z : ℂ}
    (hgc : ContinuousOn g {w : ℂ | w.re ∈ Set.Icc a b ∧ w.im ∈ Set.Icc (-h) h ∧ w.im ≠ 0})
    (hbound : ∀ w : ℂ, w.re ∈ Set.Icc a b → w.im ∈ Set.Icc (-h) h → w.im ≠ 0 → ‖g w‖ ≤ M)
    {ε : ℝ} (hε0 : 0 < ε) (hεh : ε < h) (hεz : 2 * ε < |z.im|) :
    ‖(∫ x in a..b, ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I - z)⁻¹ * g ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I))
      - (∫ x in a..b, ((x : ℂ) + (ε : ℂ) * Complex.I - z)⁻¹ * g ((x : ℂ) + (ε : ℂ) * Complex.I))‖
    ≤ (2 / |z.im|) * (∫ x in Set.Icc a b, ‖g ((x : ℂ) + (ε : ℂ) * Complex.I) - g ((x : ℂ) - (ε : ℂ) * Complex.I)‖)
      + (8 * M / |z.im| ^ 2 * (b - a)) * ε := by
  have hzim : (0:ℝ) < |z.im| := by linarith
  have hpos : ε ∈ Set.Icc (-h) h := ⟨by linarith, le_of_lt hεh⟩
  have hneg : (-ε) ∈ Set.Icc (-h) h := ⟨by linarith, by linarith⟩
  have hneg0 : (-ε) ≠ 0 := by linarith
  have hcont_m : ContinuousOn (fun x : ℝ => ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I - z)⁻¹
      * g ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I)) (Set.Icc a b) := by
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_inv_sub_self ?_
      intro x hx h
      have hxim : ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I - z).im = -ε - z.im := by simp
      rw [h] at hxim; simp at hxim
      have hne : z.im ≠ -ε := by
        intro hz; rw [hz, abs_neg, abs_of_pos hε0] at hεz; linarith
      exact hne (by linarith [hxim])
    · exact continuousOn_edge_self hgc hneg hneg0
  have hcont_p : ContinuousOn (fun x : ℝ => ((x : ℂ) + (ε : ℂ) * Complex.I - z)⁻¹
      * g ((x : ℂ) + (ε : ℂ) * Complex.I)) (Set.Icc a b) := by
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_inv_sub_self ?_
      intro x hx h
      have hxim : ((x : ℂ) + (ε : ℂ) * Complex.I - z).im = ε - z.im := by simp
      rw [h] at hxim; simp at hxim
      have hne : z.im ≠ ε := by
        intro hz; rw [hz, abs_of_pos hε0] at hεz; linarith
      exact hne (by linarith [hxim])
    · exact continuousOn_edge_self hgc hpos (ne_of_gt hε0)
  have hcont_j : ContinuousOn (fun x : ℝ =>
      ‖g ((x : ℂ) + (ε : ℂ) * Complex.I) - g ((x : ℂ) - (ε : ℂ) * Complex.I)‖) (Set.Icc a b) := by
    refine ContinuousOn.norm ?_
    have h1 := continuousOn_edge_self hgc hpos (ne_of_gt hε0)
    have h2 := continuousOn_edge_self hgc hneg hneg0
    have hfeq : (fun x : ℝ => g ((x : ℂ) - (ε : ℂ) * Complex.I))
        = (fun x : ℝ => g ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I)) := by
      funext x; congr 1; simp only [Complex.ofReal_neg]; ring
    have h2c : ContinuousOn (fun x : ℝ => g ((x : ℂ) - (ε : ℂ) * Complex.I)) (Set.Icc a b) := by
      rw [hfeq]; exact h2
    exact h1.sub h2c
  have toInt : ∀ {E : Type} [NormedAddCommGroup E] {u : ℝ → E},
      ContinuousOn u (Set.Icc a b) → IntervalIntegrable u (volume : Measure ℝ) a b := by
    intro E inst u hu
    have hu2 : ContinuousOn u (Set.uIcc a b) := by rw [Set.uIcc_of_le hab.le]; exact hu
    exact hu2.intervalIntegrable
  have hI_m : IntervalIntegrable (fun x : ℝ => ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I - z)⁻¹
      * g ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I)) volume a b :=
    toInt hcont_m
  have hI_p : IntervalIntegrable (fun x : ℝ => ((x : ℂ) + (ε : ℂ) * Complex.I - z)⁻¹
      * g ((x : ℂ) + (ε : ℂ) * Complex.I)) volume a b :=
    toInt hcont_p
  have hI_nm : IntervalIntegrable (fun x : ℝ => ‖((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I - z)⁻¹
      * g ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I)
      - ((x : ℂ) + (ε : ℂ) * Complex.I - z)⁻¹ * g ((x : ℂ) + (ε : ℂ) * Complex.I)‖) volume a b := by
    exact toInt (ContinuousOn.norm (hcont_m.sub hcont_p))
  have hI_j : IntervalIntegrable (fun x : ℝ =>
      ‖g ((x : ℂ) + (ε : ℂ) * Complex.I) - g ((x : ℂ) - (ε : ℂ) * Complex.I)‖) volume a b :=
    toInt hcont_j
  have hb : ∀ x ∈ Set.Icc a b, ‖((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I - z)⁻¹ * g ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I)
        - ((x : ℂ) + (ε : ℂ) * Complex.I - z)⁻¹ * g ((x : ℂ) + (ε : ℂ) * Complex.I)‖
      ≤ (2 / |z.im|) * ‖g ((x : ℂ) + (ε : ℂ) * Complex.I) - g ((x : ℂ) - (ε : ℂ) * Complex.I)‖
        + (8 * M / |z.im| ^ 2) * ε := by
    intro x hx
    set v : ℂ := (x : ℂ) + (ε : ℂ) * Complex.I with hv
    set w : ℂ := (x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I with hw
    have hvim : v.im = ε := by simp [hv]
    have hwim : w.im = -ε := by simp [hw]
    have hvmem : v.im ∈ Set.Icc (-h) h := by rw [hvim]; exact ⟨by linarith, le_of_lt hεh⟩
    have hwmem : w.im ∈ Set.Icc (-h) h := by rw [hwim]; exact ⟨by linarith, by linarith⟩
    have hvb : ‖g v‖ ≤ M := hbound v (by rw [hv]; simp; exact hx) hvmem (by rw [hvim]; exact ne_of_gt hε0)
    have h1 : ‖(w - z)⁻¹‖ ≤ 2 / |z.im| :=
      inv_norm_le_im_self hε0 hεz (by rw [hwim, abs_neg, abs_of_pos hε0])
    have hd : ‖w - v‖ ≤ 2 * ε := by
      have hmul : w - v = ((-(2 * ε) : ℝ) : ℂ) * Complex.I := by rw [hw, hv]; push_cast; ring
      have hsqrt : ‖((-(2 * ε) : ℝ) : ℂ)‖ = |-(2 * ε)| := by
        rw [Complex.norm_def, Complex.normSq_ofReal]
        simpa [sq] using Real.sqrt_sq_eq_abs (-(2 * ε))
      rw [hmul, norm_mul, Complex.norm_I, mul_one, hsqrt, abs_neg, abs_of_pos (by linarith)]
    have h2 : ‖(w - z)⁻¹ - (v - z)⁻¹‖ ≤ 8 * ε / |z.im| ^ 2 :=
      norm_inv_sub_le_self hε0 hεz (by rw [hwim, abs_neg, abs_of_pos hε0])
        (by rw [hvim, abs_of_pos hε0]) hd
    have hsplit : ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I - z)⁻¹ * g ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I)
        - ((x : ℂ) + (ε : ℂ) * Complex.I - z)⁻¹ * g ((x : ℂ) + (ε : ℂ) * Complex.I)
        = (w - z)⁻¹ * (g w - g v) + ((w - z)⁻¹ - (v - z)⁻¹) * g v := by rw [hw, hv]; ring
    have e1a : g w = g ((x : ℂ) - (ε : ℂ) * Complex.I) := by
      congr 1; rw [hw, Complex.ofReal_neg]; ring
    have e1b : g v = g ((x : ℂ) + (ε : ℂ) * Complex.I) := by rw [hv]
    have e1 : ‖g w - g v‖ = ‖g ((x : ℂ) + (ε : ℂ) * Complex.I) - g ((x : ℂ) - (ε : ℂ) * Complex.I)‖ := by
      rw [e1a, e1b, norm_sub_rev]
    have h4 : (2 / |z.im|) * ‖g w - g v‖ ≤ (2 / |z.im|) *
        ‖g ((x : ℂ) + (ε : ℂ) * Complex.I) - g ((x : ℂ) - (ε : ℂ) * Complex.I)‖ :=
      mul_le_mul_of_nonneg_left (le_of_eq e1) (div_nonneg (by norm_num) (abs_nonneg _))
    have h3 : (8 * ε / |z.im| ^ 2) * ‖g v‖ ≤ (8 * M / |z.im| ^ 2) * ε := by
      have hmul := mul_le_mul_of_nonneg_left hvb (by positivity : (0:ℝ) ≤ 8 * ε / |z.im| ^ 2)
      calc (8 * ε / |z.im| ^ 2) * ‖g v‖ ≤ (8 * ε / |z.im| ^ 2) * M := hmul
        _ = (8 * M / |z.im| ^ 2) * ε := by ring
    rw [hsplit]
    calc ‖(w - z)⁻¹ * (g w - g v) + ((w - z)⁻¹ - (v - z)⁻¹) * g v‖
        ≤ ‖(w - z)⁻¹ * (g w - g v)‖ + ‖((w - z)⁻¹ - (v - z)⁻¹) * g v‖ := norm_add_le _ _
      _ ≤ ‖(w - z)⁻¹‖ * ‖g w - g v‖ + ‖(w - z)⁻¹ - (v - z)⁻¹‖ * ‖g v‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (2 / |z.im|) * ‖g w - g v‖ + (8 * ε / |z.im| ^ 2) * ‖g v‖ :=
          add_le_add (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
      _ ≤ _ := add_le_add h4 h3
  have hintBd : IntervalIntegrable (fun x : ℝ => (2 / |z.im|)
      * ‖g ((x : ℂ) + (ε : ℂ) * Complex.I) - g ((x : ℂ) - (ε : ℂ) * Complex.I)‖
      + (8 * M / |z.im| ^ 2) * ε) volume a b :=
    toInt (ContinuousOn.add (ContinuousOn.const_mul hcont_j (2 / |z.im|))
      (continuousOn_const (c := (8 * M / |z.im| ^ 2) * ε)))
  have hle : a ≤ b := hab.le
  calc ‖(∫ x in a..b, ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I - z)⁻¹
          * g ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I))
        - (∫ x in a..b, ((x : ℂ) + (ε : ℂ) * Complex.I - z)⁻¹
          * g ((x : ℂ) + (ε : ℂ) * Complex.I))‖
      = ‖∫ x in a..b, (((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I - z)⁻¹
            * g ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I)
          - ((x : ℂ) + (ε : ℂ) * Complex.I - z)⁻¹ * g ((x : ℂ) + (ε : ℂ) * Complex.I))‖ := by
        rw [intervalIntegral.integral_sub hI_m hI_p]
    _ ≤ ∫ x in a..b, ‖((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I - z)⁻¹
            * g ((x : ℂ) + (((-ε : ℝ)) : ℂ) * Complex.I)
          - ((x : ℂ) + (ε : ℂ) * Complex.I - z)⁻¹ * g ((x : ℂ) + (ε : ℂ) * Complex.I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hle
    _ ≤ ∫ x in a..b, ((2 / |z.im|)
            * ‖g ((x : ℂ) + (ε : ℂ) * Complex.I) - g ((x : ℂ) - (ε : ℂ) * Complex.I)‖
          + (8 * M / |z.im| ^ 2) * ε) :=
        intervalIntegral.integral_mono_on hle hI_nm hintBd hb
    _ = (2 / |z.im|) * (∫ x in a..b,
            ‖g ((x : ℂ) + (ε : ℂ) * Complex.I) - g ((x : ℂ) - (ε : ℂ) * Complex.I)‖)
          + ((8 * M / |z.im| ^ 2) * ε) * (b - a) := by
        rw [intervalIntegral.integral_add (hI_j.const_mul (2 / |z.im|)) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        ring
    _ = (2 / |z.im|) * (∫ x in Set.Icc a b,
            ‖g ((x : ℂ) + (ε : ℂ) * Complex.I) - g ((x : ℂ) - (ε : ℂ) * Complex.I)‖)
          + (8 * M / |z.im| ^ 2 * (b - a)) * ε := by
        rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]
        ring

lemma norm_rectBdIntegral_le_self {a b c d : ℝ} (f : ℂ → ℂ) :
    ‖rectBdIntegral a b c d f‖ ≤
      ‖(∫ x in a..b, f ((x : ℂ) + (c : ℂ) * Complex.I))
          - (∫ x in a..b, f ((x : ℂ) + (d : ℂ) * Complex.I))‖
      + ‖∫ y in c..d, f ((b : ℂ) + (y : ℂ) * Complex.I)‖
      + ‖∫ y in c..d, f ((a : ℂ) + (y : ℂ) * Complex.I)‖ := by
  rw [rectBdIntegral]
  set X := ∫ x in a..b, f ((x : ℂ) + (c : ℂ) * Complex.I) with hX
  set Y := ∫ x in a..b, f ((x : ℂ) + (d : ℂ) * Complex.I) with hY
  set Z := ∫ y in c..d, f ((b : ℂ) + (y : ℂ) * Complex.I) with hZ
  set W := ∫ y in c..d, f ((a : ℂ) + (y : ℂ) * Complex.I) with hW
  calc ‖X - Y + Complex.I * Z - Complex.I * W‖
      = ‖((X - Y) + Complex.I * Z) + -(Complex.I * W)‖ := by
          rw [show X - Y + Complex.I * Z - Complex.I * W
                = ((X - Y) + Complex.I * Z) + -(Complex.I * W) by ring]
    _ ≤ ‖((X - Y) + Complex.I * Z)‖ + ‖-(Complex.I * W)‖ := norm_add_le _ _
    _ = ‖((X - Y) + Complex.I * Z)‖ + ‖Complex.I * W‖ := by rw [norm_neg]
    _ ≤ (‖X - Y‖ + ‖Complex.I * Z‖) + ‖Complex.I * W‖ := by
          linarith [norm_add_le (X - Y) (Complex.I * Z)]
    _ = ‖X - Y‖ + ‖Z‖ + ‖W‖ := by simp only [norm_mul, Complex.norm_I, one_mul]

lemma rectBdIntegral_bound_self {a b h M : ℝ} (hab : a < b) {g : ℂ → ℂ} {z : ℂ}
    (hzre : z.re ∈ Set.Ioo a b) (hzim : z.im ≠ 0)
    (hgc : ContinuousOn g {w : ℂ | w.re ∈ Set.Icc a b ∧ w.im ∈ Set.Icc (-h) h ∧ w.im ≠ 0})
    (hbound : ∀ w : ℂ, w.re ∈ Set.Icc a b → w.im ∈ Set.Icc (-h) h → w.im ≠ 0 → ‖g w‖ ≤ M)
    {ε : ℝ} (hε0 : 0 < ε) (hεh : ε < h) (hεz : 2 * ε < |z.im|) :
    ‖rectBdIntegral a b (-ε) ε (fun w => (w - z)⁻¹ * g w)‖
    ≤ (2 / |z.im|) * (∫ x in Set.Icc a b,
        ‖g ((x : ℂ) + (ε : ℂ) * Complex.I) - g ((x : ℂ) - (ε : ℂ) * Complex.I)‖)
      + (8 * M / |z.im| ^ 2 * (b - a)) * ε
      + (M / (b - z.re) * 2) * ε
      + (M / (z.re - a) * 2) * ε := by
  have hH := horizontal_slab_bound_self hab hgc hbound hε0 hεh hεz
  have hV := vertical_slab_bound hab hzre hzim hbound hε0 hεh
  have hmain := norm_rectBdIntegral_le_self (a := a) (b := b) (c := -ε) (d := ε)
      (f := fun w => (w - z)⁻¹ * g w)
  beta_reduce at hmain
  refine hmain.trans ?_
  linarith [hH, hV.1, hV.2]


theorem slab_rect_tendsto_self {a b h M : ℝ} (hab : a < b) {g : ℂ → ℂ} {z : ℂ}
    (hzre : z.re ∈ Set.Ioo a b) (hzim : z.im ≠ 0)
    (hgc : ContinuousOn g {w : ℂ | w.re ∈ Set.Icc a b ∧ w.im ∈ Set.Icc (-h) h ∧ w.im ≠ 0})
    (hbound : ∀ w : ℂ, w.re ∈ Set.Icc a b → w.im ∈ Set.Icc (-h) h → w.im ≠ 0 → ‖g w‖ ≤ M)
    {e : ℕ → ℝ} (he : ∀ j : ℕ, 0 < e j ∧ e j < h)
    (he0 : Filter.Tendsto e Filter.atTop (nhds 0))
    (hjump : Filter.Tendsto (fun j : ℕ => ∫ x in Set.Icc a b,
        ‖g ((x:ℂ) + (e j : ℂ) * Complex.I) - g ((x:ℂ) - (e j : ℂ) * Complex.I)‖)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun j : ℕ => rectBdIntegral a b (-(e j)) (e j)
        (fun w => (w - z)⁻¹ * g w)) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hzim_pos : (0:ℝ) < |z.im| := abs_pos.mpr hzim
  have hev : ∀ᶠ j in Filter.atTop, 2 * e j < |z.im| := by
    have h : ∀ᶠ j in Filter.atTop, e j < |z.im| / 2 :=
      (tendsto_order.1 he0).2 (|z.im| / 2) (by positivity)
    filter_upwards [h] with j hj
    linarith
  have hkey : ∀ᶠ j in Filter.atTop,
      ‖rectBdIntegral a b (-(e j)) (e j) (fun w => (w - z)⁻¹ * g w)‖
      ≤ (2 / |z.im|) * (∫ x in Set.Icc a b,
          ‖g ((x:ℂ) + (e j : ℂ) * Complex.I) - g ((x:ℂ) - (e j : ℂ) * Complex.I)‖)
        + (8 * M / |z.im| ^ 2 * (b - a)) * (e j)
        + (M / (b - z.re) * 2) * (e j)
        + (M / (z.re - a) * 2) * (e j) := by
    filter_upwards [hev] with j hj
    exact rectBdIntegral_bound_self hab hzre hzim hgc hbound (he j).1 (he j).2 hj
  have hgb : Filter.Tendsto (fun j : ℕ =>
      (2 / |z.im|) * (∫ x in Set.Icc a b,
          ‖g ((x:ℂ) + (e j : ℂ) * Complex.I) - g ((x:ℂ) - (e j : ℂ) * Complex.I)‖)
        + (8 * M / |z.im| ^ 2 * (b - a)) * (e j)
        + (M / (b - z.re) * 2) * (e j)
        + (M / (z.re - a) * 2) * (e j)) Filter.atTop (nhds 0) := by
    have h1 := hjump.const_mul (2 / |z.im|)
    have h2 := he0.const_mul (8 * M / |z.im| ^ 2 * (b - a))
    have h3 := he0.const_mul (M / (b - z.re) * 2)
    have h4 := he0.const_mul (M / (z.re - a) * 2)
    simpa using ((h1.add h2).add h3).add h4
  exact squeeze_zero' (Filter.Eventually.of_forall (fun j => norm_nonneg _)) hkey hgb

theorem rectangle_extension {a₁ b₁ h M : ℝ} (hab : a₁ < b₁) (hh : 0 < h) {g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U)
    (hUrect : ∀ z : ℂ, z.re ∈ Set.Icc a₁ b₁ → z.im ∈ Set.Icc (-h) h → z.im ≠ 0 → z ∈ U)
    (hhol : DifferentiableOn ℂ g U)
    (hbound : ∀ z : ℂ, z.re ∈ Set.Icc a₁ b₁ → z.im ∈ Set.Icc (-h) h → z.im ≠ 0 → ‖g z‖ ≤ M)
    (hjump : ∃ e : ℕ → ℝ, (∀ j : ℕ, 0 < e j ∧ e j < h) ∧ Filter.Tendsto e Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun j : ℕ => ∫ x in Set.Icc a₁ b₁,
          ‖g ((x : ℂ) + (e j : ℂ) * Complex.I) - g ((x : ℂ) - (e j : ℂ) * Complex.I)‖)
        Filter.atTop (nhds 0)) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {z : ℂ | z.re ∈ Set.Ioo a₁ b₁ ∧ z.im ∈ Set.Ioo (-h) h} ∧
      ∀ z : ℂ, z.re ∈ Set.Ioo a₁ b₁ → z.im ∈ Set.Ioo (-h) h → z.im ≠ 0 → G z = g z := by
  obtain ⟨e, he, he0, hjt⟩ := hjump
  have hgcon : ContinuousOn g {w : ℂ | w.re ∈ Set.Icc a₁ b₁ ∧ w.im ∈ Set.Icc (-h) h ∧ w.im ≠ 0} :=
    hhol.continuousOn.mono (fun w hw => hUrect w hw.1 hw.2.1 hw.2.2)
  refine ⟨fun z => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      rectBdIntegral a₁ b₁ (-h) h (fun w => (w - z)⁻¹ * g w), ?_, ?_⟩
  · exact (differentiableOn_rectBdIntegral hab hh hU hUrect hhol hbound).const_mul _
  · intro z hzre hzim hzne
    have hI : ∀ (x : ℝ) (c d : ℝ), Set.uIcc c d ⊆ Set.uIcc (-h) h → x ∈ Set.Icc a₁ b₁ → x ≠ z.re →
        IntervalIntegrable
          (fun y : ℝ => (((x:ℂ) + (y:ℂ) * Complex.I) - z)⁻¹ * g ((x:ℂ) + (y:ℂ) * Complex.I))
          volume c d :=
      fun x c d hcd hx hxz => intervalIntegrable_edge_sub hh hU hUrect hhol hbound hcd hx hxz
    have hval : rectBdIntegral a₁ b₁ (-h) h (fun w => (w - z)⁻¹ * g w)
        = 2 * (Real.pi : ℂ) * Complex.I * g z := by
      rcases lt_or_gt_of_ne hzne with hzneg | hzpos
      · -- z.im < 0
        have hlt : ∀ᶠ j in atTop, e j < -z.im :=
          he0.eventually (isOpen_Iio.mem_nhds (by linarith : (0:ℝ) < -z.im))
        have hslab := slab_rect_tendsto_self (a := a₁) (b := b₁) (h := h) (M := M) (g := g) (z := z)
          hab hzre hzne hgcon hbound he he0 hjt
        have hevent : (fun j : ℕ => rectBdIntegral a₁ b₁ (-h) h (fun w => (w - z)⁻¹ * g w)
              - 2 * (Real.pi : ℂ) * Complex.I * g z)
              =ᶠ[atTop] (fun j : ℕ => rectBdIntegral a₁ b₁ (-(e j)) (e j) (fun w => (w - z)⁻¹ * g w)) := by
          filter_upwards [hlt] with j hj
          have hej := he j
          have hsubA : Set.uIcc (-h) (-(e j)) ⊆ Set.uIcc (-h) h :=
            uIcc_subset_of (le_refl _) (by linarith [hej.1, hh]) (by linarith [hej.2])
          have hsubB : Set.uIcc (-(e j)) h ⊆ Set.uIcc (-h) h :=
            uIcc_subset_of (by linarith [hej.2]) (le_refl _) (by linarith [hej.2])
          have hsubD : Set.uIcc (e j) h ⊆ Set.uIcc (-h) h :=
            uIcc_subset_of (by linarith [hej.1, hh]) (le_refl _) (le_of_lt hej.2)
          have hsubE : Set.uIcc (-(e j)) (e j) ⊆ Set.uIcc (-h) h :=
            uIcc_subset_of (by linarith [hej.2]) (le_of_lt hej.2) (by linarith [hej.1])
          have hba : b₁ ∈ Set.Icc a₁ b₁ := ⟨le_of_lt hab, le_refl b₁⟩
          have hbz : b₁ ≠ z.re := ne_of_gt hzre.2
          have haa : a₁ ∈ Set.Icc a₁ b₁ := ⟨le_refl a₁, le_of_lt hab⟩
          have haz : a₁ ≠ z.re := ne_of_lt hzre.1
          have hs1 : rectBdIntegral a₁ b₁ (-h) h (fun w => (w - z)⁻¹ * g w)
              = rectBdIntegral a₁ b₁ (-(e j)) h (fun w => (w - z)⁻¹ * g w)
                + rectBdIntegral a₁ b₁ (-h) (-(e j)) (fun w => (w - z)⁻¹ * g w) :=
            Work.TMComp.Kotani.rectBdIntegral_split (f := fun w => (w - z)⁻¹ * g w)
              (hI b₁ (-h) (-(e j)) hsubA hba hbz) (hI b₁ (-(e j)) h hsubB hba hbz)
              (hI a₁ (-h) (-(e j)) hsubA haa haz) (hI a₁ (-(e j)) h hsubB haa haz)
          have hs2 : rectBdIntegral a₁ b₁ (-(e j)) h (fun w => (w - z)⁻¹ * g w)
              = rectBdIntegral a₁ b₁ (e j) h (fun w => (w - z)⁻¹ * g w)
                + rectBdIntegral a₁ b₁ (-(e j)) (e j) (fun w => (w - z)⁻¹ * g w) :=
            Work.TMComp.Kotani.rectBdIntegral_split (f := fun w => (w - z)⁻¹ * g w)
              (hI b₁ (-(e j)) (e j) hsubE hba hbz) (hI b₁ (e j) h hsubD hba hbz)
              (hI a₁ (-(e j)) (e j) hsubE haa haz) (hI a₁ (e j) h hsubD haa haz)
          have hcif : rectBdIntegral a₁ b₁ (-h) (-(e j)) (fun w => (w - z)⁻¹ * g w)
              = 2 * (Real.pi : ℂ) * Complex.I * g z := by
            have hrectU : (Set.uIcc a₁ b₁ ×ℂ Set.uIcc (-h) (-(e j))) ⊆ U := by
              intro w hw; rw [Complex.mem_reProdIm] at hw
              obtain ⟨hwr, hwi⟩ := hw
              rw [Set.uIcc_of_le hab.le] at hwr
              rw [Set.uIcc_of_le (by linarith [hej.2] : (-h:ℝ) ≤ -(e j)), Set.mem_Icc] at hwi
              exact hUrect w hwr ⟨hwi.1, le_trans hwi.2 (by linarith [hej.1, hh])⟩
                (ne_of_lt (by linarith [hwi.2, hej.1] : w.im < 0))
            exact rectBdIntegral_cauchy z hzre.1 hzre.2 hzim.1 (by linarith [hj]) (hhol.mono hrectU)
          have hout : rectBdIntegral a₁ b₁ (e j) h (fun w => (w - z)⁻¹ * g w) = 0 := by
            apply rectBdIntegral_eq_zero_of_differentiableOn
            have hrectU : (Set.uIcc a₁ b₁ ×ℂ Set.uIcc (e j) h) ⊆ U := by
              intro w hw; rw [Complex.mem_reProdIm] at hw
              obtain ⟨hwr, hwi⟩ := hw
              rw [Set.uIcc_of_le hab.le] at hwr
              rw [Set.uIcc_of_le (le_of_lt hej.2)] at hwi
              exact hUrect w hwr ⟨le_trans (by linarith [hej.1, hh] : (-h:ℝ) ≤ e j) hwi.1, hwi.2⟩
                (ne_of_gt (by linarith [hej.1, hwi.1] : (0:ℝ) < w.im))
            have hznot : z ∉ (Set.uIcc a₁ b₁ ×ℂ Set.uIcc (e j) h) := by
              intro hzmem; rw [Complex.mem_reProdIm] at hzmem
              have h2 := hzmem.2
              rw [Set.uIcc_of_le (le_of_lt hej.2), Set.mem_Icc] at h2
              linarith [h2.1, hzneg]
            have h1 : DifferentiableOn ℂ (fun w : ℂ => (w - z)⁻¹) (Set.uIcc a₁ b₁ ×ℂ Set.uIcc (e j) h) := by
              intro w hw
              have hwz : w - z ≠ 0 := by
                intro hcon; apply hznot; rw [← sub_eq_zero.mp hcon]; exact hw
              exact ((differentiableAt_id.sub_const z).inv hwz).differentiableWithinAt
            exact h1.mul (hhol.mono hrectU)
          rw [hs1, hs2, hcif, hout]
          ring
        have h2 : Tendsto (fun j : ℕ => rectBdIntegral a₁ b₁ (-h) h (fun w => (w - z)⁻¹ * g w)
            - 2 * (Real.pi : ℂ) * Complex.I * g z) atTop
            (nhds (rectBdIntegral a₁ b₁ (-h) h (fun w => (w - z)⁻¹ * g w)
              - 2 * (Real.pi : ℂ) * Complex.I * g z)) := tendsto_const_nhds
        have h3 : Tendsto (fun j : ℕ => rectBdIntegral a₁ b₁ (-h) h (fun w => (w - z)⁻¹ * g w)
            - 2 * (Real.pi : ℂ) * Complex.I * g z) atTop (nhds 0) :=
          Tendsto.congr' hevent.symm hslab
        exact sub_eq_zero.mp (tendsto_nhds_unique h2 h3)
      · -- 0 < z.im
        have hlt : ∀ᶠ j in atTop, e j < z.im :=
          he0.eventually (isOpen_Iio.mem_nhds hzpos)
        have hslab := slab_rect_tendsto_self (a := a₁) (b := b₁) (h := h) (M := M) (g := g) (z := z)
          hab hzre hzne hgcon hbound he he0 hjt
        have hevent : (fun j : ℕ => rectBdIntegral a₁ b₁ (-h) h (fun w => (w - z)⁻¹ * g w)
              - 2 * (Real.pi : ℂ) * Complex.I * g z)
              =ᶠ[atTop] (fun j : ℕ => rectBdIntegral a₁ b₁ (-(e j)) (e j) (fun w => (w - z)⁻¹ * g w)) := by
          filter_upwards [hlt] with j hj
          have hej := he j
          have hsubC : Set.uIcc (-h) (e j) ⊆ Set.uIcc (-h) h :=
            uIcc_subset_of (le_refl _) (le_of_lt hej.2) (by linarith [hej.1, hh])
          have hsubD : Set.uIcc (e j) h ⊆ Set.uIcc (-h) h :=
            uIcc_subset_of (by linarith [hej.1, hh]) (le_refl _) (le_of_lt hej.2)
          have hsubA : Set.uIcc (-h) (-(e j)) ⊆ Set.uIcc (-h) h :=
            uIcc_subset_of (le_refl _) (by linarith [hej.1, hh]) (by linarith [hej.2])
          have hsubE : Set.uIcc (-(e j)) (e j) ⊆ Set.uIcc (-h) h :=
            uIcc_subset_of (by linarith [hej.2]) (le_of_lt hej.2) (by linarith [hej.1])
          have hba : b₁ ∈ Set.Icc a₁ b₁ := ⟨le_of_lt hab, le_refl b₁⟩
          have hbz : b₁ ≠ z.re := ne_of_gt hzre.2
          have haa : a₁ ∈ Set.Icc a₁ b₁ := ⟨le_refl a₁, le_of_lt hab⟩
          have haz : a₁ ≠ z.re := ne_of_lt hzre.1
          have hs1 : rectBdIntegral a₁ b₁ (-h) h (fun w => (w - z)⁻¹ * g w)
              = rectBdIntegral a₁ b₁ (e j) h (fun w => (w - z)⁻¹ * g w)
                + rectBdIntegral a₁ b₁ (-h) (e j) (fun w => (w - z)⁻¹ * g w) :=
            Work.TMComp.Kotani.rectBdIntegral_split (f := fun w => (w - z)⁻¹ * g w)
              (hI b₁ (-h) (e j) hsubC hba hbz) (hI b₁ (e j) h hsubD hba hbz)
              (hI a₁ (-h) (e j) hsubC haa haz) (hI a₁ (e j) h hsubD haa haz)
          have hs2 : rectBdIntegral a₁ b₁ (-h) (e j) (fun w => (w - z)⁻¹ * g w)
              = rectBdIntegral a₁ b₁ (-(e j)) (e j) (fun w => (w - z)⁻¹ * g w)
                + rectBdIntegral a₁ b₁ (-h) (-(e j)) (fun w => (w - z)⁻¹ * g w) :=
            Work.TMComp.Kotani.rectBdIntegral_split (f := fun w => (w - z)⁻¹ * g w)
              (hI b₁ (-h) (-(e j)) hsubA hba hbz) (hI b₁ (-(e j)) (e j) hsubE hba hbz)
              (hI a₁ (-h) (-(e j)) hsubA haa haz) (hI a₁ (-(e j)) (e j) hsubE haa haz)
          have hcif : rectBdIntegral a₁ b₁ (e j) h (fun w => (w - z)⁻¹ * g w)
              = 2 * (Real.pi : ℂ) * Complex.I * g z := by
            have hrectU : (Set.uIcc a₁ b₁ ×ℂ Set.uIcc (e j) h) ⊆ U := by
              intro w hw; rw [Complex.mem_reProdIm] at hw
              obtain ⟨hwr, hwi⟩ := hw
              rw [Set.uIcc_of_le hab.le] at hwr
              rw [Set.uIcc_of_le (le_of_lt hej.2)] at hwi
              exact hUrect w hwr ⟨le_trans (by linarith [hej.1, hh] : (-h:ℝ) ≤ e j) hwi.1, hwi.2⟩
                (ne_of_gt (by linarith [hej.1, hwi.1] : (0:ℝ) < w.im))
            exact rectBdIntegral_cauchy z hzre.1 hzre.2 hj hzim.2 (hhol.mono hrectU)
          have hout : rectBdIntegral a₁ b₁ (-h) (-(e j)) (fun w => (w - z)⁻¹ * g w) = 0 := by
            apply rectBdIntegral_eq_zero_of_differentiableOn
            have hrectU : (Set.uIcc a₁ b₁ ×ℂ Set.uIcc (-h) (-(e j))) ⊆ U := by
              intro w hw; rw [Complex.mem_reProdIm] at hw
              obtain ⟨hwr, hwi⟩ := hw
              rw [Set.uIcc_of_le hab.le] at hwr
              rw [Set.uIcc_of_le (by linarith [hej.2] : (-h:ℝ) ≤ -(e j)), Set.mem_Icc] at hwi
              exact hUrect w hwr ⟨hwi.1, le_trans hwi.2 (by linarith [hej.1, hh])⟩
                (ne_of_lt (by linarith [hwi.2, hej.1] : w.im < 0))
            have hznot : z ∉ (Set.uIcc a₁ b₁ ×ℂ Set.uIcc (-h) (-(e j))) := by
              intro hzmem; rw [Complex.mem_reProdIm] at hzmem
              have h2 := hzmem.2
              rw [Set.uIcc_of_le (by linarith [hej.2] : (-h:ℝ) ≤ -(e j)), Set.mem_Icc] at h2
              linarith [h2.2, hzpos]
            have h1 : DifferentiableOn ℂ (fun w : ℂ => (w - z)⁻¹) (Set.uIcc a₁ b₁ ×ℂ Set.uIcc (-h) (-(e j))) := by
              intro w hw
              have hwz : w - z ≠ 0 := by
                intro hcon; apply hznot; rw [← sub_eq_zero.mp hcon]; exact hw
              exact ((differentiableAt_id.sub_const z).inv hwz).differentiableWithinAt
            exact h1.mul (hhol.mono hrectU)
          rw [hs1, hs2, hcif, hout]
          ring
        have h2 : Tendsto (fun j : ℕ => rectBdIntegral a₁ b₁ (-h) h (fun w => (w - z)⁻¹ * g w)
            - 2 * (Real.pi : ℂ) * Complex.I * g z) atTop
            (nhds (rectBdIntegral a₁ b₁ (-h) h (fun w => (w - z)⁻¹ * g w)
              - 2 * (Real.pi : ℂ) * Complex.I * g z)) := tendsto_const_nhds
        have h3 : Tendsto (fun j : ℕ => rectBdIntegral a₁ b₁ (-h) h (fun w => (w - z)⁻¹ * g w)
            - 2 * (Real.pi : ℂ) * Complex.I * g z) atTop (nhds 0) :=
          Tendsto.congr' hevent.symm hslab
        exact sub_eq_zero.mp (tendsto_nhds_unique h2 h3)
    change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        rectBdIntegral a₁ b₁ (-h) h (fun w => (w - z)⁻¹ * g w) = g z
    rw [hval]
    have hne : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (by norm_num) _) Complex.I_ne_zero
      exact_mod_cast Real.pi_ne_zero
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end Work.TMComp.RedC8
