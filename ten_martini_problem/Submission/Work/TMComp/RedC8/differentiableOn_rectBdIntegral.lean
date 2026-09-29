import Mathlib
import Submission.Work.TMComp.Kotani.RectDefs
import Submission.Work.TMComp.Kotani.cauchyLine_diffOn_horiz
import Submission.Work.TMComp.RedC8.cauchyLine_diffOn_vert

open MeasureTheory intervalIntegral Set Filter
open scoped Interval Topology

namespace Work.TMComp.RedC8

theorem differentiableOn_rectBdIntegral {a b h M : ℝ} (hab : a < b) (hh : 0 < h)
    {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hUrect : ∀ z : ℂ, z.re ∈ Set.Icc a b → z.im ∈ Set.Icc (-h) h → z.im ≠ 0 → z ∈ U)
    (hhol : DifferentiableOn ℂ g U)
    (hbound : ∀ z : ℂ, z.re ∈ Set.Icc a b → z.im ∈ Set.Icc (-h) h → z.im ≠ 0 → ‖g z‖ ≤ M) :
    DifferentiableOn ℂ
      (fun z => Work.TMComp.Kotani.rectBdIntegral a b (-h) h (fun w => (w - z)⁻¹ * g w))
      {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo (-h) h} := by
  have hgc : ContinuousOn g U := hhol.continuousOn
  -- the real number `0` is a null set
  have hne0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]; simp
  -- `uIoc` is contained in `Icc`
  have hsubh : uIoc a b ⊆ Set.Icc a b := by
    intro x hx; have := uIoc_subset_uIcc hx; rwa [uIcc_of_le hab.le] at this
  have hsubv : uIoc (-h) h ⊆ Set.Icc (-h) h := by
    intro x hx; have := uIoc_subset_uIcc hx
    rwa [uIcc_of_le (by linarith : -h ≤ h)] at this
  -- ### measurability of the horizontal traces
  have hmeas_h : ∀ c : ℝ, c ≠ 0 → c ∈ Set.Icc (-h) h →
      AEStronglyMeasurable (fun t : ℝ => g ((t : ℂ) + (c : ℂ) * Complex.I))
        (volume.restrict (uIoc a b)) := by
    intro c hc hcI
    apply ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ)) _ measurableSet_uIoc
    intro t ht
    have hre : ((t : ℂ) + (c : ℂ) * Complex.I).re = t := by simp
    have him : ((t : ℂ) + (c : ℂ) * Complex.I).im = c := by simp
    have hpt : (t : ℂ) + (c : ℂ) * Complex.I ∈ U :=
      hUrect _ (by rw [hre]; exact hsubh ht) (by rw [him]; exact hcI) (by rw [him]; exact hc)
    have hmap : ContinuousAt (fun t : ℝ => (t : ℂ) + (c : ℂ) * Complex.I) t := by fun_prop
    have hg : ContinuousAt g ((t : ℂ) + (c : ℂ) * Complex.I) := hgc.continuousAt (hU.mem_nhds hpt)
    exact (hg.comp' (f := fun t : ℝ => (t : ℂ) + (c : ℂ) * Complex.I) hmap).continuousWithinAt
  -- ### a.e. bound of the horizontal traces
  have hbnd_h : ∀ c : ℝ, c ≠ 0 → c ∈ Set.Icc (-h) h →
      ∀ᵐ t : ℝ ∂(volume.restrict (uIoc a b)), ‖g ((t : ℂ) + (c : ℂ) * Complex.I)‖ ≤ M := by
    intro c hc hcI
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with t ht
    have hre : ((t : ℂ) + (c : ℂ) * Complex.I).re = t := by simp
    have him : ((t : ℂ) + (c : ℂ) * Complex.I).im = c := by simp
    exact hbound _ (by rw [hre]; exact hsubh ht) (by rw [him]; exact hcI) (by rw [him]; exact hc)
  -- ### measurability of the vertical traces
  have hmeas_v : ∀ x₀ : ℝ, x₀ ∈ Set.Icc a b →
      AEStronglyMeasurable (fun t : ℝ => g ((x₀ : ℂ) + (t : ℂ) * Complex.I))
        (volume.restrict (uIoc (-h) h)) := by
    intro x₀ hx₀
    set W : Set ℝ := {t : ℝ | (x₀ : ℂ) + (t : ℂ) * Complex.I ∈ U} with hW
    have hWopen : IsOpen W := hU.preimage (by fun_prop)
    have hcont : ContinuousOn (fun t : ℝ => g ((x₀ : ℂ) + (t : ℂ) * Complex.I))
        (uIoc (-h) h ∩ W) := by
      intro t ht
      have hmap : ContinuousAt (fun t : ℝ => (x₀ : ℂ) + (t : ℂ) * Complex.I) t := by fun_prop
      have hg : ContinuousAt g ((x₀ : ℂ) + (t : ℂ) * Complex.I) :=
        hgc.continuousAt (hU.mem_nhds ht.2)
      exact (hg.comp' (f := fun t : ℝ => (x₀ : ℂ) + (t : ℂ) * Complex.I) hmap).continuousWithinAt
    have hmeas : AEStronglyMeasurable (fun t : ℝ => g ((x₀ : ℂ) + (t : ℂ) * Complex.I))
        (volume.restrict (uIoc (-h) h ∩ W)) :=
      hcont.aestronglyMeasurable (μ := (volume : Measure ℝ))
        (measurableSet_uIoc.inter hWopen.measurableSet)
    have hae : ((uIoc (-h) h ∩ W : Set ℝ)) =ᵐ[volume] (uIoc (-h) h) := by
      filter_upwards [hne0] with x hx0
      apply propext
      constructor
      · intro h; exact h.1
      · intro h
        refine ⟨h, ?_⟩
        have hre : ((x₀ : ℂ) + (x : ℂ) * Complex.I).re = x₀ := by simp
        have him : ((x₀ : ℂ) + (x : ℂ) * Complex.I).im = x := by simp
        exact hUrect _ (by rw [hre]; exact hx₀) (by rw [him]; exact hsubv h) (by rw [him]; exact hx0)
    rwa [Measure.restrict_congr_set hae] at hmeas
  -- ### a.e. bound of the vertical traces
  have hbnd_v : ∀ x₀ : ℝ, x₀ ∈ Set.Icc a b →
      ∀ᵐ t : ℝ ∂(volume.restrict (uIoc (-h) h)), ‖g ((x₀ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M := by
    intro x₀ hx₀
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hne0] with t ht0
    intro ht
    have hre : ((x₀ : ℂ) + (t : ℂ) * Complex.I).re = x₀ := by simp
    have him : ((x₀ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    exact hbound _ (by rw [hre]; exact hx₀) (by rw [him]; exact hsubv ht) (by rw [him]; exact ht0)
  -- ### the four boundary pieces
  have hbot := Work.TMComp.Kotani.cauchyLine_diffOn_horiz (a := a) (b := b) (c := -h) (M := M)
    (F := fun t : ℝ => g ((t : ℂ) + ((-h : ℝ) : ℂ) * Complex.I))
    (hmeas_h (-h) (neg_ne_zero.mpr (ne_of_gt hh)) (by constructor <;> linarith [hh]))
    (hbnd_h (-h) (neg_ne_zero.mpr (ne_of_gt hh)) (by constructor <;> linarith [hh]))
  have htop := Work.TMComp.Kotani.cauchyLine_diffOn_horiz (a := a) (b := b) (c := h) (M := M)
    (F := fun t : ℝ => g ((t : ℂ) + (h : ℂ) * Complex.I))
    (hmeas_h h (ne_of_gt hh) (by constructor <;> linarith [hh]))
    (hbnd_h h (ne_of_gt hh) (by constructor <;> linarith [hh]))
  have hright := cauchyLine_diffOn_vert (a := b) (c := -h) (d := h) (M := M)
    (F := fun t : ℝ => g ((b : ℂ) + (t : ℂ) * Complex.I))
    (hmeas_v b ⟨hab.le, le_rfl⟩) (hbnd_v b ⟨hab.le, le_rfl⟩)
  have hleft := cauchyLine_diffOn_vert (a := a) (c := -h) (d := h) (M := M)
    (F := fun t : ℝ => g ((a : ℂ) + (t : ℂ) * Complex.I))
    (hmeas_v a ⟨le_rfl, hab.le⟩) (hbnd_v a ⟨le_rfl, hab.le⟩)
  -- ### restrict to the open rectangle and combine
  have hS_bot : {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo (-h) h} ⊆ {z : ℂ | z.im ≠ -h} := by
    intro z hz h; linarith [hz.2.1, h]
  have hS_top : {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo (-h) h} ⊆ {z : ℂ | z.im ≠ h} :=
    fun z hz => ne_of_lt hz.2.2
  have hS_right : {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo (-h) h} ⊆ {z : ℂ | z.re ≠ b} :=
    fun z hz => ne_of_lt hz.1.2
  have hS_left : {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo (-h) h} ⊆ {z : ℂ | z.re ≠ a} := by
    intro z hz h; linarith [hz.1.1, h]
  have hcomb : DifferentiableOn ℂ
      (fun z : ℂ =>
        ((∫ t : ℝ in a..b, ((t : ℂ) + ((-h : ℝ) : ℂ) * Complex.I - z)⁻¹
              * g ((t : ℂ) + ((-h : ℝ) : ℂ) * Complex.I))
        - (∫ t : ℝ in a..b, ((t : ℂ) + ((h : ℝ) : ℂ) * Complex.I - z)⁻¹
              * g ((t : ℂ) + ((h : ℝ) : ℂ) * Complex.I)))
        + Complex.I * (∫ t : ℝ in (-h)..h, ((b : ℂ) + (t : ℂ) * Complex.I - z)⁻¹
              * g ((b : ℂ) + (t : ℂ) * Complex.I))
        - Complex.I * (∫ t : ℝ in (-h)..h, ((a : ℂ) + (t : ℂ) * Complex.I - z)⁻¹
              * g ((a : ℂ) + (t : ℂ) * Complex.I)))
      {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo (-h) h} :=
    (((hbot.mono hS_bot).sub (htop.mono hS_top)).add
      ((hright.mono hS_right).const_mul Complex.I)).sub ((hleft.mono hS_left).const_mul Complex.I)
  have hfun : (fun z : ℂ => Work.TMComp.Kotani.rectBdIntegral a b (-h) h
        (fun w => (w - z)⁻¹ * g w))
      = fun z : ℂ =>
        ((∫ t : ℝ in a..b, ((t : ℂ) + ((-h : ℝ) : ℂ) * Complex.I - z)⁻¹
              * g ((t : ℂ) + ((-h : ℝ) : ℂ) * Complex.I))
        - (∫ t : ℝ in a..b, ((t : ℂ) + ((h : ℝ) : ℂ) * Complex.I - z)⁻¹
              * g ((t : ℂ) + ((h : ℝ) : ℂ) * Complex.I)))
        + Complex.I * (∫ t : ℝ in (-h)..h, ((b : ℂ) + (t : ℂ) * Complex.I - z)⁻¹
              * g ((b : ℂ) + (t : ℂ) * Complex.I))
        - Complex.I * (∫ t : ℝ in (-h)..h, ((a : ℂ) + (t : ℂ) * Complex.I - z)⁻¹
              * g ((a : ℂ) + (t : ℂ) * Complex.I)) := by
    funext z
    simp only [Work.TMComp.Kotani.rectBdIntegral]
  rw [hfun]
  exact hcomb

end Work.TMComp.RedC8
