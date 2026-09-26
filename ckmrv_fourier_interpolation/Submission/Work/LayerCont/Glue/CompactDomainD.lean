/-
# The compact piece `closure 𝒟 ∩ {δ ≤ Im ≤ T}`

`Work.LayerCont.Glue.exists_glued_on_nbd_of_charts_DomainD` takes the compactness of
`closure 𝒟 ∩ {δ ≤ Im ≤ T}` as a hypothesis.  This file supplies it: the set is closed (the closure
of `𝒟`, intersected with the closed height band) and contained in the box
`{-1 ≤ Re ≤ 1, δ ≤ Im ≤ T}`, which is compact as soon as `δ > 0` — it is closed and *bounded* in the
hyperbolic metric, the bound coming from `‖w - i‖ / √(Im w) ≥ dist w i`
(`UpperHalfPlane.dist_le_dist_coe_div_sqrt`), exactly as for `Work.Asymptotics.lowNegBox`.
-/
import Mathlib
import Submission.Work.LayerCont.Glue.Cover
import Submission.Work.Asymptotics.DomainD

set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.Glue

open Work.Asymptotics Work.LayerCont

/-- The box `{-1 ≤ Re ≤ 1, δ ≤ Im ≤ T}` of `ℍ`. -/
def box (δ T : ℝ) : Set UpperHalfPlane :=
  {z : UpperHalfPlane | -1 ≤ z.re ∧ z.re ≤ 1 ∧ δ ≤ z.im ∧ z.im ≤ T}

lemma isClosed_box (δ T : ℝ) : IsClosed (box δ T) := by
  have h : box δ T = {z : UpperHalfPlane | (-1 : ℝ) ≤ z.re} ∩ {z : UpperHalfPlane | z.re ≤ 1} ∩
      {z : UpperHalfPlane | δ ≤ z.im} ∩ {z : UpperHalfPlane | z.im ≤ T} := by
    ext z; simp [box, and_assoc]
  rw [h]
  exact (((isClosed_le continuous_const UpperHalfPlane.continuous_re).inter
    (isClosed_le UpperHalfPlane.continuous_re continuous_const)).inter
    (isClosed_le continuous_const UpperHalfPlane.continuous_im)).inter
    (isClosed_le UpperHalfPlane.continuous_im continuous_const)

/-- The box is bounded in the hyperbolic metric, for `δ > 0`: the hyperbolic distance to `i` is at
most the Euclidean distance divided by `√(Im ·)`, and both factors are bounded below/above. -/
lemma isBounded_box {δ : ℝ} (hδ : 0 < δ) (T : ℝ) : Bornology.IsBounded (box δ T) := by
  rw [Metric.isBounded_iff_subset_closedBall (⟨Complex.I, by simp⟩ : UpperHalfPlane)]
  refine ⟨(2 + |T|) / Real.sqrt δ + 1, fun w hw => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hw
  rw [Metric.mem_closedBall]
  have hstep : dist w (⟨Complex.I, by simp⟩ : UpperHalfPlane)
      ≤ ‖(w : ℂ) - Complex.I‖ / Real.sqrt (w.im * 1) := by
    have hh := UpperHalfPlane.dist_le_dist_coe_div_sqrt w (⟨Complex.I, by simp⟩ : UpperHalfPlane)
    rw [dist_eq_norm] at hh
    rw [show (↑(⟨Complex.I, by simp⟩ : UpperHalfPlane) : ℂ) = Complex.I from rfl,
        show (⟨Complex.I, by simp⟩ : UpperHalfPlane).im = 1 from rfl] at hh
    simpa using hh
  have hnum : ‖(w : ℂ) - Complex.I‖ ≤ 2 + |T| := by
    have h := Complex.norm_le_abs_re_add_abs_im ((w : ℂ) - Complex.I)
    rw [show ((w : ℂ) - Complex.I).re = w.re by simp,
        show ((w : ℂ) - Complex.I).im = w.im - 1 by simp] at h
    have hre : |w.re| ≤ 1 := abs_le.mpr ⟨by linarith, h2⟩
    have him : |w.im - 1| ≤ 1 + |T| := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le T, abs_nonneg T, hδ, h3],
        by linarith [le_abs_self T, abs_nonneg T, h4]⟩
    linarith
  have hden : Real.sqrt δ ≤ Real.sqrt (w.im * 1) := by
    have hw : w.im * 1 = w.im := by ring
    rw [hw]
    exact Real.sqrt_le_sqrt (by linarith)
  have hpos : 0 < Real.sqrt (w.im * 1) := Real.sqrt_pos.mpr (by linarith)
  have hposδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hbound : (2 + |T|) / Real.sqrt (w.im * 1) ≤ (2 + |T|) / Real.sqrt δ := by
    apply div_le_div_of_nonneg_left (by positivity) hposδ hden
  calc dist w (⟨Complex.I, by simp⟩ : UpperHalfPlane)
      ≤ ‖(w : ℂ) - Complex.I‖ / Real.sqrt (w.im * 1) := hstep
    _ ≤ (2 + |T|) / Real.sqrt (w.im * 1) := by
        apply div_le_div_of_nonneg_right hnum hpos.le
    _ ≤ (2 + |T|) / Real.sqrt δ := hbound
    _ ≤ (2 + |T|) / Real.sqrt δ + 1 := by linarith

/-- **The box is compact** for `δ > 0`. -/
lemma isCompact_box {δ : ℝ} (hδ : 0 < δ) (T : ℝ) : IsCompact (box δ T) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨isClosed_box δ T, isBounded_box hδ T⟩

/-- **The compact piece of `closure 𝒟`.** -/
theorem isCompact_closure_DomainD_inter {δ T : ℝ} (hδ : 0 < δ) :
    IsCompact (closure Work.Asymptotics.DomainD ∩ {z : UpperHalfPlane | δ ≤ z.im ∧ z.im ≤ T}) := by
  refine IsCompact.of_isClosed_subset (isCompact_box hδ T) ?_ ?_
  · rw [Set.setOf_and]
    exact isClosed_closure.inter ((isClosed_le continuous_const UpperHalfPlane.continuous_im).inter
      (isClosed_le UpperHalfPlane.continuous_im continuous_const))
  · -- `closure 𝒟 ⊆ {-1 ≤ Re ≤ 1}` and the height band is the same
    have hstrip : closure Work.Asymptotics.DomainD ⊆
        {z : UpperHalfPlane | (-1 : ℝ) ≤ z.re ∧ z.re ≤ 1} := by
      refine closure_minimal (fun z hz => ?_) ?_
      · exact ⟨(Work.Asymptotics.re_bounds_of_mem_DomainD hz).1.le,
          (Work.Asymptotics.re_bounds_of_mem_DomainD hz).2.le⟩
      · exact (isClosed_le continuous_const UpperHalfPlane.continuous_re).inter
          (isClosed_le UpperHalfPlane.continuous_re continuous_const)
    rintro z ⟨hz1, hz2⟩
    exact ⟨(hstrip hz1).1, (hstrip hz1).2, hz2.1, hz2.2⟩

/-- **The gluing over the compact piece of `closure 𝒟`, with no compactness hypothesis left.** -/
theorem exists_glued_on_nbd_of_charts_DomainD' {δ T : ℝ} (hδ : 0 < δ)
    (c : (closure Work.Asymptotics.DomainD ∩ {z : UpperHalfPlane | δ ≤ z.im ∧ z.im ≤ T} :
      Set UpperHalfPlane) → UpperHalfPlane)
    (ε : _ → ℝ) (chart : _ → UpperHalfPlane → ℂ)
    (hmem : ∀ x : (closure Work.Asymptotics.DomainD ∩
        {z : UpperHalfPlane | δ ≤ z.im ∧ z.im ≤ T} : Set UpperHalfPlane),
      (x : UpperHalfPlane) ∈ Metric.ball (c x) (ε x))
    (hchart : ∀ x, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (chart x) (Metric.ball (c x) (ε x)))
    (hpair : ∀ x y : (closure Work.Asymptotics.DomainD ∩
        {z : UpperHalfPlane | δ ≤ z.im ∧ z.im ≤ T} : Set UpperHalfPlane),
      ∃ V : Set UpperHalfPlane,
        V ⊆ Metric.ball (c x) (ε x) ∩ Metric.ball (c y) (ε y) ∧ IsOpen V ∧ V.Nonempty ∧
        Set.EqOn (chart x) (chart y) V) :
    ∃ (O : Set UpperHalfPlane) (F₂ : UpperHalfPlane → ℂ),
      IsOpen O ∧
      (closure Work.Asymptotics.DomainD ∩ {z : UpperHalfPlane | δ ≤ z.im ∧ z.im ≤ T}) ⊆ O ∧
      MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F₂ O :=
  exists_glued_on_nbd_of_charts_DomainD (isCompact_closure_DomainD_inter hδ) c ε chart
    hmem hchart hpair

end Work.LayerCont.Glue
