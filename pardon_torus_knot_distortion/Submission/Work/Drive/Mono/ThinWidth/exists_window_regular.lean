import Mathlib
import Submission.Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic

namespace Work.Drive.Mono.ThinWidth

/-- **A symmetric pair of regular values in any window.**  For a `C²` periodic function `G` on the
plane and any nondegenerate window `(hmin, hmax)` there is `h` in the window such that both `a + h`
and `a - h` are regular values of `G` (no point of the level sets has vanishing derivative).

Route: `Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic` (import it) says
`volume {u | ∃ p, G p = u ∧ fderiv ℝ G p = 0} = 0`; call that set `N`.  Then `a + h` is regular iff
`h ∉ N - a` and `a - h` is regular iff `h ∉ a - N`; both are null
(`MeasureTheory.measure_preimage_add` for the translate, `MeasureTheory.Measure.map_neg_eq_self`
for the reflection; or argue with `MeasureTheory.ae_iff` and `MeasureTheory.Measure.ae_map_iff` to
avoid measurability obligations), so their union is null.  Since `hmin < hmax` the window has
positive measure (`Real.volume_Ioo`), hence it is not contained in a null set; take `h` outside. -/
theorem exists_window_regular {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 2 G)
    (hper₁ : ∀ p : ℝ × ℝ, G (p.1 + 2 * Real.pi, p.2) = G p)
    (hper₂ : ∀ p : ℝ × ℝ, G (p.1, p.2 + 2 * Real.pi) = G p)
    {a hmin hmax : ℝ} (hlt : hmin < hmax) :
    ∃ h : ℝ, hmin < h ∧ h < hmax ∧ (∀ p : ℝ × ℝ, G p = a + h → fderiv ℝ G p ≠ 0) ∧
      (∀ p : ℝ × ℝ, G p = a - h → fderiv ℝ G p ≠ 0) := by
  -- `N` is the set of critical values of `G`; Sard says it is null.
  set N : Set ℝ := {u : ℝ | ∃ p : ℝ × ℝ, G p = u ∧ fderiv ℝ G p = 0} with hNdef
  have hN : MeasureTheory.volume N = 0 := by
    rw [hNdef]
    exact Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic hG hper₁ hper₂
  -- The `h` for which `a + h` is critical, and those for which `a - h` is critical, are both null.
  have h1 : MeasureTheory.volume {h : ℝ | a + h ∈ N} = 0 := by
    have h := MeasureTheory.measure_preimage_add (MeasureTheory.volume : MeasureTheory.Measure ℝ) a N
    show MeasureTheory.volume ((fun h : ℝ => a + h) ⁻¹' N) = 0
    rw [h, hN]
  have h2 : MeasureTheory.volume {h : ℝ | a - h ∈ N} = 0 := by
    have key : {h : ℝ | a - h ∈ N} = Neg.neg ⁻¹' {h : ℝ | a + h ∈ N} := by
      ext h; simp [sub_eq_add_neg]
    rw [key]
    exact (MeasureTheory.Measure.measurePreserving_neg
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)).preimage_null h1
  have hbad : MeasureTheory.volume ({h : ℝ | a + h ∈ N} ∪ {h : ℝ | a - h ∈ N}) = 0 :=
    MeasureTheory.measure_union_null h1 h2
  -- A nondegenerate window is not null, so it meets the complement of the bad set.
  suffices hmain : ∃ h : ℝ, h ∈ Set.Ioo hmin hmax ∧
      h ∉ ({h : ℝ | a + h ∈ N} ∪ {h : ℝ | a - h ∈ N}) by
    obtain ⟨h, hh, hnb⟩ := hmain
    refine ⟨h, hh.1, hh.2, ?_, ?_⟩
    · intro p hp hd; exact hnb (Or.inl ⟨p, hp, hd⟩)
    · intro p hp hd; exact hnb (Or.inr ⟨p, hp, hd⟩)
  by_contra hc
  rw [not_exists] at hc
  have hsub : Set.Ioo hmin hmax ⊆ ({h : ℝ | a + h ∈ N} ∪ {h : ℝ | a - h ∈ N}) := by
    intro h hh
    by_contra hnb
    exact hc h ⟨hh, hnb⟩
  have hz : MeasureTheory.volume (Set.Ioo hmin hmax) = 0 :=
    MeasureTheory.measure_mono_null hsub hbad
  rw [Real.volume_Ioo] at hz
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hlt))) hz

end Work.Drive.Mono.ThinWidth
