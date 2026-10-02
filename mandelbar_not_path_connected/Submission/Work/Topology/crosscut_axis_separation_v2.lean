import Mathlib
import Submission.Work.Topology.sphere_arcs_of_opposite_halfplanes
import Submission.Work.Topology.exists_path_avoiding_halfplane_arc
import Submission.Work.Topology.no_path_of_crosscut_two_sphere_arcs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Metric
open scoped Topology

namespace Work.Topology

noncomputable section

/-! ## Support: the continuous restriction of `β` to the unit interval -/

/-- The restriction of `β` to the unit interval, as a continuous map. -/
private def res (β : ℝ → ℂ) (hcont : ContinuousOn β (Set.Icc (0:ℝ) 1)) :
    C(Set.Icc (0:ℝ) 1, ℂ) := ⟨Set.domRestrict (Set.Icc (0:ℝ) 1) β, hcont.domRestrict⟩

private lemma range_res (β : ℝ → ℂ) (hcont : ContinuousOn β (Set.Icc (0:ℝ) 1)) :
    Set.range (res β hcont) = β '' Set.Icc (0:ℝ) 1 := by
  have hcomp : (res β hcont : Set.Icc (0:ℝ) 1 → ℂ) = β ∘ Subtype.val := rfl
  rw [hcomp, Set.range_comp, Subtype.range_val]

/-! ## Sign of the imaginary part on the two halves of `[0,1]` -/

/-- On the open interval `(0,v)` the imaginary part of `β` has constant sign. -/
private lemma im_sign_left {β : ℝ → ℂ} {v : ℝ} (hcont : ContinuousOn β (Set.Icc (0:ℝ) 1))
    (hv1 : v ≤ 1) (hax : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≠ v → (β t).im ≠ 0) :
    (∀ t ∈ Set.Ioo (0:ℝ) v, 0 < (β t).im) ∨ (∀ t ∈ Set.Ioo (0:ℝ) v, (β t).im < 0) := by
  have hsub : Set.Ioo (0:ℝ) v ⊆ Set.Icc (0:ℝ) 1 := fun t ht =>
    ⟨le_of_lt ht.1, le_of_lt (lt_of_lt_of_le ht.2 hv1)⟩
  have hcont_im : ContinuousOn (fun t : ℝ => (β t).im) (Set.Ioo (0:ℝ) v) :=
    Complex.continuous_im.comp_continuousOn (hcont.mono hsub)
  have hpc : IsPreconnected ((fun t : ℝ => (β t).im) '' Set.Ioo (0:ℝ) v) :=
    IsPreconnected.image isPreconnected_Ioo _ hcont_im
  have hsub2 : (fun t : ℝ => (β t).im) '' Set.Ioo (0:ℝ) v ⊆ Set.Ioi 0 ∪ Set.Iio 0 := by
    rintro y ⟨t, ht, rfl⟩
    have htIcc : t ∈ Set.Icc (0:ℝ) 1 := hsub ht
    have hne : (β t).im ≠ 0 := hax t htIcc (ne_of_lt ht.2)
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hdisj : Disjoint (Set.Ioi (0:ℝ)) (Set.Iio 0) :=
    Set.disjoint_left.mpr (by rintro a (ha : (0:ℝ) < a) (hb : a < (0:ℝ)); linarith)
  rcases hpc.subset_or_subset isOpen_Ioi isOpen_Iio hdisj hsub2 with h | h
  · left; intro t ht; exact h ⟨t, ht, rfl⟩
  · right; intro t ht; exact h ⟨t, ht, rfl⟩

/-- On the open interval `(v,1)` the imaginary part of `β` has constant sign. -/
private lemma im_sign_right {β : ℝ → ℂ} {v : ℝ} (hcont : ContinuousOn β (Set.Icc (0:ℝ) 1))
    (hv0 : 0 ≤ v) (hax : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≠ v → (β t).im ≠ 0) :
    (∀ t ∈ Set.Ioo v 1, 0 < (β t).im) ∨ (∀ t ∈ Set.Ioo v 1, (β t).im < 0) := by
  have hsub : Set.Ioo v 1 ⊆ Set.Icc (0:ℝ) 1 := fun t ht =>
    ⟨le_trans hv0 (le_of_lt ht.1), le_of_lt ht.2⟩
  have hcont_im : ContinuousOn (fun t : ℝ => (β t).im) (Set.Ioo v 1) :=
    Complex.continuous_im.comp_continuousOn (hcont.mono hsub)
  have hpc : IsPreconnected ((fun t : ℝ => (β t).im) '' Set.Ioo v 1) :=
    IsPreconnected.image isPreconnected_Ioo _ hcont_im
  have hsub2 : (fun t : ℝ => (β t).im) '' Set.Ioo v 1 ⊆ Set.Ioi 0 ∪ Set.Iio 0 := by
    rintro y ⟨t, ht, rfl⟩
    have htIcc : t ∈ Set.Icc (0:ℝ) 1 := hsub ht
    have hne : (β t).im ≠ 0 := hax t htIcc (ne_of_gt ht.1)
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hdisj : Disjoint (Set.Ioi (0:ℝ)) (Set.Iio 0) :=
    Set.disjoint_left.mpr (by rintro a (ha : (0:ℝ) < a) (hb : a < (0:ℝ)); linarith)
  rcases hpc.subset_or_subset isOpen_Ioi isOpen_Iio hdisj hsub2 with h | h
  · left; intro t ht; exact h ⟨t, ht, rfl⟩
  · right; intro t ht; exact h ⟨t, ht, rfl⟩

/-- A continuous function which is positive on an open interval is nonnegative at both
endpoints. -/
private lemma nonneg_of_Ioo_pos {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b)) (hpos : ∀ t ∈ Set.Ioo a b, 0 < f t) :
    0 ≤ f a ∧ 0 ≤ f b := by
  have ha : a ∈ Set.Icc a b := ⟨le_refl a, hab.le⟩
  have hb : b ∈ Set.Icc a b := ⟨hab.le, le_refl b⟩
  constructor
  · by_contra h
    have hlt : f a < 0 := lt_of_not_ge h
    obtain ⟨δ, hδpos, hδ⟩ :=
      (continuousWithinAt_iff.mp (hfc.continuousWithinAt ha)) (-(f a) / 2) (by linarith)
    set t : ℝ := a + min (δ / 2) ((b - a) / 2) with htdef
    have hminpos : 0 < min (δ / 2) ((b - a) / 2) := lt_min (by linarith) (by linarith)
    have hminle : min (δ / 2) ((b - a) / 2) ≤ (b - a) / 2 := min_le_right _ _
    have ht1 : a < t := by rw [htdef]; linarith
    have ht2 : t < b := by rw [htdef]; linarith
    have htmem : t ∈ Set.Icc a b := ⟨ht1.le, ht2.le⟩
    have hdist : dist t a < δ := by
      rw [Real.dist_eq, abs_of_pos (by rw [htdef]; linarith : (0:ℝ) < t - a)]
      have : t - a = min (δ / 2) ((b - a) / 2) := by rw [htdef]; ring
      rw [this]
      linarith [min_le_left (δ / 2) ((b - a) / 2)]
    have h1 := hδ htmem hdist
    rw [Real.dist_eq, abs_lt] at h1
    exact absurd (hpos t ⟨ht1, ht2⟩) (not_lt.mpr (by linarith [h1.2] : f t ≤ 0))
  · by_contra h
    have hlt : f b < 0 := lt_of_not_ge h
    obtain ⟨δ, hδpos, hδ⟩ :=
      (continuousWithinAt_iff.mp (hfc.continuousWithinAt hb)) (-(f b) / 2) (by linarith)
    set t : ℝ := b - min (δ / 2) ((b - a) / 2) with htdef
    have hminpos : 0 < min (δ / 2) ((b - a) / 2) := lt_min (by linarith) (by linarith)
    have hminle : min (δ / 2) ((b - a) / 2) ≤ (b - a) / 2 := min_le_right _ _
    have ht1 : a < t := by rw [htdef]; linarith
    have ht2 : t < b := by rw [htdef]; linarith
    have htmem : t ∈ Set.Icc a b := ⟨ht1.le, ht2.le⟩
    have hdist : dist t b < δ := by
      rw [Real.dist_eq, abs_of_neg (by rw [htdef]; linarith : t - b < 0)]
      have : -(t - b) = min (δ / 2) ((b - a) / 2) := by rw [htdef]; ring
      rw [this]
      linarith [min_le_left (δ / 2) ((b - a) / 2)]
    have h1 := hδ htmem hdist
    rw [Real.dist_eq, abs_lt] at h1
    exact absurd (hpos t ⟨ht1, ht2⟩) (not_lt.mpr (by linarith [h1.2] : f t ≤ 0))

/-- A continuous function which is negative on an open interval is nonpositive at both
endpoints. -/
private lemma nonpos_of_Ioo_neg {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b)) (hneg : ∀ t ∈ Set.Ioo a b, f t < 0) :
    f a ≤ 0 ∧ f b ≤ 0 := by
  have h := nonneg_of_Ioo_pos (f := fun t => -f t) hab hfc.neg (by
    intro t ht; simpa using hneg t ht)
  constructor <;> linarith [h.1, h.2]

/-- If `β` is positive on `(0,v)` then `(β 0).im > 0`. -/
private lemma im_zero_pos {β : ℝ → ℂ} {v : ℝ} (hcont : ContinuousOn β (Set.Icc (0:ℝ) 1))
    (hv1 : v ≤ 1) (hv0 : 0 < v) (hax : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≠ v → (β t).im ≠ 0)
    (h : ∀ t ∈ Set.Ioo (0:ℝ) v, 0 < (β t).im) : 0 < (β 0).im := by
  have hsub : Set.Icc (0:ℝ) v ⊆ Set.Icc (0:ℝ) 1 := fun t ht => ⟨ht.1, le_trans ht.2 hv1⟩
  have hc : ContinuousOn (fun t : ℝ => (β t).im) (Set.Icc (0:ℝ) v) :=
    Complex.continuous_im.comp_continuousOn (hcont.mono hsub)
  have h2 : 0 ≤ (β 0).im := (nonneg_of_Ioo_pos hv0 hc h).1
  have hne : (β 0).im ≠ 0 := hax 0 ⟨le_refl 0, by norm_num⟩ (ne_of_lt hv0)
  exact lt_of_le_of_ne h2 (Ne.symm hne)

/-- If `β` is negative on `(0,v)` then `(β 0).im < 0`. -/
private lemma im_zero_neg {β : ℝ → ℂ} {v : ℝ} (hcont : ContinuousOn β (Set.Icc (0:ℝ) 1))
    (hv1 : v ≤ 1) (hv0 : 0 < v) (hax : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≠ v → (β t).im ≠ 0)
    (h : ∀ t ∈ Set.Ioo (0:ℝ) v, (β t).im < 0) : (β 0).im < 0 := by
  have hsub : Set.Icc (0:ℝ) v ⊆ Set.Icc (0:ℝ) 1 := fun t ht => ⟨ht.1, le_trans ht.2 hv1⟩
  have hc : ContinuousOn (fun t : ℝ => (β t).im) (Set.Icc (0:ℝ) v) :=
    Complex.continuous_im.comp_continuousOn (hcont.mono hsub)
  have h2 : (β 0).im ≤ 0 := (nonpos_of_Ioo_neg hv0 hc h).1
  have hne : (β 0).im ≠ 0 := hax 0 ⟨le_refl 0, by norm_num⟩ (ne_of_lt hv0)
  exact lt_of_le_of_ne h2 hne

/-- If `β` is positive on `(v,1)` then `(β 1).im > 0`. -/
private lemma im_one_pos {β : ℝ → ℂ} {v : ℝ} (hcont : ContinuousOn β (Set.Icc (0:ℝ) 1))
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hax : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≠ v → (β t).im ≠ 0)
    (h : ∀ t ∈ Set.Ioo v 1, 0 < (β t).im) : 0 < (β 1).im := by
  have hsub : Set.Icc v 1 ⊆ Set.Icc (0:ℝ) 1 := fun t ht => ⟨le_trans hv0 ht.1, ht.2⟩
  have hc : ContinuousOn (fun t : ℝ => (β t).im) (Set.Icc v 1) :=
    Complex.continuous_im.comp_continuousOn (hcont.mono hsub)
  have h2 : 0 ≤ (β 1).im := (nonneg_of_Ioo_pos hv1 hc h).2
  have hne : (β 1).im ≠ 0 := hax 1 ⟨by norm_num, le_refl 1⟩ (ne_of_gt hv1)
  exact lt_of_le_of_ne h2 (Ne.symm hne)

/-- If `β` is negative on `(v,1)` then `(β 1).im < 0`. -/
private lemma im_one_neg {β : ℝ → ℂ} {v : ℝ} (hcont : ContinuousOn β (Set.Icc (0:ℝ) 1))
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hax : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≠ v → (β t).im ≠ 0)
    (h : ∀ t ∈ Set.Ioo v 1, (β t).im < 0) : (β 1).im < 0 := by
  have hsub : Set.Icc v 1 ⊆ Set.Icc (0:ℝ) 1 := fun t ht => ⟨le_trans hv0 ht.1, ht.2⟩
  have hc : ContinuousOn (fun t : ℝ => (β t).im) (Set.Icc v 1) :=
    Complex.continuous_im.comp_continuousOn (hcont.mono hsub)
  have h2 : (β 1).im ≤ 0 := (nonpos_of_Ioo_neg hv1 hc h).2
  have hne : (β 1).im ≠ 0 := hax 1 ⟨by norm_num, le_refl 1⟩ (ne_of_gt hv1)
  exact lt_of_le_of_ne h2 hne

/-- If `β` is positive on both halves of `(0,1)` then its image lies in the closed upper
half plane. -/
private lemma im_nonneg_of_halves {β : ℝ → ℂ} {v : ℝ} (hcont : ContinuousOn β (Set.Icc (0:ℝ) 1))
    (hv : β v = 0) (hv0 : 0 < v) (hv1 : v < 1)
    (hL : ∀ t ∈ Set.Ioo (0:ℝ) v, 0 < (β t).im) (hR : ∀ t ∈ Set.Ioo v 1, 0 < (β t).im) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ (β t).im := by
  have hsubL : Set.Icc (0:ℝ) v ⊆ Set.Icc (0:ℝ) 1 := fun t ht => ⟨ht.1, le_trans ht.2 hv1.le⟩
  have hsubR : Set.Icc v 1 ⊆ Set.Icc (0:ℝ) 1 := fun t ht => ⟨le_trans hv0.le ht.1, ht.2⟩
  have hEL : 0 ≤ (β 0).im ∧ 0 ≤ (β v).im :=
    nonneg_of_Ioo_pos hv0 (Complex.continuous_im.comp_continuousOn (hcont.mono hsubL)) hL
  have hER : 0 ≤ (β v).im ∧ 0 ≤ (β 1).im :=
    nonneg_of_Ioo_pos hv1 (Complex.continuous_im.comp_continuousOn (hcont.mono hsubR)) hR
  intro t ht
  rcases le_or_gt t v with hle | hgt
  · rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq, hv]; norm_num
    · rcases eq_or_lt_of_le ht.1 with heq0 | hpos
      · rw [← heq0]; exact hEL.1
      · exact (hL t ⟨hpos, hlt⟩).le
  · rcases eq_or_lt_of_le ht.2 with heq1 | hlt1
    · rw [heq1]; exact hER.2
    · exact (hR t ⟨hgt, hlt1⟩).le

/-- If `β` is negative on both halves of `(0,1)` then its image lies in the closed lower
half plane. -/
private lemma im_nonpos_of_halves {β : ℝ → ℂ} {v : ℝ} (hcont : ContinuousOn β (Set.Icc (0:ℝ) 1))
    (hv : β v = 0) (hv0 : 0 < v) (hv1 : v < 1)
    (hL : ∀ t ∈ Set.Ioo (0:ℝ) v, (β t).im < 0) (hR : ∀ t ∈ Set.Ioo v 1, (β t).im < 0) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, (β t).im ≤ 0 := by
  have hsubL : Set.Icc (0:ℝ) v ⊆ Set.Icc (0:ℝ) 1 := fun t ht => ⟨ht.1, le_trans ht.2 hv1.le⟩
  have hsubR : Set.Icc v 1 ⊆ Set.Icc (0:ℝ) 1 := fun t ht => ⟨le_trans hv0.le ht.1, ht.2⟩
  have hEL : (β 0).im ≤ 0 ∧ (β v).im ≤ 0 :=
    nonpos_of_Ioo_neg hv0 (Complex.continuous_im.comp_continuousOn (hcont.mono hsubL)) hL
  have hER : (β v).im ≤ 0 ∧ (β 1).im ≤ 0 :=
    nonpos_of_Ioo_neg hv1 (Complex.continuous_im.comp_continuousOn (hcont.mono hsubR)) hR
  intro t ht
  rcases le_or_gt t v with hle | hgt
  · rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq, hv]; norm_num
    · rcases eq_or_lt_of_le ht.1 with heq0 | hpos
      · rw [← heq0]; exact hEL.1
      · exact le_of_lt (hL t ⟨hpos, hlt⟩)
  · rcases eq_or_lt_of_le ht.2 with heq1 | hlt1
    · rw [heq1]; exact hER.2
    · exact le_of_lt (hR t ⟨hgt, hlt1⟩)

/-! ## The two directions -/

/-- **Opposite signs imply that no path avoids the arc**: the crosscut separates `-1` from
`1` in the disc. -/
private lemma no_path_of_arc_separation {β : ℝ → ℂ} {v : ℝ}
    (hcont : ContinuousOn β (Set.Icc (0:ℝ) 1)) (hinj : Set.InjOn β (Set.Icc (0:ℝ) 1))
    (hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≠ 0 → t ≠ 1 → β t ∈ Metric.ball (0:ℂ) 1)
    (h0 : β 0 ∈ Metric.sphere (0:ℂ) 1) (h1 : β 1 ∈ Metric.sphere (0:ℂ) 1)
    (hv0 : 0 < v) (hv1 : v < 1)
    (hax : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≠ v → (β t).im ≠ 0)
    (hpat : (0 < (β 0).im ∧ (β 1).im < 0) ∨ ((β 0).im < 0 ∧ 0 < (β 1).im)) :
    ¬ (∃ γ : C(Set.Icc (0:ℝ) 1, ℂ), γ 0 = -1 ∧ γ 1 = 1 ∧
      ∀ t, t ≠ 0 → t ≠ 1 → γ t ∈ Metric.ball (0:ℂ) 1 ∧ γ t ∉ β '' Set.Icc (0:ℝ) 1) := by
  have ha0 : (β 0).im ≠ 0 := hax 0 ⟨le_refl 0, by norm_num⟩ (ne_of_lt hv0)
  have ha1 : (β 1).im ≠ 0 := hax 1 ⟨by norm_num, le_refl 1⟩ (ne_of_gt hv1)
  have hpq : β 0 ≠ β 1 := by
    intro hh
    have h01 := hinj ⟨le_refl 0, by norm_num⟩ ⟨by norm_num, le_refl 1⟩ hh
    norm_num at h01
  have hβ : Function.Injective (res β hcont) :=
    fun a b hab => Subtype.ext (hinj a.2 b.2 (show β (a:ℝ) = β (b:ℝ) from hab))
  have hint : ∀ t : Set.Icc (0:ℝ) 1, β (t:ℝ) ≠ β 0 → β (t:ℝ) ≠ β 1 →
      β (t:ℝ) ∈ Metric.ball (0:ℂ) 1 := by
    intro t h1' h2'
    exact hmem t t.2 (fun hh => h1' (by rw [hh])) (fun hh => h2' (by rw [hh]))
  have hne0 : (-1 : ℂ) ≠ β 0 := by intro hh; exact ha0 (by rw [← hh]; simp)
  have hne1 : (-1 : ℂ) ≠ β 1 := by intro hh; exact ha1 (by rw [← hh]; simp)
  have hone0 : (1 : ℂ) ≠ β 0 := by intro hh; exact ha0 (by rw [← hh]; simp)
  have hone1 : (1 : ℂ) ≠ β 1 := by intro hh; exact ha1 (by rw [← hh]; simp)
  have sep : ∀ (α₁ α₂ : C(Set.Icc (0:ℝ) 1, ℂ)),
      Function.Injective α₁ → Function.Injective α₂ →
      (∀ t : Set.Icc (0:ℝ) 1, α₁ t ∈ Metric.sphere (0:ℂ) 1) →
      (∀ t : Set.Icc (0:ℝ) 1, α₂ t ∈ Metric.sphere (0:ℂ) 1) →
      α₁ 0 = β 0 → α₁ 1 = β 1 → α₂ 0 = β 0 → α₂ 1 = β 1 →
      Set.range α₁ ∪ Set.range α₂ = Metric.sphere (0:ℂ) 1 →
      (∀ s t : Set.Icc (0:ℝ) 1, α₁ s = α₂ t → s = 0 ∨ s = 1) →
      (-1 : ℂ) ∈ Set.range α₁ → (1 : ℂ) ∈ Set.range α₂ →
      ¬ (∃ γ : C(Set.Icc (0:ℝ) 1, ℂ), γ 0 = -1 ∧ γ 1 = 1 ∧
        ∀ t, t ≠ 0 → t ≠ 1 → γ t ∈ Metric.ball (0:ℂ) 1 ∧ γ t ∉ β '' Set.Icc (0:ℝ) 1) := by
    intro α₁ α₂ hα₁ hα₂ hα₁s hα₂s hα₁0 hα₁1 hα₂0 hα₂1 hcover hdisj hx hy hcon
    obtain ⟨γ, hγ0, hγ1, hγ⟩ := hcon
    refine no_path_of_crosscut_two_sphere_arcs hβ h0 h1 hint hα₁ hα₂ hα₁s hα₂s hα₁0
      hα₁1 hα₂0 hα₂1 hcover hdisj hx hne0 hne1 hy hone0 hone1 ⟨γ, hγ0, hγ1, ?_⟩
    intro t ht0 ht1
    exact ⟨(hγ t ht0 ht1).1, by rw [range_res]; exact (hγ t ht0 ht1).2⟩
  rcases hpat with hsgn | hsgn
  · obtain ⟨α₁, α₂, hα₁, hα₂, hα₁s, hα₂s, hα₁0, hα₁1, hα₂0, hα₂1, hcover, hdisj, hm⟩ :=
      sphere_arcs_of_opposite_halfplanes h0 h1 hpq (Or.inl hsgn)
    rcases hm with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact sep α₁ α₂ hα₁ hα₂ hα₁s hα₂s hα₁0 hα₁1 hα₂0 hα₂1 hcover hdisj hx hy
    · have hcover' : Set.range α₂ ∪ Set.range α₁ = Metric.sphere (0:ℂ) 1 := by
        rw [Set.union_comm]; exact hcover
      have hdisj' : ∀ s t : Set.Icc (0:ℝ) 1, α₂ s = α₁ t → s = 0 ∨ s = 1 := by
        intro s t hst
        rcases hdisj t s hst.symm with h | h
        · left; exact hα₂ (by rw [hst, h, hα₁0, ← hα₂0])
        · right; exact hα₂ (by rw [hst, h, hα₁1, ← hα₂1])
      exact sep α₂ α₁ hα₂ hα₁ hα₂s hα₁s hα₂0 hα₂1 hα₁0 hα₁1 hcover' hdisj' hy hx
  · obtain ⟨α₁, α₂, hα₁, hα₂, hα₁s, hα₂s, hα₁0, hα₁1, hα₂0, hα₂1, hcover, hdisj, hm⟩ :=
      sphere_arcs_of_opposite_halfplanes h0 h1 hpq (Or.inr hsgn)
    rcases hm with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact sep α₁ α₂ hα₁ hα₂ hα₁s hα₂s hα₁0 hα₁1 hα₂0 hα₂1 hcover hdisj hx hy
    · have hcover' : Set.range α₂ ∪ Set.range α₁ = Metric.sphere (0:ℂ) 1 := by
        rw [Set.union_comm]; exact hcover
      have hdisj' : ∀ s t : Set.Icc (0:ℝ) 1, α₂ s = α₁ t → s = 0 ∨ s = 1 := by
        intro s t hst
        rcases hdisj t s hst.symm with h | h
        · left; exact hα₂ (by rw [hst, h, hα₁0, ← hα₂0])
        · right; exact hα₂ (by rw [hst, h, hα₁1, ← hα₂1])
      exact sep α₂ α₁ hα₂ hα₁ hα₂s hα₁s hα₂0 hα₂1 hα₁0 hα₁1 hcover' hdisj' hy hx

/-- **Equal signs imply that a path avoids the arc**: the opposite half plane carries a path
from `-1` to `1` inside the disc. -/
private lemma exists_path_of_pos {β : ℝ → ℂ} {v : ℝ} (hcont : ContinuousOn β (Set.Icc (0:ℝ) 1))
    (hv : β v = 0) (hv0 : 0 < v) (hv1 : v < 1)
    (hL : ∀ t ∈ Set.Ioo (0:ℝ) v, 0 < (β t).im) (hR : ∀ t ∈ Set.Ioo v 1, 0 < (β t).im) :
    ∃ γ : C(Set.Icc (0:ℝ) 1, ℂ), γ 0 = -1 ∧ γ 1 = 1 ∧
      ∀ t, t ≠ 0 → t ≠ 1 → γ t ∈ Metric.ball (0:ℂ) 1 ∧ γ t ∉ β '' Set.Icc (0:ℝ) 1 := by
  have hnn' : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ (β t).im := im_nonneg_of_halves hcont hv hv0 hv1 hL hR
  have hnn : ∀ t : Set.Icc (0:ℝ) 1, 0 ≤ (res β hcont t).im := fun t => hnn' t t.2
  obtain ⟨γ, hγ0, hγ1, hγ⟩ := exists_path_avoiding_halfplane_arc (β := res β hcont) (Or.inl hnn)
  exact ⟨γ, hγ0, hγ1, fun t ht0 ht1 =>
    ⟨(hγ t ht0 ht1).1, by rw [← range_res β hcont]; exact (hγ t ht0 ht1).2⟩⟩

/-- **Equal signs imply that a path avoids the arc**: the opposite half plane carries a path
from `-1` to `1` inside the disc (negative version). -/
private lemma exists_path_of_neg {β : ℝ → ℂ} {v : ℝ} (hcont : ContinuousOn β (Set.Icc (0:ℝ) 1))
    (hv : β v = 0) (hv0 : 0 < v) (hv1 : v < 1)
    (hL : ∀ t ∈ Set.Ioo (0:ℝ) v, (β t).im < 0) (hR : ∀ t ∈ Set.Ioo v 1, (β t).im < 0) :
    ∃ γ : C(Set.Icc (0:ℝ) 1, ℂ), γ 0 = -1 ∧ γ 1 = 1 ∧
      ∀ t, t ≠ 0 → t ≠ 1 → γ t ∈ Metric.ball (0:ℂ) 1 ∧ γ t ∉ β '' Set.Icc (0:ℝ) 1 := by
  have hnn' : ∀ t ∈ Set.Icc (0:ℝ) 1, (β t).im ≤ 0 := im_nonpos_of_halves hcont hv hv0 hv1 hL hR
  have hnn : ∀ t : Set.Icc (0:ℝ) 1, (res β hcont t).im ≤ 0 := fun t => hnn' t t.2
  obtain ⟨γ, hγ0, hγ1, hγ⟩ := exists_path_avoiding_halfplane_arc (β := res β hcont) (Or.inr hnn)
  exact ⟨γ, hγ0, hγ1, fun t ht0 ht1 =>
    ⟨(hγ t ht0 ht1).1, by rw [← range_res β hcont]; exact (hγ t ht0 ht1).2⟩⟩

/-- **A crosscut of the open unit disc through the centre separates the two ends of the real
diameter iff it crosses the real axis there.**  `β` is an injective arc (restricted to `[0,1]`)
from a point of the unit circle through `0 = β v` to another point of the unit circle; it meets
the real axis only at `0`.  Then its two halves lie on opposite sides of the real axis **iff** no
path inside the open disc from `-1` to `1` avoids the image `β '' [0,1]`. -/
theorem crosscut_axis_separation_v2 {β : ℝ → ℂ} {v : ℝ}
    (hcont : ContinuousOn β (Set.Icc (0:ℝ) 1)) (hinj : Set.InjOn β (Set.Icc (0:ℝ) 1))
    (hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≠ 0 → t ≠ 1 → β t ∈ Metric.ball (0:ℂ) 1)
    (h0 : β 0 ∈ Metric.sphere (0:ℂ) 1) (h1 : β 1 ∈ Metric.sphere (0:ℂ) 1)
    (hv : β v = 0) (hv0 : 0 < v) (hv1 : v < 1)
    (hax : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≠ v → (β t).im ≠ 0) :
    (((∃ t ∈ Set.Ioo (0:ℝ) v, 0 < (β t).im) ∧ (∃ t ∈ Set.Ioo v 1, (β t).im < 0)) ∨
      ((∃ t ∈ Set.Ioo (0:ℝ) v, (β t).im < 0) ∧ (∃ t ∈ Set.Ioo v 1, 0 < (β t).im)))
    ↔ ¬ (∃ γ : C(Set.Icc (0:ℝ) 1, ℂ),
          γ 0 = -1 ∧ γ 1 = 1 ∧
            ∀ t, t ≠ 0 → t ≠ 1 →
              γ t ∈ Metric.ball (0:ℂ) 1 ∧ γ t ∉ β '' Set.Icc (0:ℝ) 1) := by
  have hLsign := im_sign_left hcont hv1.le hax
  have hRsign := im_sign_right hcont hv0.le hax
  constructor
  · intro hL
    have hpat : (0 < (β 0).im ∧ (β 1).im < 0) ∨ ((β 0).im < 0 ∧ 0 < (β 1).im) := by
      rcases hL with ⟨hle, hri⟩ | ⟨hle, hri⟩
      · have hp : ∀ t ∈ Set.Ioo (0:ℝ) v, 0 < (β t).im := by
          rcases hLsign with h | h
          · exact h
          · obtain ⟨t, ht, hpos⟩ := hle
            exact absurd (h t ht) (not_lt.mpr hpos.le)
        have hn : ∀ t ∈ Set.Ioo v 1, (β t).im < 0 := by
          rcases hRsign with h | h
          · obtain ⟨t, ht, hneg⟩ := hri
            exact absurd (h t ht) (not_lt.mpr hneg.le)
          · exact h
        exact Or.inl ⟨im_zero_pos hcont hv1.le hv0 hax hp, im_one_neg hcont hv0.le hv1 hax hn⟩
      · have hn : ∀ t ∈ Set.Ioo (0:ℝ) v, (β t).im < 0 := by
          rcases hLsign with h | h
          · obtain ⟨t, ht, hneg⟩ := hle
            exact absurd (h t ht) (not_lt.mpr hneg.le)
          · exact h
        have hp : ∀ t ∈ Set.Ioo v 1, 0 < (β t).im := by
          rcases hRsign with h | h
          · exact h
          · obtain ⟨t, ht, hpos⟩ := hri
            exact absurd (h t ht) (not_lt.mpr hpos.le)
        exact Or.inr ⟨im_zero_neg hcont hv1.le hv0 hax hn, im_one_pos hcont hv0.le hv1 hax hp⟩
    exact no_path_of_arc_separation hcont hinj hmem h0 h1 hv0 hv1 hax hpat
  · intro hR
    by_contra hL
    rcases hLsign with hLpos | hLneg
    · rcases hRsign with hRpos | hRneg
      · exact hR (exists_path_of_pos hcont hv hv0 hv1 hLpos hRpos)
      · exact hL (Or.inl ⟨⟨v / 2, by constructor <;> linarith,
            hLpos (v / 2) (by constructor <;> linarith)⟩,
          ⟨(v + 1) / 2, by constructor <;> linarith,
            hRneg ((v + 1) / 2) (by constructor <;> linarith)⟩⟩)
    · rcases hRsign with hRpos | hRneg
      · exact hL (Or.inr ⟨⟨v / 2, by constructor <;> linarith,
            hLneg (v / 2) (by constructor <;> linarith)⟩,
          ⟨(v + 1) / 2, by constructor <;> linarith,
            hRpos ((v + 1) / 2) (by constructor <;> linarith)⟩⟩)
      · exact hR (exists_path_of_neg hcont hv hv0 hv1 hLneg hRneg)

end

end Work.Topology
