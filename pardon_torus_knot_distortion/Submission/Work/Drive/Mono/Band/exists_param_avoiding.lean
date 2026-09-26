import Mathlib

/-!
# Avoiding two translates and a null set of slices, simultaneously

`Work.Drive.Mono.Band.exists_param_avoiding`: given a null set `S ⊆ ℝ²` and a null set `N ⊆ ℝ`,
and any non-degenerate interval `(hmin, hmax)`, there are `h ∈ (hmin, hmax)` and `t ∈ ℝ` with

  `a + h ∉ N`, `a - h ∉ N`, `(a + h, t) ∉ S`, `(a - h, t) ∉ S`.

This is the elementary "two moving points" measure-theoretic step: the set of `(h, t)` at which
one of the four membership statements holds is a finite union of null sets
(`S` pulled back by the two translations `(h,t) ↦ (a ± h, t)`, and the two vertical strips over
the null sets `(N - a)`, `(a - N)`), hence null; a non-degenerate rectangle is not null, so it
meets the complement.  Note that no completeness or measurable-hull argument is needed: the
translations and the reflection of the first coordinate are measure preserving on the nose.
-/

namespace Work.Drive.Mono.Band

open MeasureTheory

/-- Two points `a ± h` of the line, with `h` in a prescribed non-degenerate interval, avoid a null
set `N`; and the corresponding two vertical lines avoid a null set `S ⊆ ℝ²` at a common height
`t`. -/
theorem exists_param_avoiding {S : Set (ℝ × ℝ)} (hS : MeasureTheory.volume S = 0)
    {N : Set ℝ} (hN : MeasureTheory.volume N = 0) {a hmin hmax : ℝ} (hlt : hmin < hmax) :
    ∃ h t : ℝ, hmin < h ∧ h < hmax ∧ a + h ∉ N ∧ a - h ∉ N ∧
      (a + h, t) ∉ S ∧ (a - h, t) ∉ S := by
  -- The two pulls of `S` back by the translations `(h,t) ↦ (a + h, t)` and `(h,t) ↦ (a - h, t)`.
  have h1 : volume ((fun p : ℝ × ℝ => (a + p.1, p.2)) ⁻¹' S) = 0 := by
    have h : (fun p : ℝ × ℝ => (a + p.1, p.2)) = (fun p => (a, 0) + p) := by
      funext p
      simp [Prod.add_def]
    rw [h]
    exact (measure_preimage_add (volume : Measure (ℝ × ℝ)) (a, 0) S).trans hS
  have h2 : volume ((fun p : ℝ × ℝ => (a - p.1, p.2)) ⁻¹' S) = 0 := by
    have hlog : Measure.map (fun x : ℝ => x) (volume : Measure ℝ) = volume := Measure.map_id
    -- the reflection of the first coordinate preserves Lebesgue measure on `ℝ × ℝ`
    have hmap : Measure.map (fun p : ℝ × ℝ => (-p.1, p.2)) (volume : Measure (ℝ × ℝ)) = volume := by
      have h := Measure.map_prod_map (μa := (volume : Measure ℝ)) (μc := (volume : Measure ℝ))
        (f := fun x : ℝ => -x) (g := fun x : ℝ => x) measurable_neg measurable_id
      rw [Measure.map_neg_eq_self, hlog, ← MeasureTheory.Measure.volume_eq_prod] at h
      have hfun : (fun p : ℝ × ℝ => (-p.1, p.2)) = Prod.map Neg.neg id := by
        funext p; simp [Prod.map]
      rw [hfun]
      exact h.symm
    have hcomp : (fun p : ℝ × ℝ => (a - p.1, p.2))
        = (fun p : ℝ × ℝ => (a + p.1, p.2)) ∘ (fun p : ℝ × ℝ => (-p.1, p.2)) := by
      funext p; simp [sub_eq_add_neg]
    rw [hcomp, Set.preimage_comp]
    have hle := Measure.le_map_apply (μ := (volume : Measure (ℝ × ℝ)))
      (f := fun p : ℝ × ℝ => (-p.1, p.2)) (by fun_prop)
      ((fun p : ℝ × ℝ => (a + p.1, p.2)) ⁻¹' S)
    rw [hmap, h1] at hle
    exact le_antisymm hle bot_le
  -- The two vertical strips over the null sets `{a + h ∈ N}` and `{a - h ∈ N}`.
  have h3 : volume ({u : ℝ | a + u ∈ N} ×ˢ (Set.univ : Set ℝ)) = 0 := by
    have h3set : volume ({u : ℝ | a + u ∈ N}) = 0 := by
      exact (measure_preimage_add (volume : Measure ℝ) a N).trans hN
    rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod, h3set, zero_mul]
  have h4 : volume ({u : ℝ | a - u ∈ N} ×ˢ (Set.univ : Set ℝ)) = 0 := by
    have h4set : volume ({u : ℝ | a - u ∈ N}) = 0 := by
      have hmap : Measure.map (fun u : ℝ => a - u) (volume : Measure ℝ) = volume :=
        Measure.map_sub_left_eq_self (volume : Measure ℝ) a
      have hle := Measure.le_map_apply (μ := (volume : Measure ℝ))
        (f := fun u : ℝ => a - u) (measurable_const.sub measurable_id).aemeasurable N
      rw [hmap, hN] at hle
      exact le_antisymm hle bot_le
    rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod, h4set, zero_mul]
  -- The bad set of parameters `(h, t)`.
  set B : Set (ℝ × ℝ) :=
      ((fun p : ℝ × ℝ => (a + p.1, p.2)) ⁻¹' S ∪ (fun p : ℝ × ℝ => (a - p.1, p.2)) ⁻¹' S)
      ∪ {u : ℝ | a + u ∈ N} ×ˢ (Set.univ : Set ℝ)
      ∪ {u : ℝ | a - u ∈ N} ×ˢ (Set.univ : Set ℝ) with hB
  have hBnull : volume B = 0 := by
    rw [hB]
    exact measure_union_null (measure_union_null (measure_union_null h1 h2) h3) h4
  -- A non-degenerate rectangle has non-zero measure.
  have hstrip : volume ((Set.Ioo hmin hmax) ×ˢ (Set.Ioo (0:ℝ) 1)) ≠ 0 := by
    rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
    norm_num
    exact hlt
  have hnotsub : ¬ ((Set.Ioo hmin hmax) ×ˢ (Set.univ : Set ℝ) ⊆ B) := by
    intro hsub
    have hsub2 : (Set.Ioo hmin hmax) ×ˢ (Set.Ioo (0:ℝ) 1) ⊆ B :=
      (Set.prod_mono_right (Set.subset_univ _)).trans hsub
    have hle : volume ((Set.Ioo hmin hmax) ×ˢ (Set.Ioo (0:ℝ) 1)) ≤ volume B := measure_mono hsub2
    rw [hBnull] at hle
    exact hstrip (le_antisymm hle bot_le)
  obtain ⟨p, hpmem, hpnot⟩ := Set.not_subset.mp hnotsub
  obtain ⟨h, t⟩ := p
  rw [Set.mem_prod] at hpmem
  obtain ⟨hhmem, -⟩ := hpmem
  rw [Set.mem_Ioo] at hhmem
  rw [hB, Set.mem_union, Set.mem_union, Set.mem_union, not_or, not_or, not_or] at hpnot
  obtain ⟨⟨⟨hp1, hp2⟩, hp3⟩, hp4⟩ := hpnot
  exact ⟨h, t, hhmem.1, hhmem.2, fun hc => hp3 ⟨hc, trivial⟩, fun hc => hp4 ⟨hc, trivial⟩,
    fun hc => hp1 hc, fun hc => hp2 hc⟩

end Work.Drive.Mono.Band
