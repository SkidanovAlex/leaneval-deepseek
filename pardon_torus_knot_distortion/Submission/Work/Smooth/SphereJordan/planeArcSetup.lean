import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.DiscCurve
import Submission.Work.Smooth.Jordan.All

/-!
# The elementary configuration of the two-disc theta graph

Two disjoint embedded discs `D₁`, `D₂` in `ℂ` joined by two arcs `α`, `β` whose interiors avoid the
discs.  This module fixes the elementary consequences of the hypotheses of
`Work.Smooth.SphereJordan.planeAnnulusTwoComponents` which every proof of the two-component statement
consumes:

* the endpoints `α 0`, `β 0` lie on the *frontier* of `D₁` (and `α 1`, `β 1` on the frontier of
  `D₂`): an arc which immediately leaves a closed set starts on its frontier
  (`mem_frontier_of_mem_of_arc_avoid`);
* consequently each endpoint lies on the boundary circle of the corresponding disc, hence is
  `discCurve f (θ)` for some boundary parameter `θ`
  (`mem_trace_discCurve_of_mem_frontier`);
* each arc meets each disc in exactly one endpoint (`range_inter_left`, `range_inter_right`);
* the two arcs are disjoint (`disjoint_range_of_ends`).

These are the facts that make the four arcs `∂D₁`-part / `α` / `∂D₂`-part / `β̄` into genuine simple
closed curves; the gluing itself is the business of the companion modules.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## An arc leaving a closed set immediately starts on its frontier -/

/-- **If a continuous arc starts at a point `p` of a closed set `S` and immediately leaves `S`, then
`p` lies on the frontier of `S`.**  The point of the lemma is that the arc need not be injective and
`S` need not be a manifold: only continuity of the arc at its starting point is used. -/
theorem mem_frontier_of_mem_of_arc_avoid {S : Set ℂ} (hS : IsClosed S) {p : ℂ} (hp : p ∈ S)
    {γ : C(Set.Icc (0 : ℝ) 1, ℂ)} (h0 : γ ⟨0, by norm_num⟩ = p)
    (hav : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → γ t ∉ S) :
    p ∈ frontier S := by
  by_contra hpf
  have hmem : p ∈ interior S := by
    have h1 : p ∈ interior S ∪ frontier S := by
      rw [← closure_eq_interior_union_frontier S, hS.closure_eq]
      exact hp
    rcases h1 with h | h
    · exact h
    · exact absurd h hpf
  obtain ⟨ε, hεpos, hball⟩ := (Metric.isOpen_iff.mp isOpen_interior) p hmem
  have hnhds : Metric.ball p ε ∈ nhds (γ ⟨0, by norm_num⟩) := by
    rw [h0]; exact Metric.ball_mem_nhds p hεpos
  have hpre : γ ⁻¹' Metric.ball p ε ∈ nhds (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) :=
    γ.continuous.continuousAt.preimage_mem_nhds hnhds
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hpre
  set t₀ : ℝ := min δ 1 / 2 with ht₀
  have ht₀pos : 0 < t₀ := by
    have h1 : 0 < min δ 1 := lt_min hδpos (by norm_num)
    rw [ht₀]; linarith
  have ht₀lt1 : t₀ < 1 := by
    have h1 : min δ 1 ≤ 1 := min_le_right _ _
    rw [ht₀]; linarith
  have ht₀ltδ : t₀ < δ := by
    have h1 : min δ 1 ≤ δ := min_le_left _ _
    rw [ht₀]; linarith
  have hmem' : (⟨t₀, le_of_lt ht₀pos, le_of_lt ht₀lt1⟩ : Set.Icc (0 : ℝ) 1) ∈
      Metric.ball (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) δ := by
    rw [Metric.mem_ball, Subtype.dist_eq]
    show dist t₀ (0 : ℝ) < δ
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos ht₀pos]
    exact ht₀ltδ
  have hmem'' : γ ⟨t₀, le_of_lt ht₀pos, le_of_lt ht₀lt1⟩ ∈ Metric.ball p ε := hδ hmem'
  have hS' : γ ⟨t₀, le_of_lt ht₀pos, le_of_lt ht₀lt1⟩ ∈ S := interior_subset (hball hmem'')
  exact hav ⟨t₀, le_of_lt ht₀pos, le_of_lt ht₀lt1⟩ ⟨ht₀pos, ht₀lt1⟩ hS'

/-- **The same statement at the right endpoint**: an arc ending at a point `p` of a closed set `S`
and immediately preceding it outside `S` starts (at `t = 1`) on the frontier of `S`. -/
theorem mem_frontier_of_mem_of_arc_avoid_right {S : Set ℂ} (hS : IsClosed S) {p : ℂ} (hp : p ∈ S)
    {γ : C(Set.Icc (0 : ℝ) 1, ℂ)} (h1 : γ ⟨1, by norm_num⟩ = p)
    (hav : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → γ t ∉ S) :
    p ∈ frontier S := by
  by_contra hpf
  have hmem : p ∈ interior S := by
    have h1 : p ∈ interior S ∪ frontier S := by
      rw [← closure_eq_interior_union_frontier S, hS.closure_eq]
      exact hp
    rcases h1 with h | h
    · exact h
    · exact absurd h hpf
  obtain ⟨ε, hεpos, hball⟩ := (Metric.isOpen_iff.mp isOpen_interior) p hmem
  have hnhds : Metric.ball p ε ∈ nhds (γ ⟨1, by norm_num⟩) := by
    rw [h1]; exact Metric.ball_mem_nhds p hεpos
  have hpre : γ ⁻¹' Metric.ball p ε ∈ nhds (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) :=
    γ.continuous.continuousAt.preimage_mem_nhds hnhds
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hpre
  set t₀ : ℝ := 1 - min δ 1 / 2 with ht₀
  have hminpos : 0 < min δ 1 := lt_min hδpos (by norm_num)
  have ht₀lt1 : t₀ < 1 := by
    have h1 : 0 < min δ 1 / 2 := by linarith
    rw [ht₀]; linarith
  have ht₀pos : 0 < t₀ := by
    have h1 : min δ 1 ≤ 1 := min_le_right _ _
    rw [ht₀]; linarith
  have hdist : dist t₀ (1 : ℝ) < δ := by
    have h2 : dist t₀ (1 : ℝ) = 1 - t₀ := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t₀)]
    rw [h2]
    have h1 : min δ 1 ≤ δ := min_le_left _ _
    rw [ht₀]; linarith
  have hmem' : (⟨t₀, le_of_lt ht₀pos, le_of_lt ht₀lt1⟩ : Set.Icc (0 : ℝ) 1) ∈
      Metric.ball (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) δ := by
    rw [Metric.mem_ball, Subtype.dist_eq]
    exact hdist
  have hmem'' : γ ⟨t₀, le_of_lt ht₀pos, le_of_lt ht₀lt1⟩ ∈ Metric.ball p ε := hδ hmem'
  have hS' : γ ⟨t₀, le_of_lt ht₀pos, le_of_lt ht₀lt1⟩ ∈ S := interior_subset (hball hmem'')
  exact hav ⟨t₀, le_of_lt ht₀pos, le_of_lt ht₀lt1⟩ ⟨ht₀pos, ht₀lt1⟩ hS'


/-! ## The endpoints of the joining arcs lie on the boundary circles -/

/-- The image of the model disc under an injective continuous map is closed (it is compact). -/
theorem isClosed_of_range_disc {D : Set ℂ}
    (hD : ∃ f : C(Work.Smooth.SphereJordan.Disc, ℂ), Function.Injective f ∧ Set.range f = D) :
    IsClosed D := by
  obtain ⟨f, -, rfl⟩ := hD
  exact (isCompact_range f.continuous).isClosed

/-- **The four endpoints of the two joining arcs lie on the frontiers of the two discs.** -/
theorem endpoints_mem_frontier {D₁ D₂ : Set ℂ}
    (hD₁ : ∃ f : C(Work.Smooth.SphereJordan.Disc, ℂ), Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Work.Smooth.SphereJordan.Disc, ℂ), Function.Injective g ∧ Set.range g = D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, ℂ))
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂) :
    α ⟨0, by norm_num⟩ ∈ frontier D₁ ∧ β ⟨0, by norm_num⟩ ∈ frontier D₁ ∧
    α ⟨1, by norm_num⟩ ∈ frontier D₂ ∧ β ⟨1, by norm_num⟩ ∈ frontier D₂ := by
  have hc₁ : IsClosed D₁ := isClosed_of_range_disc hD₁
  have hc₂ : IsClosed D₂ := isClosed_of_range_disc hD₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mem_frontier_of_mem_of_arc_avoid hc₁ hα₀ rfl
      (fun t ht h => hαint t ht (Or.inl h))
  · exact mem_frontier_of_mem_of_arc_avoid hc₁ hβ₀ rfl
      (fun t ht h => hβint t ht (Or.inl h))
  · exact mem_frontier_of_mem_of_arc_avoid_right hc₂ hα₁ rfl
      (fun t ht h => hαint t ht (Or.inr h))
  · exact mem_frontier_of_mem_of_arc_avoid_right hc₂ hβ₁ rfl
      (fun t ht h => hβint t ht (Or.inr h))

/-- The frontier of the image of an injective disc map is traced by its boundary curve. -/
theorem mem_trace_discCurve_of_mem_frontier {f : C(Work.Smooth.SphereJordan.Disc, ℂ)}
    (hf : Function.Injective f) {p : ℂ} (hp : p ∈ frontier (Set.range f)) :
    p ∈ (discCurve f).trace :=
  discCurve_frontier_subset_trace hf hp

/-- **Each endpoint of a joining arc is a boundary point of the corresponding disc map**: there is a
boundary parameter `θ` at which the disc map takes that value. -/
theorem exists_circlePoint_eq_of_mem_trace {f : C(Work.Smooth.SphereJordan.Disc, ℂ)} {p : ℂ}
    (hp : p ∈ (discCurve f).trace) : ∃ θ : ℝ, f (Work.Smooth.Jordan.circlePoint θ) = p :=
  hp

/-! ## Each arc meets each disc in exactly one endpoint -/

/-- A point of `Icc 0 1` which is not interior is one of the two endpoints. -/
theorem eq_endpoints_of_mem_Icc {t : Set.Icc (0 : ℝ) 1} (ht : ¬ (t : ℝ) ∈ Set.Ioo 0 1) :
    t = ⟨0, by norm_num⟩ ∨ t = ⟨1, by norm_num⟩ := by
  have h0 : (0 : ℝ) ≤ t := t.2.1
  have h1 : (t : ℝ) ≤ 1 := t.2.2
  rw [Set.mem_Ioo, not_and_or] at ht
  push_neg at ht
  rcases ht with h | h
  · left; exact Subtype.ext (by simp only [Subtype.coe_mk]; linarith)
  · right; exact Subtype.ext (by simp only [Subtype.coe_mk]; linarith)

/-- **An arc can only meet the first disc at the parameter `0`.** -/
theorem eq_zero_of_mem_left {D₁ D₂ : Set ℂ} (hdisj : Disjoint D₁ D₂)
    {γ : C(Set.Icc (0 : ℝ) 1, ℂ)}
    (hγ₀ : γ ⟨0, by norm_num⟩ ∈ D₁) (hγ₁ : γ ⟨1, by norm_num⟩ ∈ D₂)
    (hγint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → γ t ∉ D₁ ∪ D₂)
    {t : Set.Icc (0 : ℝ) 1} (ht : γ t ∈ D₁) : (t : ℝ) = 0 := by
  by_cases h0 : (t : ℝ) = 0
  · exact h0
  · exfalso
    have h0' : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm h0)
    by_cases h1 : (t : ℝ) = 1
    · have he : γ t = γ ⟨1, by norm_num⟩ := congrArg γ (Subtype.ext (by simpa using h1))
      exact Set.disjoint_left.mp hdisj ht (he ▸ hγ₁)
    · have h1' : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 h1
      exact hγint t ⟨h0', h1'⟩ (Or.inl ht)

/-- **An arc can only meet the second disc at the parameter `1`.** -/
theorem eq_one_of_mem_right {D₁ D₂ : Set ℂ} (hdisj : Disjoint D₁ D₂)
    {γ : C(Set.Icc (0 : ℝ) 1, ℂ)}
    (hγ₀ : γ ⟨0, by norm_num⟩ ∈ D₁) (hγ₁ : γ ⟨1, by norm_num⟩ ∈ D₂)
    (hγint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → γ t ∉ D₁ ∪ D₂)
    {t : Set.Icc (0 : ℝ) 1} (ht : γ t ∈ D₂) : (t : ℝ) = 1 := by
  by_cases h1 : (t : ℝ) = 1
  · exact h1
  · exfalso
    have h1' : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 h1
    by_cases h0 : (t : ℝ) = 0
    · have he : γ t = γ ⟨0, by norm_num⟩ := congrArg γ (Subtype.ext (by simpa using h0))
      exact Set.disjoint_left.mp hdisj (he ▸ hγ₀) ht
    · have h0' : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm h0)
      exact hγint t ⟨h0', h1'⟩ (Or.inr ht)

/-- **The arc meets the first disc exactly in its first endpoint.** -/
theorem range_inter_left {D₁ D₂ : Set ℂ} (hdisj : Disjoint D₁ D₂)
    {α : C(Set.Icc (0 : ℝ) 1, ℂ)}
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂) :
    Set.range α ∩ D₁ = {α ⟨0, by norm_num⟩} := by
  ext x
  constructor
  · rintro ⟨⟨t, rfl⟩, hxt⟩
    rw [Set.mem_singleton_iff]
    by_cases ht : (t : ℝ) ∈ Set.Ioo 0 1
    · exact absurd (Or.inl hxt) (hαint t ht)
    · rcases eq_endpoints_of_mem_Icc ht with h | h
      · exact congrArg α h
      · exfalso
        exact Set.disjoint_left.mp hdisj (h ▸ hxt) hα₁
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    refine ⟨?_, hx ▸ hα₀⟩
    exact ⟨⟨0, by norm_num⟩, hx.symm⟩

/-- **The arc meets the second disc exactly in its second endpoint.** -/
theorem range_inter_right {D₁ D₂ : Set ℂ} (hdisj : Disjoint D₁ D₂)
    {α : C(Set.Icc (0 : ℝ) 1, ℂ)}
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂) :
    Set.range α ∩ D₂ = {α ⟨1, by norm_num⟩} := by
  ext x
  constructor
  · rintro ⟨⟨t, rfl⟩, hxt⟩
    rw [Set.mem_singleton_iff]
    by_cases ht : (t : ℝ) ∈ Set.Ioo 0 1
    · exact absurd (Or.inr hxt) (hαint t ht)
    · rcases eq_endpoints_of_mem_Icc ht with h | h
      · exfalso
        exact Set.disjoint_left.mp hdisj hα₀ (h ▸ hxt)
      · exact congrArg α h
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    refine ⟨?_, hx ▸ hα₁⟩
    exact ⟨⟨1, by norm_num⟩, hx.symm⟩

/-- **The two joining arcs are disjoint.**  They meet neither in the interior (the separation
hypothesis `hsep`) nor at the endpoints, where they lie in different discs. -/
theorem disjoint_range_of_ends {D₁ D₂ : Set ℂ} (hdisj : Disjoint D₁ D₂)
    {α β : C(Set.Icc (0 : ℝ) 1, ℂ)}
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩)
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩) :
    Disjoint (Set.range α) (Set.range β) := by
  rw [Set.disjoint_left]
  rintro x ⟨s, hs⟩ ⟨t, ht⟩
  have hst : α s = β t := hs.trans ht.symm
  by_cases hs' : (s : ℝ) ∈ Set.Ioo 0 1
  · by_cases ht' : (t : ℝ) ∈ Set.Ioo 0 1
    · exact hsep s t hs' ht' hst
    · rcases eq_endpoints_of_mem_Icc ht' with h | h
      · exact hαint s hs' (Or.inl (hst.trans (congrArg β h) ▸ hβ₀))
      · exact hαint s hs' (Or.inr (hst.trans (congrArg β h) ▸ hβ₁))
  · rcases eq_endpoints_of_mem_Icc hs' with h | h
    · have hmem : β t ∈ D₁ := (hst ▸ congrArg α h) ▸ hα₀
      have ht0 : (t : ℝ) = 0 := eq_zero_of_mem_left hdisj hβ₀ hβ₁ hβint hmem
      have he : β t = β ⟨0, by norm_num⟩ := congrArg β (Subtype.ext (by simpa using ht0))
      exact hαβ₀ ((congrArg α h).symm.trans (hst.trans he))
    · have hmem : β t ∈ D₂ := (hst ▸ congrArg α h) ▸ hα₁
      have ht1 : (t : ℝ) = 1 := eq_one_of_mem_right hdisj hβ₀ hβ₁ hβint hmem
      have he : β t = β ⟨1, by norm_num⟩ := congrArg β (Subtype.ext (by simpa using ht1))
      exact hαβ₁ ((congrArg α h).symm.trans (hst.trans he))

end

end Work.Smooth.SphereJordan
