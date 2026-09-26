import Mathlib
import Submission.Work.Topology.PlaneCurve.jordanRectSetup
import Submission.Work.Topology.PlaneCurve.frontier_component_eq_range

/-!
# Arc membership for a simple closed plane curve

Let `γ : ℝ → ℂ` be continuous, `2π`-periodic and injective on `[0, 2π)`, and let `0 < θ < 2π`.
The two points `γ 0` and `γ θ` cut the trace of `γ` into two closed arcs
`γ '' Icc 0 θ` and `γ '' Icc θ (2π)`.  A connected subset of the trace that misses both points
lies entirely in one of the two arcs.

This is the structural input needed by Maehara's boundedness argument: the arc `δ₁ : Path m l`
supplied by `exists_windowConfig` avoids `±1`, hence is a connected subset of the trace missing the
two cut points, hence lies in the arc containing `l`; consequently it is disjoint from the *other*
arc, which can then serve as the left-to-right path in the crossing lemma.
-/

namespace Work.Topology.PlaneCurve

open Set

/-- **Arc membership.** -/
theorem isConnected_subset_arc_of_avoid {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    {C : Set ℂ} (hC : IsConnected C) (hCγ : C ⊆ Set.range γ)
    (h0 : γ 0 ∉ C) (hθ : γ θ ∉ C) :
    C ⊆ γ '' Set.Icc 0 θ ∨ C ⊆ γ '' Set.Icc θ (2 * Real.pi) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2π : γ (2 * Real.pi) ∉ C := by have := hper 0; rw [zero_add] at this; rw [this]; exact h0
  set S : Set ℝ := {t | t ∈ Set.Ico 0 (2 * Real.pi) ∧ γ t ∈ C} with hSdef
  -- (1) the trace of `S` is all of `C`
  have hImS : γ '' S = C := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨t, ht, rfl⟩
      exact ht.2
    · intro y hy
      have hy' : y ∈ γ '' Set.Icc 0 (2 * Real.pi) := by
        rw [← range_eq_image_Icc hper]; exact hCγ hy
      obtain ⟨t, ht, hty⟩ := hy'
      have htlt : t < 2 * Real.pi := by
        rcases lt_or_eq_of_le ht.2 with h | h
        · exact h
        · exact absurd (show γ (2 * Real.pi) ∈ C from h ▸ hty ▸ hy) h2π
      exact ⟨t, ⟨⟨ht.1, htlt⟩, hty ▸ hy⟩, hty⟩
  -- (2) `S` is an interval
  have hconv : ∀ t₁ t₂ t : ℝ, t₁ ∈ S → t₂ ∈ S → t₁ ≤ t → t ≤ t₂ → t ∈ S := by
    intro t₁ t₂ t ht₁ ht₂ hle₁ hle₂
    have htlt : t < 2 * Real.pi := lt_of_le_of_lt hle₂ ht₂.1.2
    have htS : t ∈ Set.Ico 0 (2 * Real.pi) := ⟨le_trans ht₁.1.1 hle₁, htlt⟩
    by_contra hnot
    have htC : γ t ∉ C := fun hc => hnot ⟨htS, hc⟩
    set u : Set ℂ := γ '' Set.Icc 0 t with hudef
    set v : Set ℂ := γ '' Set.Icc t (2 * Real.pi) with hvdef
    have hu_cl : IsClosed u := (isCompact_Icc.image hγ).isClosed
    have hv_cl : IsClosed v := (isCompact_Icc.image hγ).isClosed
    have hCuv : C ⊆ u ∪ v := by
      intro y hy
      have hy' : y ∈ γ '' Set.Icc 0 (2 * Real.pi) := by
        rw [← range_eq_image_Icc hper]; exact hCγ hy
      obtain ⟨s, hs, hsy⟩ := hy'
      rcases le_or_gt s t with hst | hts
      · exact Or.inl ⟨s, ⟨hs.1, hst⟩, hsy⟩
      · exact Or.inr ⟨s, ⟨le_of_lt hts, hs.2⟩, hsy⟩
    have hinter : C ∩ (u ∩ v) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hyC, ⟨⟨s₁, hs₁, hs₁y⟩, ⟨s₂, hs₂, hs₂y⟩⟩⟩
      have hss : γ s₁ = γ s₂ := by rw [hs₁y, hs₂y]
      have hs₁Ico : s₁ ∈ Set.Ico 0 (2 * Real.pi) := ⟨hs₁.1, lt_of_le_of_lt hs₁.2 htlt⟩
      rcases lt_or_eq_of_le hs₂.2 with hs₂lt | hs₂eq
      · have hs₂Ico : s₂ ∈ Set.Ico 0 (2 * Real.pi) := ⟨le_trans htS.1 hs₂.1, hs₂lt⟩
        have heq : s₁ = s₂ := hinj hs₁Ico hs₂Ico hss
        have hst : s₁ = t := le_antisymm hs₁.2 (by rw [heq]; exact hs₂.1)
        exact htC (hst ▸ (hs₁y ▸ hyC))
      · have : γ s₁ = γ 0 := by rw [hss, hs₂eq]; simpa using hper 0
        have hz : s₁ = 0 := hinj hs₁Ico ⟨le_refl 0, hπ⟩ this
        rw [hz] at hs₁y
        exact h0 (hs₁y ▸ hyC)
    have hsep : C ⊆ u ∨ C ⊆ v :=
      isPreconnected_iff_subset_of_disjoint_closed.mp hC.isPreconnected u v hu_cl hv_cl hCuv hinter
    rcases hsep with hCu | hCv
    · -- `γ t₂ ∈ C ⊆ u` and `γ t₂ ∈ v`
      have h1 : γ t₂ ∈ u := hCu ht₂.2
      have h2 : γ t₂ ∈ v := ⟨t₂, ⟨hle₂, ht₂.1.2.le⟩, rfl⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hinter) (γ t₂) ⟨ht₂.2, h1, h2⟩
    · -- `γ t₁ ∈ C ⊆ v` and `γ t₁ ∈ u`
      have h1 : γ t₁ ∈ v := hCv ht₁.2
      have h2 : γ t₁ ∈ u := ⟨t₁, ⟨ht₁.1.1, hle₁⟩, rfl⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hinter) (γ t₁) ⟨ht₁.2, h2, h1⟩
  -- (3) `S` lies in one of the two intervals
  have hSsub : S ⊆ Set.Ico 0 θ ∨ S ⊆ Set.Ico θ (2 * Real.pi) := by
    rcases S.eq_empty_or_nonempty with hS0 | ⟨t₀, ht₀⟩
    · left; rw [hS0]; exact Set.empty_subset _
    · rcases lt_or_gt_of_ne (fun h : t₀ = θ => hθ (h ▸ ht₀.2)) with hlt | hgt
      · left
        intro t ht
        refine ⟨ht.1.1, ?_⟩
        by_contra hcon
        exact hθ (hconv t₀ t θ ht₀ ht (le_of_lt hlt) (not_lt.mp hcon)).2
      · right
        intro t ht
        refine ⟨?_, ht.1.2⟩
        by_contra hcon
        exact hθ (hconv t t₀ θ ht ht₀ (le_of_lt (not_le.mp hcon)) (le_of_lt hgt)).2
  rcases hSsub with hS | hS
  · left
    rintro y hy
    obtain ⟨t, ht, hty⟩ : y ∈ γ '' S := by rw [hImS]; exact hy
    exact ⟨t, ⟨(hS ht).1, (hS ht).2.le⟩, hty⟩
  · right
    rintro y hy
    obtain ⟨t, ht, hty⟩ : y ∈ γ '' S := by rw [hImS]; exact hy
    exact ⟨t, ⟨(hS ht).1, (hS ht).2.le⟩, hty⟩

/-- The two closed arcs of the trace meet only in the two cut points. -/
theorem image_Icc_inter_image_Icc_subset {γ : ℝ → ℂ}
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi) :
    γ '' Set.Icc 0 θ ∩ γ '' Set.Icc θ (2 * Real.pi) ⊆ {γ 0, γ θ} := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  rintro y ⟨⟨s₁, hs₁, hs₁y⟩, ⟨s₂, hs₂, hs₂y⟩⟩
  have hss : γ s₁ = γ s₂ := by rw [hs₁y, hs₂y]
  obtain ⟨k, hk⟩ := Work.Smooth.SphereJordan.exists_int_sub_eq_of_periodic_injOn hper hinj hss
  have h1 : (k : ℝ) * (2 * Real.pi) ≤ 0 := by
    rw [← hk]; linarith [hs₁.2, hs₂.1]
  have h2 : -(2 * Real.pi) ≤ (k : ℝ) * (2 * Real.pi) := by
    rw [← hk]; linarith [hs₁.1, hs₂.2]
  have hk0 : (k : ℝ) ≤ 0 := by nlinarith [Real.pi_pos, h1]
  have hkm1 : (-1 : ℝ) ≤ (k : ℝ) := by nlinarith [Real.pi_pos, h2]
  have hkcase : k = 0 ∨ k = -1 := by
    have hk0' : k ≤ 0 := by exact_mod_cast hk0
    have hkm1' : (-1 : ℤ) ≤ k := by exact_mod_cast hkm1
    omega
  rcases hkcase with hk0' | hkm1'
  · right
    have : s₁ = s₂ := by
      have h := hk; rw [hk0'] at h; push_cast at h; linarith
    have hsθ : s₁ = θ := le_antisymm hs₁.2 (by rw [this]; exact hs₂.1)
    have hy : y = γ θ := by rw [← hs₁y, hsθ]
    simp [hy]
  · left
    have hsp : s₁ - s₂ = -(2 * Real.pi) := by
      have h := hk; rw [hkm1'] at h; push_cast at h; linarith
    have hs₁0 : s₁ = 0 := le_antisymm (by linarith [hsp, hs₂.2]) hs₁.1
    have hs₂2π : s₂ = 2 * Real.pi := by linarith [hsp, hs₁.1]
    have hy : y = γ 0 := by rw [← hs₁y, hs₁0]
    simp [hy]

/-- **Instantiation of `isConnected_subset_arc_of_avoid` for an arc of the trace.** -/
theorem path_range_subset_arc_of_avoid {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi) (h0 : γ 0 = -1) (hθ : γ θ = 1)
    {p q : ℂ} {δ : Path p q} (hδγ : ∀ t, δ t ∈ Set.range γ)
    (hδav : ∀ t, δ t ≠ -1 ∧ δ t ≠ 1) :
    Set.range δ ⊆ γ '' Set.Icc 0 θ ∨ Set.range δ ⊆ γ '' Set.Icc θ (2 * Real.pi) := by
  have hne : (Set.range δ).Nonempty := ⟨δ 1, 1, rfl⟩
  refine isConnected_subset_arc_of_avoid hγ hper hinj hθ0 hθ2 ⟨hne, ?_⟩ ?_ ?_ ?_
  · exact isPreconnected_range δ.continuous
  · rintro _ ⟨t, rfl⟩; exact hδγ t
  · rw [h0]; rintro ⟨t, ht⟩; exact (hδav t).1 ht
  · rw [hθ]; rintro ⟨t, ht⟩; exact (hδav t).2 ht

/-- If, in addition, the terminal point of `δ` lies in the first arc and not in the second, then the
image of `δ` is disjoint from the second arc. -/
theorem path_range_disjoint_second_arc {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi) (h0 : γ 0 = -1) (hθ : γ θ = 1)
    {p q : ℂ} {δ : Path p q} (hδγ : ∀ t, δ t ∈ Set.range γ)
    (hδav : ∀ t, δ t ≠ -1 ∧ δ t ≠ 1)
    (hq : q ∉ γ '' Set.Icc θ (2 * Real.pi)) :
    Set.range δ ∩ γ '' Set.Icc θ (2 * Real.pi) = ∅ := by
  rcases path_range_subset_arc_of_avoid hγ hper hinj hθ0 hθ2 h0 hθ hδγ hδav with h | h
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hyδ, hy2⟩
    have hycut : y ∈ {γ 0, γ θ} :=
      image_Icc_inter_image_Icc_subset hper hinj hθ0 hθ2 ⟨h hyδ, hy2⟩
    obtain ⟨t, hty⟩ := hyδ
    have hdt : δ t ∈ {γ 0, γ θ} := hty ▸ hycut
    rcases hdt with h' | h'
    · exact (hδav t).1 (by rw [h', h0])
    · rw [Set.mem_singleton_iff] at h'
      exact (hδav t).2 (by rw [h', hθ])
  · refine absurd (h ⟨1, rfl⟩) ?_
    rwa [Path.target]

/-- The arc of the trace from `γ θ` to `γ (2π)`, reparametrised so that `-1 ↦ γ (2π)` and
`1 ↦ γ θ`.  When `γ θ = 1` and `γ (2π) = -1` this is the left-to-right path used as `h` in the
crossing lemma (`crossing_rect`). -/
noncomputable def arcPath (γ : ℝ → ℂ) (θ : ℝ) : ℝ → ℂ :=
  fun s => γ (θ + ((1 - s) / 2) * (2 * Real.pi - θ))

theorem continuous_arcPath {γ : ℝ → ℂ} (hγ : Continuous γ) (θ : ℝ) :
    Continuous (arcPath γ θ) :=
  hγ.comp (by fun_prop)

theorem arcPath_neg_one (γ : ℝ → ℂ) (θ : ℝ) : arcPath γ θ (-1) = γ (2 * Real.pi) := by
  unfold arcPath; norm_num

theorem arcPath_one (γ : ℝ → ℂ) (θ : ℝ) : arcPath γ θ 1 = γ θ := by
  unfold arcPath; norm_num

/-- The parameter of `arcPath` stays in the arc's parameter interval. -/
theorem arcPath_arg_mem_Icc {θ s : ℝ} (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2 * Real.pi)
    (hs : s ∈ Set.Icc (-1:ℝ) 1) :
    θ + ((1 - s) / 2) * (2 * Real.pi - θ) ∈ Set.Icc θ (2 * Real.pi) := by
  obtain ⟨hs1, hs2⟩ := hs
  have hnn : 0 ≤ 2 * Real.pi - θ := by linarith
  constructor
  · have h1 : 0 ≤ (1 - s) / 2 := by linarith
    have := mul_nonneg h1 hnn
    linarith
  · have h1 : (1 - s) / 2 ≤ 1 := by linarith
    have := mul_le_mul_of_nonneg_right h1 hnn
    linarith

/-- For `s ∈ [-1, 1]` the point `arcPath γ θ s` lies on the arc `γ '' Icc θ (2π)`. -/
theorem arcPath_mem_arc {γ : ℝ → ℂ} {θ s : ℝ} (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2 * Real.pi)
    (hs : s ∈ Set.Icc (-1:ℝ) 1) :
    arcPath γ θ s ∈ γ '' Set.Icc θ (2 * Real.pi) :=
  ⟨_, arcPath_arg_mem_Icc hθ0 hθ2 hs, rfl⟩

end Work.Topology.PlaneCurve
