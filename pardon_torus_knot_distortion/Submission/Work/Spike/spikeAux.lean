import Mathlib
import Submission.Work.Smooth.JordanSeparation.arc_not_separate
import Submission.Work.Smooth.SphereJordan.interior_range_empty_of_injOn_Icc

/-!
# Auxiliary topology for the spike/slit lemma

Verified pieces of the decomposition of `Work.Smooth.SphereJordan.spikePreconnected` (see
`Submission/Work/Smooth/SphereJordan/PLAN_planeCrosscut.md`, section "The spike/slit lemma"):

* `exists_norm_gt_notMem` — a compact set misses points of arbitrarily large norm;
* `isPreconnected_compl_range_arc` — the complement of the trace of an injective arc in the plane
  is **preconnected** (obtained from `arc_not_separate` by clamping the parametrisation to `Icc 0
  1`);  this is the input needed for case P1 of the decomposition;
* `spike_inter_eq` — in the spike setting `K ∩ Set.range β = {β 0}`.

This file deliberately lives outside `Smooth/SphereJordan/`: the modules
`Smooth/JordanSeparation/isPreconnected_frontier_connectedComponentIn` and
`Smooth/JordanSeparation/exists_continuum_separating` define clashing names
(`isPreconnected_insert_of_mem_closure`), so `Smooth/SphereJordan/planeCrosscut.lean` (whose import
closure contains the latter) cannot also import `arc_not_separate`.  Files that need both trees must
live in a directory whose import closure avoids one of them, as here.
-/

open Set

namespace Work.Spike

noncomputable section

/-- Points of arbitrarily large norm outside a compact set. -/
theorem exists_norm_gt_notMem {C : Set ℂ} (hC : IsCompact C) (R : ℝ) :
    ∃ z : ℂ, R < ‖z‖ ∧ z ∉ C := by
  obtain ⟨r, hr⟩ := hC.isBounded.subset_ball (0 : ℂ)
  refine ⟨((|R| + |r| + 1 : ℝ) : ℂ), ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 : R ≤ |R| := le_abs_self R
    have h2 : (0:ℝ) ≤ |r| := abs_nonneg r
    linarith
  · intro hmem
    have hb := hr hmem
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)] at hb
    have h1 : r ≤ |r| := le_abs_self r
    have h2 : (0:ℝ) ≤ |R| := abs_nonneg R
    linarith

/-- The complement of the trace of an injective arc in the plane is preconnected. -/
theorem isPreconnected_compl_range_arc {β : C(Set.Icc (0 : ℝ) 1, ℂ)}
    (hβ : Function.Injective β) :
    IsPreconnected (Set.range β)ᶜ := by
  set f : ℝ → ℂ := fun t =>
    β ⟨max 0 (min 1 t), Set.mem_Icc.mpr
      ⟨le_max_left 0 (min 1 t), max_le (by norm_num) (min_le_left 1 t)⟩⟩
    with hfdef
  have hfc : Continuous f :=
    β.continuous.comp (Continuous.subtype_mk
      ((continuous_const.max (continuous_const.min continuous_id) :
        Continuous fun t : ℝ => max 0 (min 1 t))) _)
  have hfr : f '' Set.Icc (0 : ℝ) 1 = Set.range β := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨(u : ℝ), u.2, ?_⟩
      show β ⟨max 0 (min 1 (u : ℝ)), _⟩ = β u
      congr 1
      exact Subtype.ext (by
        show max 0 (min 1 (u : ℝ)) = (u : ℝ)
        rw [min_eq_right u.2.2, max_eq_right u.2.1])
  have hfi : Set.InjOn f (Set.Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    have h1 := hβ hst
    have h2 := Subtype.ext_iff.mp h1
    simp only at h2
    rw [min_eq_right hs.2, min_eq_right ht.2, max_eq_right hs.1, max_eq_right ht.1] at h2
    exact h2
  rw [← hfr]
  exact (Work.Smooth.JordanSeparation.arc_not_separate hfc hfi).isConnected.isPreconnected

/-- In the spike setting, `K ∩ range β = {β 0}`. -/
theorem spike_inter_eq {K : Set ℂ} {β : C(Set.Icc (0 : ℝ) 1, ℂ)}
    (hβ : Function.Injective β) (h₀ : β ⟨0, by norm_num⟩ ∈ K) (h₁ : β ⟨1, by norm_num⟩ ∉ K)
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ K) :
    K ∩ Set.range β = {β ⟨0, by norm_num⟩} := by
  ext z
  constructor
  · rintro ⟨hzK, t, rfl⟩
    by_cases ht0 : (t : ℝ) = 0
    · rw [show t = ⟨0, by norm_num⟩ from Subtype.ext ht0]
      exact rfl
    · exfalso
      have ht0' : (0 : ℝ) < t := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
      by_cases ht1 : (t : ℝ) = 1
      · exact h₁ (by rw [show t = ⟨1, by norm_num⟩ from Subtype.ext ht1] at hzK; exact hzK)
      · exact hint t ⟨ht0', lt_of_le_of_ne t.2.2 ht1⟩ hzK
  · rintro (rfl)
    exact ⟨h₀, ⟨⟨0, by norm_num⟩, rfl⟩⟩



/-- An open subset of a preconnected set that is closed in it is empty or everything.  (Local copy:
`Work.Smooth.SphereJordan.eq_empty_or_subset_of_clopen` lives in a clashing tree.) -/
theorem eq_empty_or_subset_of_clopen {Ω S : Set ℂ} (hΩ : IsOpen Ω) (hS : IsPreconnected S)
    (hsub : Ω ⊆ S) (hcl : closure Ω ∩ S ⊆ Ω) : Ω = ∅ ∨ S ⊆ Ω := by
  rcases hS.subset_or_subset hΩ isClosed_closure.isOpen_compl
      (Set.disjoint_left.mpr fun z hz1 hz2 => hz2 (subset_closure hz1)) (fun z hz => by
        by_cases hzΩ : z ∈ Ω
        · exact Or.inl hzΩ
        · exact Or.inr fun hzcl => hzΩ (hcl ⟨hzcl, hz⟩)) with h | h
  · exact Or.inr h
  · left
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    exact h (hsub hz) (subset_closure hz)

/-- The frontier of a component of the complement of a closed set is contained in the set
(`Work.Smooth.JordanSeparation.frontier_connectedComponentIn_eq`). -/
theorem frontier_connectedComponentIn_subset_of_isClosed {C : Set ℂ} (hC : IsClosed C) (x : ℂ) :
    frontier (connectedComponentIn Cᶜ x) ⊆ C := by
  rw [Work.Smooth.JordanSeparation.frontier_connectedComponentIn_eq hC]
  exact inter_subset_right

/-- **P1, `K` case.**  A bounded component of the complement of `K ∪ range β` meets `K`. -/
theorem boundedComponent_frontier_meets_K {K : Set ℂ} (hK : IsCompact K)
    {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    {x : ℂ} (hx : x ∉ K ∪ Set.range β)
    (hbdd : Bornology.IsBounded (connectedComponentIn (K ∪ Set.range β)ᶜ x)) :
    (frontier (connectedComponentIn (K ∪ Set.range β)ᶜ x) ∩ K).Nonempty := by
  classical
  set C : Set ℂ := K ∪ Set.range β with hCdef
  have hCcl : IsClosed C := hK.isClosed.union (isCompact_range β.continuous).isClosed
  set Ω : Set ℂ := connectedComponentIn Cᶜ x with hΩdef
  have hxΩ : x ∈ Ω := hΩdef ▸ mem_connectedComponentIn (by simpa [hCdef] using hx)
  have hΩo : IsOpen Ω := hΩdef ▸ hCcl.isOpen_compl.connectedComponentIn
  have hfrC : frontier Ω ⊆ C := hΩdef ▸ frontier_connectedComponentIn_subset_of_isClosed hCcl x
  have hΩsub : Ω ⊆ (Set.range β)ᶜ := by
    intro z hz hzβ
    exact (connectedComponentIn_subset Cᶜ x (hΩdef ▸ hz)) (by simp [hCdef, hzβ])
  by_contra hne
  have hfrβ : frontier Ω ⊆ Set.range β := by
    intro z hz
    have hzC : z ∈ K ∪ Set.range β := by rw [← hCdef]; exact hfrC hz
    rcases hzC with h | h
    · exact absurd (show (frontier Ω ∩ K).Nonempty from ⟨z, hz, h⟩) hne
    · exact h
  have hcl : closure Ω ∩ (Set.range β)ᶜ ⊆ Ω := by
    rintro z ⟨hzcl, hzβ⟩
    by_contra hzΩ
    exact hzβ (hfrβ ⟨hzcl, by rwa [hΩo.interior_eq]⟩)
  rcases eq_empty_or_subset_of_clopen hΩo (isPreconnected_compl_range_arc hβ) hΩsub hcl with
    h | h
  · exact absurd (h ▸ hxΩ) (Set.notMem_empty x)
  · obtain ⟨R, hR⟩ := hbdd.subset_ball (0 : ℂ)
    obtain ⟨z, hzR, hzβ⟩ := exists_norm_gt_notMem (isCompact_range β.continuous) R
    have hzΩ : z ∈ Ω := h hzβ
    have hzball := hR hzΩ
    rw [Metric.mem_ball, dist_zero_right] at hzball
    linarith

/-- **P1, `range β` case.**  A bounded component of the complement of `K ∪ range β` meets the arc. -/
theorem boundedComponent_frontier_meets_range {K : Set ℂ} (hK : IsCompact K)
    (hconn : IsPreconnected Kᶜ) {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    {x : ℂ} (hx : x ∉ K ∪ Set.range β)
    (hbdd : Bornology.IsBounded (connectedComponentIn (K ∪ Set.range β)ᶜ x)) :
    (frontier (connectedComponentIn (K ∪ Set.range β)ᶜ x) ∩ Set.range β).Nonempty := by
  classical
  set C : Set ℂ := K ∪ Set.range β with hCdef
  have hCcl : IsClosed C := hK.isClosed.union (isCompact_range β.continuous).isClosed
  set Ω : Set ℂ := connectedComponentIn Cᶜ x with hΩdef
  have hxΩ : x ∈ Ω := hΩdef ▸ mem_connectedComponentIn (by simpa [hCdef] using hx)
  have hΩo : IsOpen Ω := hΩdef ▸ hCcl.isOpen_compl.connectedComponentIn
  have hfrC : frontier Ω ⊆ C := hΩdef ▸ frontier_connectedComponentIn_subset_of_isClosed hCcl x
  have hΩsub : Ω ⊆ Kᶜ := by
    intro z hz hzK
    exact (connectedComponentIn_subset Cᶜ x (hΩdef ▸ hz)) (by simp [hCdef, hzK])
  by_contra hne
  have hfrK : frontier Ω ⊆ K := by
    intro z hz
    have hzC : z ∈ K ∪ Set.range β := by rw [← hCdef]; exact hfrC hz
    rcases hzC with h | h
    · exact h
    · exact absurd (show (frontier Ω ∩ Set.range β).Nonempty from ⟨z, hz, h⟩) hne
  have hcl : closure Ω ∩ Kᶜ ⊆ Ω := by
    rintro z ⟨hzcl, hzK⟩
    by_contra hzΩ
    exact hzK (hfrK ⟨hzcl, by rwa [hΩo.interior_eq]⟩)
  rcases eq_empty_or_subset_of_clopen hΩo hconn hΩsub hcl with h | h
  · exact absurd (h ▸ hxΩ) (Set.notMem_empty x)
  · obtain ⟨R, hR⟩ := hbdd.subset_ball (0 : ℂ)
    obtain ⟨z, hzR, hzK⟩ := exists_norm_gt_notMem hK R
    have hzΩ : z ∈ Ω := h hzK
    have hzball := hR hzΩ
    rw [Metric.mem_ball, dist_zero_right] at hzball
    linarith


/-- **P2.**  In the spike setting, a *bounded* component of the complement of `K ∪ Set.range β`
has `β 0` on its frontier: the frontier of a component is a continuum (because `K ∪ Set.range β`
is a compact continuum) covered by the two non-empty closed pieces `∩ K` and `∩ Set.range β`, whose
intersection lies in `K ∩ Set.range β = {β 0}`. -/
theorem spike_boundedComponent_frontier {K : Set ℂ} (hK : IsCompact K) (hKconn : IsPreconnected K)
    (hconn : IsPreconnected Kᶜ) {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    (h₀ : β ⟨0, by norm_num⟩ ∈ K) (h₁ : β ⟨1, by norm_num⟩ ∉ K)
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ K)
    {x : ℂ} (hx : x ∉ K ∪ Set.range β)
    (hbdd : Bornology.IsBounded (connectedComponentIn (K ∪ Set.range β)ᶜ x)) :
    β ⟨0, by norm_num⟩ ∈ frontier (connectedComponentIn (K ∪ Set.range β)ᶜ x) := by
  classical
  set C : Set ℂ := K ∪ Set.range β with hCdef
  have hCcl : IsClosed C := hK.isClosed.union (isCompact_range β.continuous).isClosed
  have hxK : x ∉ K := by rw [hCdef] at hx; exact fun h => hx (Or.inl h)
  have hCpre : IsPreconnected C := by
    rw [hCdef]
    exact IsPreconnected.union' ⟨β ⟨0, by norm_num⟩, h₀, ⟨⟨0, by norm_num⟩, rfl⟩⟩
      hKconn (isPreconnected_range β.continuous)
  have hCne : C.Nonempty := ⟨β ⟨0, by norm_num⟩, by rw [hCdef]; exact Or.inl h₀⟩
  have hCcomp : IsCompact C := hK.union (isCompact_range β.continuous)
  have hxC : x ∉ C := by rwa [hCdef]
  have hfrpre : IsPreconnected (frontier (connectedComponentIn Cᶜ x)) :=
    (Work.Smooth.JordanSeparation.frontier_component_continuum hCcomp hCpre hCne hxC).2
  obtain ⟨z₁, hz₁fr, hz₁K⟩ := boundedComponent_frontier_meets_K hK hβ hx hbdd
  obtain ⟨z₂, hz₂fr, hz₂β⟩ := boundedComponent_frontier_meets_range hK hconn hβ hx hbdd
  have hinter : K ∩ Set.range β = {β ⟨0, by norm_num⟩} := spike_inter_eq hβ h₀ h₁ hint
  have hsub : frontier (connectedComponentIn Cᶜ x) ⊆ K ∪ Set.range β := by
    intro z hz
    have h1 := frontier_connectedComponentIn_subset_of_isClosed hCcl x hz
    rwa [hCdef] at h1
  by_contra hcon
  have hdisj : frontier (connectedComponentIn Cᶜ x) ∩ (K ∩ Set.range β) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro w ⟨hwfr, hwK, hwβ⟩
    have hw : w = β ⟨0, by norm_num⟩ := by
      have : w ∈ K ∩ Set.range β := ⟨hwK, hwβ⟩
      rwa [hinter] at this
    exact hcon (hw ▸ hwfr)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hfrpre) K (Set.range β)
      hK.isClosed (isCompact_range β.continuous).isClosed hsub hdisj with h | h
  · have hz₂ : z₂ = β ⟨0, by norm_num⟩ := by
      have : z₂ ∈ K ∩ Set.range β := ⟨h hz₂fr, hz₂β⟩
      rwa [hinter] at this
    exact hcon (hz₂ ▸ hz₂fr)
  · have hz₁ : z₁ = β ⟨0, by norm_num⟩ := by
      have : z₁ ∈ K ∩ Set.range β := ⟨hz₁K, h hz₁fr⟩
      rwa [hinter] at this
    exact hcon (hz₁ ▸ hz₁fr)


/-- A point outside a closed set has a ball inside its complement. -/
theorem exists_ball_subset_compl {s : Set ℂ} (hs : IsClosed s) {x : ℂ} (hx : x ∉ s) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ sᶜ :=
  Metric.isOpen_iff.mp hs.isOpen_compl x hx

/-- **`hloc` for the spike.**  At a point off both `K` and the arc, a small ball lies in the
complement of `K ∪ Set.range β`; being a ball, it is preconnected.  This is the first of the two
side conditions of `Work.Smooth.SphereJordan.isPreconnected_sdiff_of_germ` in the spike setting. -/
theorem local_preconnected_compl {K : Set ℂ} (hK : IsCompact K)
    {β : C(Set.Icc (0 : ℝ) 1, ℂ)} {x : ℂ} (hx : x ∉ K ∪ Set.range β) :
    ∃ ρ : ℝ, 0 < ρ ∧ IsPreconnected ((K ∪ Set.range β)ᶜ ∩ Metric.ball x ρ) := by
  have hs : IsClosed (K ∪ Set.range β) :=
    hK.isClosed.union (isCompact_range β.continuous).isClosed
  obtain ⟨ρ, hρ, hball⟩ := exists_ball_subset_compl hs hx
  refine ⟨ρ, hρ, ?_⟩
  have hEq : (K ∪ Set.range β)ᶜ ∩ Metric.ball x ρ = Metric.ball x ρ :=
    Set.Subset.antisymm inter_subset_right (fun z hz => ⟨hball hz, hz⟩)
  rw [hEq]
  exact (convex_ball x ρ).isPreconnected


/-- The arc `β`, read as a function on `ℝ` by clamping the parameter to `Icc 0 1`. -/
def clampArc (β : C(Set.Icc (0 : ℝ) 1, ℂ)) (t : ℝ) : ℂ :=
  β ⟨max 0 (min 1 t), Set.mem_Icc.mpr
    ⟨le_max_left 0 (min 1 t), max_le (by norm_num) (min_le_left 1 t)⟩⟩

theorem clampArc_continuous (β : C(Set.Icc (0 : ℝ) 1, ℂ)) : Continuous (clampArc β) :=
  β.continuous.comp (Continuous.subtype_mk
    ((continuous_const.max (continuous_const.min continuous_id) :
      Continuous fun t : ℝ => max 0 (min 1 t))) _)

theorem clampArc_eq (β : C(Set.Icc (0 : ℝ) 1, ℂ)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    clampArc β t = β ⟨t, ht⟩ := by
  simp only [clampArc]
  congr 1
  exact Subtype.ext (by
    show max 0 (min 1 t) = t
    rw [min_eq_right ht.2, max_eq_right ht.1])

theorem clampArc_range (β : C(Set.Icc (0 : ℝ) 1, ℂ)) :
    clampArc β '' Set.Icc (0 : ℝ) 1 = Set.range β := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, (clampArc_eq β ht).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(u : ℝ), u.2, clampArc_eq β u.2⟩

theorem clampArc_injOn {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β) :
    Set.InjOn (clampArc β) (Set.Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  rw [clampArc_eq β hs, clampArc_eq β ht] at hst
  exact congrArg Subtype.val (hβ hst)

/-- The trace of an injective arc has empty interior. -/
theorem interior_range_empty_of_injective {β : C(Set.Icc (0 : ℝ) 1, ℂ)}
    (hβ : Function.Injective β) : interior (Set.range β) = ∅ := by
  rw [← clampArc_range β]
  exact Work.Smooth.SphereJordan.interior_range_empty_of_injOn_Icc (by norm_num)
    (clampArc_continuous β) (clampArc_injOn hβ)

/-- **One point of the complement near the free end.**  There is a ball about `β 1` inside `Kᶜ`,
and it contains a point off the arc: a ball is a neighbourhood of its centre, whereas the arc has
empty interior. -/
theorem exists_point_ball_compl {K : Set ℂ} (hK : IsCompact K)
    {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    (h₁ : β ⟨1, by norm_num⟩ ∉ K) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (β ⟨1, by norm_num⟩) ρ ⊆ Kᶜ ∧
      ∃ z₀ ∈ Metric.ball (β ⟨1, by norm_num⟩) ρ, z₀ ∉ K ∪ Set.range β := by
  obtain ⟨ρ, hρ, hball⟩ := exists_ball_subset_compl hK.isClosed h₁
  have hnot : ∃ z ∈ Metric.ball (β ⟨1, by norm_num⟩) ρ, z ∉ Set.range β := by
    by_contra hcon
    push_neg at hcon
    have hmem : β ⟨1, by norm_num⟩ ∈ interior (Set.range β) :=
      mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (Metric.ball_mem_nhds _ hρ) hcon)
    rwa [interior_range_empty_of_injective hβ] at hmem
  obtain ⟨z₀, hz₀, hz₀β⟩ := hnot
  exact ⟨ρ, hρ, hball, z₀, hz₀, fun h => h.elim (fun hK' => hball hz₀ hK') hz₀β⟩

end

end Work.Spike
