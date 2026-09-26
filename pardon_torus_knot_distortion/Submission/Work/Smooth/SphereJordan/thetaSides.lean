import Mathlib
import Submission.Work.Smooth.SphereJordan.planeThetaCurves
import Submission.Work.Smooth.SphereJordan.planeTwoDiscs
import Submission.Work.Smooth.SphereJordan.half_spans_of_plane
import Submission.Work.Smooth.SphereJordan.radialWinding
import Submission.Work.Smooth.SphereJordan.thetaWinding
import Submission.Work.Smooth.SphereJordan.discCurveSpans
import Submission.Work.Smooth.SphereJordan.DiscSpansAPI

/-!
# The side determination for the plane theta graph

This file isolates the geometric content of `Work.Smooth.SphereJordan.planeThetaSpans`: the two
simple closed curves of the theta configuration whose bounded/unbounded sides are the two
components of the complement of the theta graph.
-/

open Set
open Work.SphereJordan

set_option maxHeartbeats 1000000

namespace Work.Smooth.SphereJordan

open ThetaSetup

noncomputable section

/-- **The side determination.**  In the theta configuration there are two four-arc curves `J₁`,
`J₂` (containing the two joining arcs) whose bounded, respectively unbounded, sides avoid the theta
graph and whose sides tile the complement. -/
theorem thetaSideDetermination (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {D₁ D₂ : Set ℂ}
    (hD₁ : ∃ f : C(Work.Smooth.SphereJordan.Disc, ℂ), Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Work.Smooth.SphereJordan.Disc, ℂ), Function.Injective g ∧ Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, ℂ)) (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩)
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩) :
    ∃ (J₁ J₂ : Work.Smooth.Jordan.PlaneCurve)
      (S₁ : Work.Smooth.Jordan.PlaneSeparation J₁) (S₂ : Work.Smooth.Jordan.PlaneSeparation J₂),
      J₁.IsSimple ∧ J₂.IsSimple ∧
      Set.range J₁.γ ⊆ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β ∧
      Set.range J₂.γ ⊆ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β ∧
      Set.range α ⊆ J₁.trace ∧ Set.range β ⊆ J₁.trace ∧
      Set.range α ⊆ J₂.trace ∧ Set.range β ⊆ J₂.trace ∧
      (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) ∩ S₁.V = ∅ ∧
      (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) ∩ S₂.U = ∅ ∧
      Disjoint S₁.V S₂.U ∧
      S₁.V ∪ S₂.U = (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ := by
  obtain ⟨T, hTα, hTβ⟩ :=
    exists_thetaSetup h hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep
      hαβ₀ hαβ₁
  -- the Schoenflies discs of the two boundary curves of the theta graph
  obtain ⟨Sf⟩ := h (discCurve T.f) (discCurve_isSimple T.hf)
  obtain ⟨hfrange, hfopen⟩ := discCurveSpans T.hf Sf
  obtain ⟨Sg⟩ := h (discCurve T.g) (discCurve_isSimple T.hg)
  obtain ⟨hgrange, hgopen⟩ := discCurveSpans T.hg Sg
  have hfopen' : openImage T.f = Sf.V := hfopen
  have hfrange' : Set.range T.f = closure Sf.V := hfrange
  have hgopen' : openImage T.g = Sg.V := hgopen
  have hgrange' : Set.range T.g = closure Sg.V := hgrange
  -- the two interior points
  have hmem0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_zero]
    norm_num
  set z₀ : Disc := ⟨0, hmem0⟩ with hz₀def
  have hz₀norm : ‖(z₀ : ℂ)‖ < 1 := by
    rw [show (z₀ : ℂ) = 0 from rfl]
    norm_num
  set x₀ : ℂ := T.f z₀ with hx₀def
  set y₀ : ℂ := T.g z₀ with hy₀def
  have hx₀op : x₀ ∈ openImage T.f := ⟨z₀, hz₀norm, hx₀def.symm⟩
  have hy₀op : y₀ ∈ openImage T.g := ⟨z₀, hz₀norm, hy₀def.symm⟩
  have hx₀V : x₀ ∈ Sf.V := by rw [← hfopen']; exact hx₀op
  have hy₀V : y₀ ∈ Sg.V := by rw [← hgopen']; exact hy₀op
  have hx₀_odd : Odd (windNumber (discCurve T.f).γ (discCurve T.f).cont x₀) :=
    Work.SphereJordan.odd_windNumber_of_mem_V Sf hx₀V
  have hy₀_odd : Odd (windNumber (discCurve T.g).γ (discCurve T.g).cont y₀) :=
    Work.SphereJordan.odd_windNumber_of_mem_V Sg hy₀V
  -- the incidence facts
  have hx_trace : ∀ i j : Bool, x₀ ∉ (T.cur i j).trace := by
    intro i j
    rw [hx₀def]
    exact (center_notMem_cur_trace T z₀ hz₀norm i j).1
  have hy_trace : ∀ i j : Bool, y₀ ∉ (T.cur i j).trace := by
    intro i j
    rw [hy₀def]
    exact (center_notMem_cur_trace T z₀ hz₀norm i j).2
  have hxcirc_f : ∀ ψ : ℝ, T.f (circlePoint ψ) ≠ x₀ := by
    intro ψ
    rw [hx₀def]
    exact circlePoint_ne_of_norm_lt T hz₀norm ψ
  have hycirc_g : ∀ ψ : ℝ, T.g (circlePoint ψ) ≠ y₀ := by
    intro ψ
    rw [hy₀def]
    exact circlePoint_ne_of_norm_lt_g T hz₀norm ψ
  have hx₀D₁ : x₀ ∈ D₁ := by
    rw [hx₀def]
    have h1 : T.f z₀ ∈ Set.range T.f := ⟨z₀, rfl⟩
    rwa [T.hfr] at h1
  have hy₀D₂ : y₀ ∈ D₂ := by
    rw [hy₀def]
    have h1 : T.g z₀ ∈ Set.range T.g := ⟨z₀, rfl⟩
    rwa [T.hgr] at h1
  have hx₀_notD₂ : x₀ ∉ D₂ := fun hc => Set.disjoint_left.mp T.hdisj hx₀D₁ hc
  have hy₀_notD₁ : y₀ ∉ D₁ := fun hc => Set.disjoint_left.mp T.hdisj hc hy₀D₂
  have hycirc_f : ∀ ψ : ℝ, T.f (circlePoint ψ) ≠ y₀ := by
    intro ψ hcon
    have h1 : T.f (circlePoint ψ) ∈ D₁ := by
      have h2 : T.f (circlePoint ψ) ∈ Set.range T.f := ⟨circlePoint ψ, rfl⟩
      rwa [T.hfr] at h2
    exact Set.disjoint_left.mp T.hdisj h1 (by rw [hcon]; exact hy₀D₂)
  have hxcirc_g : ∀ ψ : ℝ, T.g (circlePoint ψ) ≠ x₀ := by
    intro ψ hcon
    have h1 : T.g (circlePoint ψ) ∈ D₂ := by
      have h2 : T.g (circlePoint ψ) ∈ Set.range T.g := ⟨circlePoint ψ, rfl⟩
      rwa [T.hgr] at h2
    exact Set.disjoint_left.mp T.hdisj (by rw [hcon]; exact hx₀D₁) h1
  have hWf_y : windNumber (discCurve T.f).γ (discCurve T.f).cont y₀ = 0 :=
    windNumber_discCurve_eq_zero h T.hf (fun hc => hy₀_notD₁ (by rwa [T.hfr] at hc))
  have hWg_x : windNumber (discCurve T.g).γ (discCurve T.g).cont x₀ = 0 :=
    windNumber_discCurve_eq_zero h T.hg (fun hc => hx₀_notD₂ (by rwa [T.hgr] at hc))
  -- the two indices
  obtain ⟨i₀, hi₀, hi₀uniq⟩ :=
    exists_zero_index_arcA T h false (hx_trace true false) (hx_trace false false) hxcirc_f hx₀_odd
  obtain ⟨j₀, hj₀, hj₀uniq⟩ :=
    exists_zero_index_arcB T h i₀ (hy_trace i₀ true) (hy_trace i₀ false) hycirc_g hy₀_odd
  have hJ₁s : (T.cur i₀ j₀).IsSimple := T.cur_isSimple i₀ j₀
  have hJ₂s : (T.cur (!i₀) (!j₀)).IsSimple := T.cur_isSimple (!i₀) (!j₀)
  obtain ⟨S₁⟩ := h (T.cur i₀ j₀) hJ₁s
  obtain ⟨S₂⟩ := h (T.cur (!i₀) (!j₀)) hJ₂s
  -- the winding numbers of the two curves
  have hJ₁x : windNumber (T.cur i₀ j₀).γ (T.cur i₀ j₀).cont x₀ = 0 := by
    rw [windNumber_cur_indep_j T i₀ j₀ (hx_trace i₀ true) (hx_trace i₀ false) hxcirc_g hWg_x]
    exact hi₀
  have hJ₁y : windNumber (T.cur i₀ j₀).γ (T.cur i₀ j₀).cont y₀ = 0 := hj₀
  have hne_swap_i : ¬ ((!i₀) = i₀) := by
    cases i₀ <;> simp
  have hne_swap_j : ¬ ((!j₀) = j₀) := by
    cases j₀ <;> simp
  have hJ₂x : windNumber (T.cur (!i₀) (!j₀)).γ (T.cur (!i₀) (!j₀)).cont x₀ ≠ 0 := by
    rw [windNumber_cur_indep_j T (!i₀) (!j₀) (hx_trace (!i₀) true) (hx_trace (!i₀) false)
      hxcirc_g hWg_x]
    intro h0
    exact absurd (hi₀uniq (!i₀) h0) hne_swap_i
  have hJ₂y : windNumber (T.cur (!i₀) (!j₀)).γ (T.cur (!i₀) (!j₀)).cont y₀ ≠ 0 := by
    have h1 : windNumber (T.cur i₀ (!j₀)).γ (T.cur i₀ (!j₀)).cont y₀ ≠ 0 := by
      intro h0
      exact absurd (hj₀uniq (!j₀) h0) hne_swap_j
    intro h0
    have h2 : windNumber (T.cur true (!j₀)).γ (T.cur true (!j₀)).cont y₀ = 0 := by
      rw [← windNumber_cur_indep_i T (!i₀) (!j₀) (hy_trace true (!j₀)) (hy_trace false (!j₀))
        hycirc_f hWf_y]
      exact h0
    exact h1 (by
      rw [windNumber_cur_indep_i T i₀ (!j₀) (hy_trace true (!j₀)) (hy_trace false (!j₀))
        hycirc_f hWf_y]
      exact h2)
  -- the open discs miss the traces of the two curves
  have hopen₁f : openImage T.f ⊆ (T.cur i₀ j₀).traceᶜ := by
    rintro u ⟨w, hw, rfl⟩
    exact f_notMem_cur_trace T w hw i₀ j₀
  have hopen₂f : openImage T.f ⊆ (T.cur (!i₀) (!j₀)).traceᶜ := by
    rintro u ⟨w, hw, rfl⟩
    exact f_notMem_cur_trace T w hw (!i₀) (!j₀)
  have hopen₁g : openImage T.g ⊆ (T.cur i₀ j₀).traceᶜ := by
    rintro u ⟨w, hw, rfl⟩
    exact g_notMem_cur_trace T w hw i₀ j₀
  have hopen₂g : openImage T.g ⊆ (T.cur (!i₀) (!j₀)).traceᶜ := by
    rintro u ⟨w, hw, rfl⟩
    exact g_notMem_cur_trace T w hw (!i₀) (!j₀)
  -- the sides of `S₁` contain the two discs
  have hxU₁ : x₀ ∈ S₁.U := by
    have hmem : x₀ ∈ S₁.U ∪ S₁.V := by rw [S₁.union_eq]; exact hx_trace i₀ j₀
    rcases hmem with h | h
    · exact h
    · exact absurd hJ₁x (windNumber_ne_zero_of_mem_V S₁ h)
  have hyU₁ : y₀ ∈ S₁.U := by
    have hmem : y₀ ∈ S₁.U ∪ S₁.V := by rw [S₁.union_eq]; exact hy_trace i₀ j₀
    rcases hmem with h | h
    · exact h
    · exact absurd hJ₁y (windNumber_ne_zero_of_mem_V S₁ h)
  have hopen_f_U₁ : openImage T.f ⊆ S₁.U := by
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S₁.toPlaneSeparation
      (openImage_preconnected T.f) hopen₁f with h | h
    · exact h
    · exact absurd (h hx₀op) (Set.disjoint_left.mp S₁.toPlaneSeparation.disjoint_UV hxU₁)
  have hopen_g_U₁ : openImage T.g ⊆ S₁.U := by
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S₁.toPlaneSeparation
      (openImage_preconnected T.g) hopen₁g with h | h
    · exact h
    · exact absurd (h hy₀op) (Set.disjoint_left.mp S₁.toPlaneSeparation.disjoint_UV hyU₁)
  have hclos₁ : closure (openImage T.f) = D₁ := by
    rw [hfopen', hfrange'.symm]
    exact T.hfr
  have hclos₂ : closure (openImage T.g) = D₂ := by
    rw [hgopen', hgrange'.symm]
    exact T.hgr
  have hV₁D₁ : S₁.V ∩ D₁ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huV, huD⟩
    have hucl : u ∈ closure (openImage T.f) := hclos₁.symm ▸ huD
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp S₁.toPlaneSeparation.isOpen_V u huV
    rw [Metric.mem_closure_iff] at hucl
    obtain ⟨v, hvop, hvd⟩ := hucl ε hε
    have hvball : v ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, dist_comm]
      exact hvd
    exact Set.disjoint_left.mp S₁.toPlaneSeparation.disjoint_UV (hopen_f_U₁ hvop) (hball hvball)
  have hV₁D₂ : S₁.V ∩ D₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huV, huD⟩
    have hucl : u ∈ closure (openImage T.g) := hclos₂.symm ▸ huD
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp S₁.toPlaneSeparation.isOpen_V u huV
    rw [Metric.mem_closure_iff] at hucl
    obtain ⟨v, hvop, hvd⟩ := hucl ε hε
    have hvball : v ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, dist_comm]
      exact hvd
    exact Set.disjoint_left.mp S₁.toPlaneSeparation.disjoint_UV (hopen_g_U₁ hvop) (hball hvball)
  have hA₁ : (D₁ ∪ D₂ ∪ Set.range T.α ∪ Set.range T.β) ∩ S₁.V = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huA, huV⟩
    have huVt : u ∉ (T.cur i₀ j₀).trace := by
      have hmem : u ∈ S₁.U ∪ S₁.V := Or.inr huV
      rwa [S₁.union_eq] at hmem
    rcases huA with ((h | h) | h) | h
    · exact (Set.eq_empty_iff_forall_notMem.mp hV₁D₁) u ⟨huV, h⟩
    · exact (Set.eq_empty_iff_forall_notMem.mp hV₁D₂) u ⟨huV, h⟩
    · exact huVt (T.range_α_subset_cur i₀ j₀ h)
    · exact huVt (T.range_β_subset_cur i₀ j₀ h)
  -- the sides of `S₂`
  have hxV₂ : x₀ ∈ S₂.V := by
    have hmem : x₀ ∈ S₂.U ∪ S₂.V := by rw [S₂.union_eq]; exact hx_trace (!i₀) (!j₀)
    rcases hmem with h | h
    · exact absurd (Work.Smooth.SphereJordan.windNumber_eq_zero_of_mem_U S₂.toPlaneSeparation h)
        hJ₂x
    · exact h
  have hyV₂ : y₀ ∈ S₂.V := by
    have hmem : y₀ ∈ S₂.U ∪ S₂.V := by rw [S₂.union_eq]; exact hy_trace (!i₀) (!j₀)
    rcases hmem with h | h
    · exact absurd (Work.Smooth.SphereJordan.windNumber_eq_zero_of_mem_U S₂.toPlaneSeparation h)
        hJ₂y
    · exact h
  have hopen_f_V₂ : openImage T.f ⊆ S₂.V := by
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S₂.toPlaneSeparation
      (openImage_preconnected T.f) hopen₂f with h | h
    · exact False.elim (Set.disjoint_left.mp S₂.toPlaneSeparation.disjoint_UV (h hx₀op) hxV₂)
    · exact h
  have hopen_g_V₂ : openImage T.g ⊆ S₂.V := by
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S₂.toPlaneSeparation
      (openImage_preconnected T.g) hopen₂g with h | h
    · exact False.elim (Set.disjoint_left.mp S₂.toPlaneSeparation.disjoint_UV (h hy₀op) hyV₂)
    · exact h
  have hU₂D₁ : S₂.U ∩ D₁ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huU, huD⟩
    have hucl : u ∈ closure (openImage T.f) := hclos₁.symm ▸ huD
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp S₂.toPlaneSeparation.isOpen_U u huU
    rw [Metric.mem_closure_iff] at hucl
    obtain ⟨v, hvop, hvd⟩ := hucl ε hε
    have hvball : v ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, dist_comm]
      exact hvd
    exact Set.disjoint_left.mp S₂.toPlaneSeparation.disjoint_UV (hball hvball) (hopen_f_V₂ hvop)
  have hU₂D₂ : S₂.U ∩ D₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huU, huD⟩
    have hucl : u ∈ closure (openImage T.g) := hclos₂.symm ▸ huD
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp S₂.toPlaneSeparation.isOpen_U u huU
    rw [Metric.mem_closure_iff] at hucl
    obtain ⟨v, hvop, hvd⟩ := hucl ε hε
    have hvball : v ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, dist_comm]
      exact hvd
    exact Set.disjoint_left.mp S₂.toPlaneSeparation.disjoint_UV (hball hvball) (hopen_g_V₂ hvop)
  have hA₂ : (D₁ ∪ D₂ ∪ Set.range T.α ∪ Set.range T.β) ∩ S₂.U = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huA, huU⟩
    have huUt : u ∉ (T.cur (!i₀) (!j₀)).trace := by
      have hmem : u ∈ S₂.U ∪ S₂.V := Or.inl huU
      rwa [S₂.union_eq] at hmem
    rcases huA with ((h | h) | h) | h
    · exact (Set.eq_empty_iff_forall_notMem.mp hU₂D₁) u ⟨huU, h⟩
    · exact (Set.eq_empty_iff_forall_notMem.mp hU₂D₂) u ⟨huU, h⟩
    · exact huUt (T.range_α_subset_cur (!i₀) (!j₀) h)
    · exact huUt (T.range_β_subset_cur (!i₀) (!j₀) h)
  -- outside the theta graph the two curves have the same winding number
  have hAgree : ∀ z : ℂ, z ∉ (D₁ ∪ D₂ ∪ Set.range T.α ∪ Set.range T.β) →
      windNumber (T.cur i₀ j₀).γ (T.cur i₀ j₀).cont z
        = windNumber (T.cur (!i₀) (!j₀)).γ (T.cur (!i₀) (!j₀)).cont z := by
    intro z hz
    have hzD₁ : z ∉ D₁ := fun h => hz (Or.inl (Or.inl (Or.inl h)))
    have hzD₂ : z ∉ D₂ := fun h => hz (Or.inl (Or.inl (Or.inr h)))
    have hzT₁ : z ∉ (T.cur i₀ j₀).trace := fun h => hz (T.cur_subset i₀ j₀ h)
    have hzT₂ : z ∉ (T.cur (!i₀) (!j₀)).trace := fun h => hz (T.cur_subset (!i₀) (!j₀) h)
    have hzt : ∀ i j : Bool, z ∉ (T.cur i j).trace := fun i j h => hz (T.cur_subset i j h)
    have hzf : windNumber (discCurve T.f).γ (discCurve T.f).cont z = 0 :=
      windNumber_discCurve_eq_zero h T.hf (fun hc => hzD₁ (by rwa [T.hfr] at hc))
    have hzg : windNumber (discCurve T.g).γ (discCurve T.g).cont z = 0 :=
      windNumber_discCurve_eq_zero h T.hg (fun hc => hzD₂ (by rwa [T.hgr] at hc))
    have hcirc_z_f : ∀ ψ : ℝ, T.f (circlePoint ψ) ≠ z := by
      intro ψ hcon
      exact hzD₁ (by
        have h3 : T.f (circlePoint ψ) ∈ Set.range T.f := ⟨circlePoint ψ, rfl⟩
        rw [T.hfr] at h3
        rwa [hcon] at h3)
    have hcirc_z_g : ∀ ψ : ℝ, T.g (circlePoint ψ) ≠ z := by
      intro ψ hcon
      exact hzD₂ (by
        have h3 : T.g (circlePoint ψ) ∈ Set.range T.g := ⟨circlePoint ψ, rfl⟩
        rw [T.hgr] at h3
        rwa [hcon] at h3)
    have e1 : windNumber (T.cur i₀ j₀).γ (T.cur i₀ j₀).cont z
        = windNumber (T.cur (!i₀) j₀).γ (T.cur (!i₀) j₀).cont z :=
      windNumber_cur_swap_i T i₀ j₀ (hzt true j₀) (hzt false j₀) hcirc_z_f hzf
    have e2 : windNumber (T.cur (!i₀) j₀).γ (T.cur (!i₀) j₀).cont z
        = windNumber (T.cur (!i₀) (!j₀)).γ (T.cur (!i₀) (!j₀)).cont z :=
      windNumber_cur_swap_j T (!i₀) j₀ (hzt (!i₀) true) (hzt (!i₀) false) hcirc_z_g hzg
    rw [e1, e2]
  have hcur₁ : Set.range (T.cur i₀ j₀).γ ⊆ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β := by
    rw [← hTα, ← hTβ]
    exact T.cur_subset i₀ j₀
  have hcur₂ : Set.range (T.cur (!i₀) (!j₀)).γ ⊆ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β := by
    rw [← hTα, ← hTβ]
    exact T.cur_subset (!i₀) (!j₀)
  have hα₁' : Set.range α ⊆ (T.cur i₀ j₀).trace := by
    rw [← hTα]
    exact T.range_α_subset_cur i₀ j₀
  have hβ₁' : Set.range β ⊆ (T.cur i₀ j₀).trace := by
    rw [← hTβ]
    exact T.range_β_subset_cur i₀ j₀
  have hα₂' : Set.range α ⊆ (T.cur (!i₀) (!j₀)).trace := by
    rw [← hTα]
    exact T.range_α_subset_cur (!i₀) (!j₀)
  have hβ₂' : Set.range β ⊆ (T.cur (!i₀) (!j₀)).trace := by
    rw [← hTβ]
    exact T.range_β_subset_cur (!i₀) (!j₀)
  have hA₁' : (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) ∩ S₁.V = ∅ := by
    rw [← hTα, ← hTβ]
    exact hA₁
  have hA₂' : (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) ∩ S₂.U = ∅ := by
    rw [← hTα, ← hTβ]
    exact hA₂
  refine ⟨T.cur i₀ j₀, T.cur (!i₀) (!j₀), S₁.toPlaneSeparation, S₂.toPlaneSeparation,
    hJ₁s, hJ₂s, hcur₁, hcur₂, hα₁', hβ₁', hα₂', hβ₂', hA₁', hA₂', ?_, ?_⟩
  · -- the two sides are disjoint
    rw [Set.disjoint_left]
    rintro u huV₁ huU₂
    have huA : u ∉ (D₁ ∪ D₂ ∪ Set.range T.α ∪ Set.range T.β) :=
      fun hA => (Set.eq_empty_iff_forall_notMem.mp hA₁) u ⟨hA, huV₁⟩
    have hW₁ : windNumber (T.cur i₀ j₀).γ (T.cur i₀ j₀).cont u ≠ 0 :=
      windNumber_ne_zero_of_mem_V S₁ huV₁
    have hW₂ : windNumber (T.cur (!i₀) (!j₀)).γ (T.cur (!i₀) (!j₀)).cont u = 0 :=
      Work.Smooth.SphereJordan.windNumber_eq_zero_of_mem_U S₂.toPlaneSeparation huU₂
    exact hW₁ (by rw [hAgree u huA]; exact hW₂)
  · -- the two sides exhaust the complement
    rw [← hTα, ← hTβ]
    refine Set.Subset.antisymm ?_ ?_
    · rintro u (huV₁ | huU₂)
      · exact fun hA => (Set.eq_empty_iff_forall_notMem.mp hA₁) u ⟨hA, huV₁⟩
      · exact fun hA => (Set.eq_empty_iff_forall_notMem.mp hA₂) u ⟨hA, huU₂⟩
    · intro u huA
      have huT₁ : u ∉ (T.cur i₀ j₀).trace := fun h => huA (T.cur_subset i₀ j₀ h)
      have huT₂ : u ∉ (T.cur (!i₀) (!j₀)).trace := fun h => huA (T.cur_subset (!i₀) (!j₀) h)
      by_cases hzero : windNumber (T.cur (!i₀) (!j₀)).γ (T.cur (!i₀) (!j₀)).cont u = 0
      · have hmem : u ∈ S₂.U ∪ S₂.V := by rw [S₂.union_eq]; exact huT₂
        rcases hmem with h | h
        · exact Or.inr h
        · exact absurd hzero (windNumber_ne_zero_of_mem_V S₂ h)
      · have hW₁ : windNumber (T.cur i₀ j₀).γ (T.cur i₀ j₀).cont u ≠ 0 := by
          rw [hAgree u huA]
          exact hzero
        have hmem : u ∈ S₁.U ∪ S₁.V := by rw [S₁.union_eq]; exact huT₁
        rcases hmem with h | h
        · exact absurd (Work.Smooth.SphereJordan.windNumber_eq_zero_of_mem_U
            S₁.toPlaneSeparation h) hW₁
        · exact Or.inl h


end

end Work.Smooth.SphereJordan
