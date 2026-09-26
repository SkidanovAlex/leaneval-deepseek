import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.planeArcComponentsCore
import Submission.Work.Smooth.SphereJordan.thetaPlaneJordanCurve
import Submission.Work.Smooth.SphereJordan.thetaFoundation
import Submission.Work.Smooth.SphereJordan.disc_complement_preconnected
import Submission.Work.Smooth.SphereJordan.twoComponentsAux
import Submission.Work.Smooth.SphereJordan.atMostTwo_components_of_embeddedCircle
import Submission.Work.Smooth.SphereJordan.thetaSpansAux
import Submission.Work.Smooth.SphereJordan.Transport
import Submission.Work.Smooth.SphereJordan.thetaComplementComponents
import Submission.Work.Smooth.SphereJordan.compl_range_disc_preconnected_plane
import Submission.Work.Smooth.SphereJordan.windNumber_eq_zero_or_odd_uncond
import Submission.Work.Smooth.SphereJordan.cruxClean

/-!
# The two complementary components of the theta graph

Two disjoint embedded discs `D₁`, `D₂` on the Riemann sphere joined by two disjoint arcs `α`, `β`
whose interiors avoid the discs: the complement of the union is the disjoint union of two non-empty
open preconnected sets.

Everything here is unconditional: the Jordan separation of the continuous simple closed plane curves
occurring in the argument is supplied by `Work.Smooth.SphereJordan.exists_jsep_clean` (the "at least two
components" half, from the winding number) and the "at most two components" half comes from the
winding-number side determination (`ThetaAtMostTwoUncond`).
-/

set_option maxHeartbeats 1000000

namespace Work.Smooth.SphereJordan

noncomputable section

open Set

open Work.Smooth.SphereJordan.ThetaSetup

/-! ## The complement of the plane theta graph is not preconnected -/

theorem thetaPlane_not_preconnected_uncond
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
    ¬ IsPreconnected ((D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ : Set ℂ) := by
  obtain ⟨f, hf, hfr⟩ := hD₁
  obtain ⟨g, hg, hgr⟩ := hD₂
  obtain ⟨K, hKsimple, hKsub, hKα, hKβ⟩ := thetaPlaneJordanCurve f hf hfr g hg hgr hdisj α β
    hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁
  obtain ⟨S⟩ := exists_jsep_clean K hKsimple
  set M : Set ℂ := D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β with hM
  have hMcomp : IsCompact M := by
    rw [hM, ← hfr, ← hgr]
    exact (((isCompact_range f.continuous).union (isCompact_range g.continuous)).union
      (isCompact_range α.continuous)).union (isCompact_range β.continuous)
  have htraceM : K.trace ⊆ M := by rw [hM]; exact hKsub
  have hVoff : S.V ⊆ K.traceᶜ := by
    rw [← S.union_eq]; exact Set.subset_union_right
  have htrace_closure : K.trace ⊆ closure S.V := by
    rw [← S.frontier_V]; exact frontier_subset_closure
  have hsplit : Mᶜ ⊆ S.V ∪ S.U := by
    intro z hz
    have hzK : z ∉ K.trace := fun hc => hz (htraceM hc)
    have hzUV : z ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hzK
    rcases hzUV with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'
  have hfar : (Mᶜ ∩ S.U).Nonempty := by
    obtain ⟨C, hC⟩ := (hMcomp.isBounded).exists_norm_le
    obtain ⟨z, hzU, hzC⟩ :=
      Work.Smooth.Jordan.plane_separation_unbounded (S.toPlaneSeparation hKsimple) (C + 1)
    exact ⟨z, fun hzM => absurd (hC z hzM) (by linarith), hzU⟩
  have hnear : (Mᶜ ∩ S.V).Nonempty := by
    by_contra hcon
    have hVM : S.V ⊆ M := by
      intro z hzV
      by_contra hzM
      exact hcon ⟨z, hzM, hzV⟩
    have hVD : S.V ⊆ D₁ ∪ D₂ := by
      intro z hzV
      have hzM := hVM hzV
      rw [hM] at hzM
      simp only [Set.mem_union] at hzM
      by_cases h1 : z ∈ D₁
      · exact Or.inl h1
      by_cases h2 : z ∈ D₂
      · exact Or.inr h2
      exfalso
      have hzK : z ∉ K.trace := hVoff hzV
      rcases hzM with ((h' | h') | h') | h'
      · exact h1 h'
      · exact h2 h'
      · exact hzK (hKα h')
      · exact hzK (hKβ h')
    have hD₁closed : IsClosed D₁ := by rw [← hfr]; exact (isCompact_range f.continuous).isClosed
    have hD₂closed : IsClosed D₂ := by rw [← hgr]; exact (isCompact_range g.continuous).isClosed
    have key₁ : S.V ⊆ D₁ → False := by
      intro hsub
      have hint : S.V ⊆ interior D₁ := by
        rw [← S.isOpen_V.interior_eq]
        exact interior_mono hsub
      have hclo : closure (interior D₁) = D₁ := by
        rw [← hfr]; exact closure_interior_range f hf
      have hmem : α ⟨1 / 2, by norm_num⟩ ∈ D₁ := by
        have h1 : α ⟨1 / 2, by norm_num⟩ ∈ closure S.V :=
          htrace_closure (hKα ⟨⟨1 / 2, by norm_num⟩, rfl⟩)
        rw [← hclo]
        exact closure_mono hint h1
      exact hαint ⟨1 / 2, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (Or.inl hmem)
    have key₂ : S.V ⊆ D₂ → False := by
      intro hsub
      have hint : S.V ⊆ interior D₂ := by
        rw [← S.isOpen_V.interior_eq]
        exact interior_mono hsub
      have hclo : closure (interior D₂) = D₂ := by
        rw [← hgr]; exact closure_interior_range g hg
      have hmem : α ⟨1 / 2, by norm_num⟩ ∈ D₂ := by
        have h1 : α ⟨1 / 2, by norm_num⟩ ∈ closure S.V :=
          htrace_closure (hKα ⟨⟨1 / 2, by norm_num⟩, rfl⟩)
        rw [← hclo]
        exact closure_mono hint h1
      exact hαint ⟨1 / 2, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (Or.inr hmem)
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp S.preconn_V) D₁ D₂ hD₁closed
      hD₂closed hVD (by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨-, hz₁, hz₂⟩
        exact Set.disjoint_left.mp hdisj hz₁ hz₂) with h' | h'
    · exact key₁ h'
    · exact key₂ h'
  intro hpre
  have hbad : (Mᶜ ∩ (S.V ∩ S.U)).Nonempty :=
    hpre (u := S.V) (v := S.U) S.isOpen_V S.isOpen_U hsplit hnear hfar
  obtain ⟨z, -, hzV, hzU⟩ := hbad
  exact (Set.disjoint_left.mp S.disjoint_UV hzU) hzV

/-! ## The unconditional `ThetaSetup` and the disc-curve Schoenflies datum -/

/-- **The four-arc configuration from the raw hypotheses of the theta graph**, unconditionally. -/
theorem exists_thetaSetup_uncond
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
    ∃ T : ThetaSetup D₁ D₂, T.α = α ∧ T.β = β := by
  obtain ⟨f, hf, hfr⟩ := hD₁
  obtain ⟨g, hg, hgr⟩ := hD₂
  obtain ⟨-, hβ₀fr, hα₁fr, hβ₁fr⟩ :=
    endpoints_mem_frontier ⟨f, hf, hfr⟩ ⟨g, hg, hgr⟩ α β hα₀ hα₁ hβ₀ hβ₁ hαint hβint
  have hα₀fr : α ⟨0, by norm_num⟩ ∈ frontier D₁ :=
    mem_frontier_of_mem_of_arc_avoid (isClosed_of_range_disc ⟨f, hf, hfr⟩) hα₀ rfl
      (fun t ht h => hαint t ht (Or.inl h))
  have hα₀fr' : α ⟨0, by norm_num⟩ ∈ frontier (Set.range f) := by rw [hfr]; exact hα₀fr
  have hβ₀fr' : β ⟨0, by norm_num⟩ ∈ frontier (Set.range f) := by rw [hfr]; exact hβ₀fr
  have hβ₁fr' : β ⟨1, by norm_num⟩ ∈ frontier (Set.range g) := by rw [hgr]; exact hβ₁fr
  have hα₁fr' : α ⟨1, by norm_num⟩ ∈ frontier (Set.range g) := by rw [hgr]; exact hα₁fr
  obtain ⟨θq, hθq⟩ := mem_trace_discCurve_of_mem_frontier (f := f) hf hβ₀fr'
  obtain ⟨φb, hφb⟩ := mem_trace_discCurve_of_mem_frontier (f := g) hg hβ₁fr'
  obtain ⟨θp, hθp_mem, hθp⟩ := exists_parameter_Ioo (w := θq) (p := α ⟨0, by norm_num⟩)
    (mem_trace_discCurve_of_mem_frontier (f := f) hf hα₀fr')
    (fun hcon => hαβ₀ (hcon.symm.trans hθq))
  obtain ⟨φa, hφa_mem, hφa⟩ := exists_parameter_Ioo (w := φb) (p := α ⟨1, by norm_num⟩)
    (mem_trace_discCurve_of_mem_frontier (f := g) hg hα₁fr')
    (fun hcon => hαβ₁ (hcon.symm.trans hφb))
  exact ⟨ThetaSetup.mk f hf hfr g hg hgr hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint
    hsep hαβ₀ hαβ₁ θq θp φa φb hθq hθp_mem.1 hθp_mem.2 hθp hφb hφa_mem.1 hφa_mem.2 hφa, rfl,
    rfl⟩

/-- **The Schoenflies datum of the boundary curve of an embedded disc**, with the inside side
`openImage f` and the outside side `(range f)ᶜ`. -/
def discCurveSchoenflies (f : C(Work.Smooth.SphereJordan.Disc, ℂ))
    (hf : Function.Injective f) : Work.Smooth.Jordan.PlaneSchoenflies (discCurve f) where
  simple := discCurve_isSimple hf
  U := (Set.range f)ᶜ
  V := openImage f
  isOpen_U := (isCompact_range f.continuous).isClosed.isOpen_compl
  isOpen_V := openImage_isOpen hf
  preconn_U := compl_range_disc_preconnected_plane hf
  preconn_V := openImage_preconnected f
  nonempty_U := by
    obtain ⟨R, hR⟩ := (isCompact_range f.continuous).isBounded.exists_norm_le
    have hR0 : 0 ≤ R := le_trans (norm_nonneg (f 0)) (hR (f 0) ⟨0, rfl⟩)
    refine ⟨((R + 1 : ℝ) : ℂ), ?_⟩
    rintro ⟨z, hz⟩
    have h1 : ‖f z‖ ≤ R := hR (f z) ⟨z, rfl⟩
    have h2 : ‖(((R + 1 : ℝ)) : ℂ)‖ = R + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have h3 : ‖f z‖ = R + 1 := by rw [hz, h2]
    linarith
  nonempty_V := ⟨f 0, 0, by simp, rfl⟩
  disjoint_UV := by
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy1, hy2⟩
    rcases hy2 with ⟨z, hz, rfl⟩
    exact hy1 ⟨z, rfl⟩
  union_eq := by
    have h1 : (discCurve f).trace = circleImage f := by
      rw [circleImage_eq_range_circlePoint]
      congr 1
    rw [h1, compl_circleImage_eq_openImage_union_compl hf, Set.union_comm]
  bounded_V := (isCompact_range f.continuous).isBounded.subset
    (by rintro y ⟨z, hz, rfl⟩; exact ⟨z, rfl⟩)
  e := f
  inj := hf
  boundary := fun _ => rfl
  range_e := (closure_openImage f).symm

/-- **A point outside the image of a disc map is wound zero times round by its boundary curve.** -/
theorem windNumber_discCurve_eq_zero_uncond {F : C(Work.Smooth.SphereJordan.Disc, ℂ)}
    (hF : Function.Injective F) {z : ℂ} (hz : z ∉ Set.range F) :
    windNumber (discCurve F).γ (discCurve F).cont z = 0 :=
  windNumber_eq_zero_of_mem_U (discCurveSchoenflies F hF).toPlaneSeparation
    (p := z) (by rw [discCurveSchoenflies]; exact hz)

/-- **Exactly one of the two curves `cur true j`, `cur false j` winds zero times about a point of
the interior of `D₁`.** -/
theorem exists_zero_index_arcA_uncond {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂) (j : Bool) {x : ℂ}
    (hx1 : x ∉ (T.cur true j).trace) (hx2 : x ∉ (T.cur false j).trace)
    (hxcirc : ∀ ψ : ℝ, T.f (circlePoint ψ) ≠ x)
    (hW : Odd (windNumber (discCurve T.f).γ (discCurve T.f).cont x)) :
    ∃ i : Bool, windNumber (T.cur i j).γ (T.cur i j).cont x = 0 ∧
      ∀ i' : Bool, windNumber (T.cur i' j).γ (T.cur i' j).cont x = 0 → i' = i := by
  have h1 := windNumber_eq_zero_or_odd_uncond (T.cur true j).cont (T.cur true j).periodic
    (T.cur_isSimple true j) (fun t ht => hx1 ⟨t, ht⟩)
  have h2 := windNumber_eq_zero_or_odd_uncond (T.cur false j).cont (T.cur false j).periodic
    (T.cur_isSimple false j) (fun t ht => hx2 ⟨t, ht⟩)
  have hd := windNumber_cur_arcA_diff T j hx1 hx2 hxcirc
  have hne : windNumber (discCurve T.f).γ (discCurve T.f).cont x ≠ 0 := by
    obtain ⟨m, hm⟩ := hW
    rw [hm]
    omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · have hzero : windNumber (discCurve T.f).γ (discCurve T.f).cont x = 0 := by
      rw [h1, h2, sub_zero] at hd
      exact hd.symm
    exact absurd hzero hne
  · refine ⟨true, h1, fun i' hi' => ?_⟩
    cases i' with
    | true => rfl
    | false =>
      obtain ⟨m, hm⟩ := h2
      rw [hi'] at hm
      omega
  · refine ⟨false, h2, fun i' hi' => ?_⟩
    cases i' with
    | true =>
      obtain ⟨m, hm⟩ := h1
      rw [hi'] at hm
      omega
    | false => rfl
  · exfalso
    obtain ⟨m, hm⟩ := h1
    obtain ⟨k, hk⟩ := h2
    obtain ⟨l, hl⟩ := hW
    rw [hm, hk, hl] at hd
    omega

/-- **Exactly one of the two curves `cur i true`, `cur i false` winds zero times about a point of
the interior of `D₂`.** -/
theorem exists_zero_index_arcB_uncond {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂) (i : Bool) {y : ℂ}
    (hy1 : y ∉ (T.cur i true).trace) (hy2 : y ∉ (T.cur i false).trace)
    (hycirc : ∀ ψ : ℝ, T.g (circlePoint ψ) ≠ y)
    (hW : Odd (windNumber (discCurve T.g).γ (discCurve T.g).cont y)) :
    ∃ j : Bool, windNumber (T.cur i j).γ (T.cur i j).cont y = 0 ∧
      ∀ j' : Bool, windNumber (T.cur i j').γ (T.cur i j').cont y = 0 → j' = j := by
  have h1 := windNumber_eq_zero_or_odd_uncond (T.cur i true).cont (T.cur i true).periodic
    (T.cur_isSimple i true) (fun t ht => hy1 ⟨t, ht⟩)
  have h2 := windNumber_eq_zero_or_odd_uncond (T.cur i false).cont (T.cur i false).periodic
    (T.cur_isSimple i false) (fun t ht => hy2 ⟨t, ht⟩)
  have hd := windNumber_cur_arcB_diff T i hy1 hy2 hycirc
  have hne : windNumber (discCurve T.g).γ (discCurve T.g).cont y ≠ 0 := by
    obtain ⟨m, hm⟩ := hW
    rw [hm]
    omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · have hzero : windNumber (discCurve T.g).γ (discCurve T.g).cont y = 0 := by
      rw [h1, h2, sub_zero] at hd
      exact hd.symm
    exact absurd hzero hne
  · refine ⟨true, h1, fun j' hj' => ?_⟩
    cases j' with
    | true => rfl
    | false =>
      obtain ⟨m, hm⟩ := h2
      rw [hj'] at hm
      omega
  · refine ⟨false, h2, fun j' hj' => ?_⟩
    cases j' with
    | true =>
      obtain ⟨m, hm⟩ := h1
      rw [hj'] at hm
      omega
    | false => rfl
  · exfalso
    obtain ⟨m, hm⟩ := h1
    obtain ⟨k, hk⟩ := h2
    obtain ⟨l, hl⟩ := hW
    rw [hm, hk, hl] at hd
    omega

/-! ## The two-component statements, as `Prop`s -/

/-- **The at-most-two-components statement for the plane theta graph**: of any three points off
`D₁ ∪ D₂ ∪ range α ∪ range β`, two lie in the same connected component of the complement. -/
def ThetaAtMostTwoUncond : Prop :=
  ∀ {D₁ D₂ : Set ℂ}
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
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩),
    ∀ x y z : ℂ, x ∉ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β →
      y ∉ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β →
      z ∉ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β →
      connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ x =
        connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ y ∨
      connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ x =
        connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ z ∨
      connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ y =
        connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ z

/-- **The plane theta graph has exactly two complementary components** (from the at-most-two
input). -/
theorem thetaPlane_twoComponents_of (h2 : ThetaAtMostTwoUncond)
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
    ∃ P₁ P₂ : Set ℂ, P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂ := by
  have h2' := h2 hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁
  obtain ⟨f, hf, hD₁'⟩ := hD₁
  obtain ⟨g, hg, hD₂'⟩ := hD₂
  set Y : Set ℂ := (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ with hY
  have hYclosed : IsClosed (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) := by
    rw [← hD₁', ← hD₂']
    exact (((isCompact_range f.continuous).union (isCompact_range g.continuous)).union
      (isCompact_range α.continuous)).union (isCompact_range β.continuous) |>.isClosed
  have hYopen : IsOpen Y := by rw [hY]; exact hYclosed.isOpen_compl
  have hYnotpre : ¬ IsPreconnected Y := by
    rw [hY]
    exact thetaPlane_not_preconnected_uncond ⟨f, hf, hD₁'⟩ ⟨g, hg, hD₂'⟩ hdisj α β hαinj hβinj
      hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁
  have hex : ∃ y ∈ Y, connectedComponentIn Y y ≠ Y := by
    by_contra hc
    apply hYnotpre
    rw [Work.Smooth.JordanSeparation.isPreconnected_iff_connectedComponentIn_eq]
    intro z hz
    by_contra hne
    exact hc ⟨z, hz, hne⟩
  obtain ⟨y, hyY, hyne⟩ := hex
  obtain ⟨z, hzY, hzy⟩ : ∃ z ∈ Y, z ∉ connectedComponentIn Y y := by
    by_contra hc
    apply hyne
    refine Set.Subset.antisymm (connectedComponentIn_subset Y y) ?_
    intro w hw
    by_contra hw'
    exact hc ⟨w, hw, hw'⟩
  refine ⟨connectedComponentIn Y y, connectedComponentIn Y z, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨y, mem_connectedComponentIn hyY⟩
  · exact ⟨z, mem_connectedComponentIn hzY⟩
  · exact isOpen_connectedComponentIn_of_isOpen' hYopen y
  · exact isOpen_connectedComponentIn_of_isOpen' hYopen z
  · rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    rintro w ⟨hwy, hwz⟩
    have h1 : connectedComponentIn Y y = connectedComponentIn Y w :=
      connectedComponentIn_eq (x := y) (y := w) hwy
    have h2w : connectedComponentIn Y z = connectedComponentIn Y w :=
      connectedComponentIn_eq (x := z) (y := w) hwz
    have h3 : connectedComponentIn Y z = connectedComponentIn Y y := by rw [h2w, h1]
    exact hzy (h3 ▸ mem_connectedComponentIn hzY)
  · ext w
    constructor
    · rintro (hw | hw)
      · exact connectedComponentIn_subset Y y hw
      · exact connectedComponentIn_subset Y z hw
    · intro hw
      have hw' : w ∉ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β := by
        rw [hY] at hw; exact hw
      have hy' : y ∉ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β := by
        rw [hY] at hyY; exact hyY
      have hz' : z ∉ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β := by
        rw [hY] at hzY; exact hzY
      have hkey := h2' w y z hw' hy' hz'
      rcases hkey with h1 | h1 | h1
      · exact Or.inl (h1 ▸ mem_connectedComponentIn hw)
      · exact Or.inr (h1 ▸ mem_connectedComponentIn hw)
      · exact absurd (h1.symm ▸ mem_connectedComponentIn hzY) hzy
  · exact isPreconnected_connectedComponentIn
  · exact isPreconnected_connectedComponentIn

/-- **The plane theta graph has exactly two complementary components**: the unconditional form of
`Work.Smooth.SphereJordan.PlaneThetaTwoComponents`. -/
def PlaneThetaTwoComponentsUncond : Prop :=
  ∀ {D₁ D₂ : Set ℂ}
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
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩),
    ∃ P₁ P₂ : Set ℂ, P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂

/-! ## From the plane to the sphere -/

theorem sphereThetaComponentsOfPlane (hplane : PlaneThetaTwoComponentsUncond)
    {D₁ D₂ : Set RiemannSphere}
    (hD₁ : ∃ f : C(Disc, RiemannSphere), Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Disc, RiemannSphere), Function.Injective g ∧ Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, RiemannSphere))
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩)
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩) :
    ∃ P₁ P₂ : Set RiemannSphere,
      P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = Set.univ \ (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂ := by
  classical
  obtain ⟨p, hp⟩ := exists_notMem_theta hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁
    hαint hβint hsep hαβ₀ hαβ₁
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph_infty_eq p
  set Ψ : RiemannSphere ≃ₜ RiemannSphere := Φ.symm with hΨdef
  have hΨp : Ψ p = infty := by
    rw [hΨdef, ← hΦ]
    exact Φ.symm_apply_apply infty
  obtain ⟨f₁, hf₁inj, hf₁range⟩ := hD₁
  obtain ⟨f₂, hf₂inj, hf₂range⟩ := hD₂
  set X : Set RiemannSphere := D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β with hXdef
  have hpX : p ∉ X := hp
  have hInfX : (infty : RiemannSphere) ∉ Ψ '' X := by
    rintro ⟨y, hy, hyinf⟩
    have hyp : y = p := Ψ.injective (hyinf.trans hΨp.symm)
    exact hpX (hyp ▸ hy)
  have hne : ∀ y : RiemannSphere, y ∈ X → Ψ y ≠ infty := by
    intro y hy hcon
    exact hInfX ⟨y, hy, hcon⟩
  obtain ⟨F₁, hF₁coe₀, hF₁inj_of⟩ := exists_lift_of_avoids_infty
    ⟨fun u => Ψ (f₁ u), Ψ.continuous.comp f₁.continuous⟩
    (fun u => hne (f₁ u) (by rw [hXdef, ← hf₁range]; exact Or.inl (Or.inl (Or.inl ⟨u, rfl⟩))))
  have hF₁coe : ∀ u : Disc, ((F₁ u : ℂ) : RiemannSphere) = Ψ (f₁ u) := fun u => hF₁coe₀ u
  obtain ⟨F₂, hF₂coe₀, hF₂inj_of⟩ := exists_lift_of_avoids_infty
    ⟨fun u => Ψ (f₂ u), Ψ.continuous.comp f₂.continuous⟩
    (fun u => hne (f₂ u) (by rw [hXdef, ← hf₂range]; exact Or.inl (Or.inl (Or.inr ⟨u, rfl⟩))))
  have hF₂coe : ∀ u : Disc, ((F₂ u : ℂ) : RiemannSphere) = Ψ (f₂ u) := fun u => hF₂coe₀ u
  obtain ⟨A, hAcoe₀, hAinj_of⟩ := exists_lift_of_avoids_infty
    ⟨fun t => Ψ (α t), Ψ.continuous.comp α.continuous⟩
    (fun t => hne (α t) (by rw [hXdef]; exact Or.inl (Or.inr ⟨t, rfl⟩)))
  have hAcoe : ∀ t : Set.Icc (0 : ℝ) 1, ((A t : ℂ) : RiemannSphere) = Ψ (α t) :=
    fun t => hAcoe₀ t
  obtain ⟨B, hBcoe₀, hBinj_of⟩ := exists_lift_of_avoids_infty
    ⟨fun t => Ψ (β t), Ψ.continuous.comp β.continuous⟩
    (fun t => hne (β t) (by rw [hXdef]; exact Or.inr ⟨t, rfl⟩))
  have hBcoe : ∀ t : Set.Icc (0 : ℝ) 1, ((B t : ℂ) : RiemannSphere) = Ψ (β t) :=
    fun t => hBcoe₀ t
  have hF₁inj : Function.Injective F₁ := hF₁inj_of (Ψ.injective.comp hf₁inj)
  have hF₂inj : Function.Injective F₂ := hF₂inj_of (Ψ.injective.comp hf₂inj)
  have hAinj : Function.Injective A := hAinj_of (Ψ.injective.comp hαinj)
  have hBinj : Function.Injective B := hBinj_of (Ψ.injective.comp hβinj)
  set d₁ : Set ℂ := Set.range F₁ with hd₁def
  set d₂ : Set ℂ := Set.range F₂ with hd₂def
  have hd₁coe : (↑) '' d₁ = Ψ '' D₁ := by
    rw [hd₁def, ← hf₁range]
    ext x; constructor
    · rintro ⟨z, ⟨u, rfl⟩, rfl⟩
      exact ⟨f₁ u, ⟨u, rfl⟩, (hF₁coe u).symm⟩
    · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
      exact ⟨F₁ u, ⟨u, rfl⟩, hF₁coe u⟩
  have hd₂coe : (↑) '' d₂ = Ψ '' D₂ := by
    rw [hd₂def, ← hf₂range]
    ext x; constructor
    · rintro ⟨z, ⟨u, rfl⟩, rfl⟩
      exact ⟨f₂ u, ⟨u, rfl⟩, (hF₂coe u).symm⟩
    · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
      exact ⟨F₂ u, ⟨u, rfl⟩, hF₂coe u⟩
  have hd₁d₂ : Disjoint d₁ d₂ := by
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    have h1 : (↑z : RiemannSphere) ∈ Ψ '' D₁ := by rw [← hd₁coe]; exact ⟨z, hz₁, rfl⟩
    have h2 : (↑z : RiemannSphere) ∈ Ψ '' D₂ := by rw [← hd₂coe]; exact ⟨z, hz₂, rfl⟩
    obtain ⟨y₁, hy₁, hy₁z⟩ := h1
    obtain ⟨y₂, hy₂, hy₂z⟩ := h2
    exact (Set.disjoint_left.mp hdisj hy₁) (Ψ.injective (hy₁z.trans hy₂z.symm) ▸ hy₂)
  have hA₀ : A ⟨0, by norm_num⟩ ∈ d₁ := by
    obtain ⟨u, hu⟩ := (show α ⟨0, by norm_num⟩ ∈ Set.range f₁ by rw [hf₁range]; exact hα₀)
    exact ⟨u, OnePoint.coe_injective (by rw [hF₁coe u, hAcoe ⟨0, by norm_num⟩, hu])⟩
  have hA₁ : A ⟨1, by norm_num⟩ ∈ d₂ := by
    obtain ⟨u, hu⟩ := (show α ⟨1, by norm_num⟩ ∈ Set.range f₂ by rw [hf₂range]; exact hα₁)
    exact ⟨u, OnePoint.coe_injective (by rw [hF₂coe u, hAcoe ⟨1, by norm_num⟩, hu])⟩
  have hB₀ : B ⟨0, by norm_num⟩ ∈ d₁ := by
    obtain ⟨u, hu⟩ := (show β ⟨0, by norm_num⟩ ∈ Set.range f₁ by rw [hf₁range]; exact hβ₀)
    exact ⟨u, OnePoint.coe_injective (by rw [hF₁coe u, hBcoe ⟨0, by norm_num⟩, hu])⟩
  have hB₁ : B ⟨1, by norm_num⟩ ∈ d₂ := by
    obtain ⟨u, hu⟩ := (show β ⟨1, by norm_num⟩ ∈ Set.range f₂ by rw [hf₂range]; exact hβ₁)
    exact ⟨u, OnePoint.coe_injective (by rw [hF₂coe u, hBcoe ⟨1, by norm_num⟩, hu])⟩
  have hAint : ∀ t : Set.Icc (0:ℝ) 1, (t:ℝ) ∈ Set.Ioo 0 1 → A t ∉ d₁ ∪ d₂ := by
    intro t ht hmem
    have hmem' : (↑(A t) : RiemannSphere) ∈ Ψ '' D₁ ∪ Ψ '' D₂ := by
      rcases hmem with h | h
      · exact Or.inl (by rw [← hd₁coe]; exact ⟨A t, h, rfl⟩)
      · exact Or.inr (by rw [← hd₂coe]; exact ⟨A t, h, rfl⟩)
    rw [hAcoe t] at hmem'
    rcases hmem' with ⟨y, hy, hyz⟩ | ⟨y, hy, hyz⟩
    · exact hαint t ht (Or.inl (Ψ.injective hyz ▸ hy))
    · exact hαint t ht (Or.inr (Ψ.injective hyz ▸ hy))
  have hBint : ∀ t : Set.Icc (0:ℝ) 1, (t:ℝ) ∈ Set.Ioo 0 1 → B t ∉ d₁ ∪ d₂ := by
    intro t ht hmem
    have hmem' : (↑(B t) : RiemannSphere) ∈ Ψ '' D₁ ∪ Ψ '' D₂ := by
      rcases hmem with h | h
      · exact Or.inl (by rw [← hd₁coe]; exact ⟨B t, h, rfl⟩)
      · exact Or.inr (by rw [← hd₂coe]; exact ⟨B t, h, rfl⟩)
    rw [hBcoe t] at hmem'
    rcases hmem' with ⟨y, hy, hyz⟩ | ⟨y, hy, hyz⟩
    · exact hβint t ht (Or.inl (Ψ.injective hyz ▸ hy))
    · exact hβint t ht (Or.inr (Ψ.injective hyz ▸ hy))
  have hsep' : ∀ s t : Set.Icc (0:ℝ) 1, (s:ℝ) ∈ Set.Ioo 0 1 → (t:ℝ) ∈ Set.Ioo 0 1 →
      A s ≠ B t := by
    intro s t hs ht hcon
    exact hsep s t hs ht (Ψ.injective (by rw [← hAcoe s, ← hBcoe t, hcon]))
  have hAβ₀ : A ⟨0, by norm_num⟩ ≠ B ⟨0, by norm_num⟩ := by
    intro hcon
    exact hαβ₀ (Ψ.injective (by rw [← hAcoe ⟨0, by norm_num⟩, ← hBcoe ⟨0, by norm_num⟩, hcon]))
  have hAβ₁ : A ⟨1, by norm_num⟩ ≠ B ⟨1, by norm_num⟩ := by
    intro hcon
    exact hαβ₁ (Ψ.injective (by rw [← hAcoe ⟨1, by norm_num⟩, ← hBcoe ⟨1, by norm_num⟩, hcon]))
  obtain ⟨P₁', P₂', hP₁ne, hP₂ne, hP₁o, hP₂o, hPdisj, hPun, hP₁c, hP₂c⟩ :=
    hplane ⟨F₁, hF₁inj, hd₁def.symm⟩ ⟨F₂, hF₂inj, hd₂def.symm⟩ hd₁d₂ A B hAinj hBinj hA₀ hA₁
      hB₀ hB₁ hAint hBint hsep' hAβ₀ hAβ₁
  have hArcα : Set.range (fun t : Set.Icc (0 : ℝ) 1 => ((A t : ℂ) : RiemannSphere)) =
      Ψ '' Set.range α := by
    ext x; constructor
    · rintro ⟨t, rfl⟩; exact ⟨α t, ⟨t, rfl⟩, (hAcoe t).symm⟩
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩; exact ⟨t, hAcoe t⟩
  have hArcβ : Set.range (fun t : Set.Icc (0 : ℝ) 1 => ((B t : ℂ) : RiemannSphere)) =
      Ψ '' Set.range β := by
    ext x; constructor
    · rintro ⟨t, rfl⟩; exact ⟨β t, ⟨t, rfl⟩, (hBcoe t).symm⟩
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩; exact ⟨t, hBcoe t⟩
  have hO : ((↑) '' d₁ ∪ (↑) '' d₂ ∪
        Set.range (fun t : Set.Icc (0 : ℝ) 1 => ((A t : ℂ) : RiemannSphere)) ∪
        Set.range (fun t : Set.Icc (0 : ℝ) 1 => ((B t : ℂ) : RiemannSphere))) = Ψ '' X := by
    rw [hd₁coe, hd₂coe, hArcα, hArcβ, hXdef, ← Set.image_union, ← Set.image_union,
      ← Set.image_union]
  have hO' : (↑) '' (d₁ ∪ d₂ ∪ Set.range A ∪ Set.range B) = Ψ '' X := by
    rw [Set.image_union, Set.image_union, Set.image_union]
    rw [← Set.range_comp ((↑) : ℂ → RiemannSphere) A,
        ← Set.range_comp ((↑) : ℂ → RiemannSphere) B]
    exact hO
  have hPun' : P₁' ∪ P₂' = (↑) ⁻¹' (Ψ '' X)ᶜ := by
    rw [hPun, ← hO']
    ext z
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_image, Set.mem_union, Set.mem_range]
    constructor
    · intro hz ⟨a, has, haz⟩
      exact hz (OnePoint.coe_injective haz ▸ has)
    · intro hz hmem
      exact hz ⟨z, hmem, rfl⟩
  have hInfXc : (infty : RiemannSphere) ∈ (Ψ '' X)ᶜ := hInfX
  have hran : Set.range ((↑) : ℂ → RiemannSphere) = ({infty} : Set RiemannSphere)ᶜ := by
    rw [← OnePoint.compl_range_coe, compl_compl]
  have hX'compl : (↑) '' (P₁' ∪ P₂') ∪ {infty} = (Ψ '' X)ᶜ := by
    have h1 : (↑) '' (P₁' ∪ P₂') = (Ψ '' X)ᶜ \ {infty} := by
      rw [hPun', Set.image_preimage_eq_inter_range, hran, Set.sdiff_eq]
    rw [h1]
    ext x; constructor
    · rintro (⟨hx, -⟩ | rfl)
      · exact hx
      · exact hInfXc
    · intro hx
      by_cases h : x = infty
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
  have hXcompact : IsCompact X := by
    rw [hXdef, ← hf₁range, ← hf₂range]
    exact (((isCompact_range f₁.continuous).union (isCompact_range f₂.continuous)).union
      (isCompact_range α.continuous)).union (isCompact_range β.continuous)
  have hX'compact : IsCompact (Ψ '' X) := hXcompact.image Ψ.continuous
  have hX'open : IsOpen ((Ψ '' X)ᶜ) := hX'compact.isClosed.isOpen_compl
  have hcpt : IsCompact (((↑) ⁻¹' (Ψ '' X)ᶜ)ᶜ : Set ℂ) :=
    ((OnePoint.isOpen_iff_of_mem' hInfXc).mp hX'open).1
  obtain ⟨R, hR⟩ := hcpt.isBounded.exists_norm_le
  set R₀ : ℝ := max R 0 with hR₀def
  have hR₀pos : 0 < R₀ + 1 := by rw [hR₀def]; positivity
  have hfar_sub : ∀ z : ℂ, R₀ + 1 < ‖z‖ → z ∈ P₁' ∪ P₂' := by
    intro z hz
    rw [hPun']
    intro hmem
    have h1 : ‖z‖ ≤ R := hR z (fun hcon => hcon hmem)
    have h2 : R ≤ R₀ := by rw [hR₀def]; exact le_max_left R 0
    linarith
  have hXfin : (↑) '' (P₁' ∪ P₂') ∪ {infty} = (Φ.symm '' X)ᶜ := by
    rw [← hΨdef]; exact hX'compl
  have hXfin' : (↑) '' (P₂' ∪ P₁') ∪ {infty} = (Φ.symm '' X)ᶜ := by
    rw [Set.union_comm P₂' P₁']; exact hXfin
  rcases (isPreconnected_far' hR₀pos).subset_or_subset hP₁o hP₂o hPdisj hfar_sub with
    hfar₁ | hfar₂
  · obtain ⟨Q₁, Q₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      sphereTwoPiecesOfPlanePair Φ hP₁o hP₂o hPdisj hP₁c hP₂c hP₂ne hXfin hfar₁
    refine ⟨Q₁, Q₂, h1, h2, h3, h4, h5, ?_, h7, h8⟩
    exact h6.trans (congrArg (fun s => Set.univ \ s) hXdef)
  · obtain ⟨Q₁, Q₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      sphereTwoPiecesOfPlanePair Φ hP₂o hP₁o hPdisj.symm hP₂c hP₁c hP₁ne hXfin' hfar₂
    refine ⟨Q₁, Q₂, h1, h2, h3, h4, h5, ?_, h7, h8⟩
    exact h6.trans (congrArg (fun s => Set.univ \ s) hXdef)

theorem thetaSideDetermination_uncond
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
    ∃ P Q : Set ℂ, IsPreconnected P ∧ IsPreconnected Q ∧
      P ⊆ (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ ∧
      Q ⊆ (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ ∧
      (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ ⊆ P ∪ Q := by
  obtain ⟨T, hTα, hTβ⟩ :=
    exists_thetaSetup_uncond hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep
      hαβ₀ hαβ₁
  -- the Schoenflies discs of the two boundary curves of the theta graph
  set Sf : Work.Smooth.Jordan.PlaneSchoenflies (discCurve T.f) :=
    discCurveSchoenflies T.f T.hf with hSfdef
  obtain ⟨hfrange, hfopen⟩ := discCurveSpans T.hf Sf
  set Sg : Work.Smooth.Jordan.PlaneSchoenflies (discCurve T.g) :=
    discCurveSchoenflies T.g T.hg with hSgdef
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
    windNumber_discCurve_eq_zero_uncond T.hf (fun hc => hy₀_notD₁ (by rwa [T.hfr] at hc))
  have hWg_x : windNumber (discCurve T.g).γ (discCurve T.g).cont x₀ = 0 :=
    windNumber_discCurve_eq_zero_uncond T.hg (fun hc => hx₀_notD₂ (by rwa [T.hgr] at hc))
  -- the two indices
  obtain ⟨i₀, hi₀, hi₀uniq⟩ :=
    exists_zero_index_arcA_uncond T false (hx_trace true false) (hx_trace false false) hxcirc_f hx₀_odd
  obtain ⟨j₀, hj₀, hj₀uniq⟩ :=
    exists_zero_index_arcB_uncond T i₀ (hy_trace i₀ true) (hy_trace i₀ false) hycirc_g hy₀_odd
  have hJ₁s : (T.cur i₀ j₀).IsSimple := T.cur_isSimple i₀ j₀
  have hJ₂s : (T.cur (!i₀) (!j₀)).IsSimple := T.cur_isSimple (!i₀) (!j₀)
  obtain ⟨S₁⟩ := exists_jsep_clean (T.cur i₀ j₀) hJ₁s
  obtain ⟨S₂⟩ := exists_jsep_clean (T.cur (!i₀) (!j₀)) hJ₂s
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
    · exact absurd hJ₁x (S₁.wind_ne_zero_of_mem_V h)
  have hyU₁ : y₀ ∈ S₁.U := by
    have hmem : y₀ ∈ S₁.U ∪ S₁.V := by rw [S₁.union_eq]; exact hy_trace i₀ j₀
    rcases hmem with h | h
    · exact h
    · exact absurd hJ₁y (S₁.wind_ne_zero_of_mem_V h)
  have hopen_f_U₁ : openImage T.f ⊆ S₁.U := by
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset (S₁.toPlaneSeparation hJ₁s)
      (openImage_preconnected T.f) hopen₁f with h | h
    · exact h
    · exact absurd (h hx₀op) (Set.disjoint_left.mp (S₁.toPlaneSeparation hJ₁s).disjoint_UV hxU₁)
  have hopen_g_U₁ : openImage T.g ⊆ S₁.U := by
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset (S₁.toPlaneSeparation hJ₁s)
      (openImage_preconnected T.g) hopen₁g with h | h
    · exact h
    · exact absurd (h hy₀op) (Set.disjoint_left.mp (S₁.toPlaneSeparation hJ₁s).disjoint_UV hyU₁)
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
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (S₁.toPlaneSeparation hJ₁s).isOpen_V u huV
    rw [Metric.mem_closure_iff] at hucl
    obtain ⟨v, hvop, hvd⟩ := hucl ε hε
    have hvball : v ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, dist_comm]
      exact hvd
    exact Set.disjoint_left.mp (S₁.toPlaneSeparation hJ₁s).disjoint_UV (hopen_f_U₁ hvop) (hball hvball)
  have hV₁D₂ : S₁.V ∩ D₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huV, huD⟩
    have hucl : u ∈ closure (openImage T.g) := hclos₂.symm ▸ huD
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (S₁.toPlaneSeparation hJ₁s).isOpen_V u huV
    rw [Metric.mem_closure_iff] at hucl
    obtain ⟨v, hvop, hvd⟩ := hucl ε hε
    have hvball : v ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, dist_comm]
      exact hvd
    exact Set.disjoint_left.mp (S₁.toPlaneSeparation hJ₁s).disjoint_UV (hopen_g_U₁ hvop) (hball hvball)
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
    · exact absurd (Work.Smooth.SphereJordan.windNumber_eq_zero_of_mem_U (S₂.toPlaneSeparation hJ₂s) h)
        hJ₂x
    · exact h
  have hyV₂ : y₀ ∈ S₂.V := by
    have hmem : y₀ ∈ S₂.U ∪ S₂.V := by rw [S₂.union_eq]; exact hy_trace (!i₀) (!j₀)
    rcases hmem with h | h
    · exact absurd (Work.Smooth.SphereJordan.windNumber_eq_zero_of_mem_U (S₂.toPlaneSeparation hJ₂s) h)
        hJ₂y
    · exact h
  have hopen_f_V₂ : openImage T.f ⊆ S₂.V := by
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset (S₂.toPlaneSeparation hJ₂s)
      (openImage_preconnected T.f) hopen₂f with h | h
    · exact False.elim (Set.disjoint_left.mp (S₂.toPlaneSeparation hJ₂s).disjoint_UV (h hx₀op) hxV₂)
    · exact h
  have hopen_g_V₂ : openImage T.g ⊆ S₂.V := by
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset (S₂.toPlaneSeparation hJ₂s)
      (openImage_preconnected T.g) hopen₂g with h | h
    · exact False.elim (Set.disjoint_left.mp (S₂.toPlaneSeparation hJ₂s).disjoint_UV (h hy₀op) hyV₂)
    · exact h
  have hU₂D₁ : S₂.U ∩ D₁ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huU, huD⟩
    have hucl : u ∈ closure (openImage T.f) := hclos₁.symm ▸ huD
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (S₂.toPlaneSeparation hJ₂s).isOpen_U u huU
    rw [Metric.mem_closure_iff] at hucl
    obtain ⟨v, hvop, hvd⟩ := hucl ε hε
    have hvball : v ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, dist_comm]
      exact hvd
    exact Set.disjoint_left.mp (S₂.toPlaneSeparation hJ₂s).disjoint_UV (hball hvball) (hopen_f_V₂ hvop)
  have hU₂D₂ : S₂.U ∩ D₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huU, huD⟩
    have hucl : u ∈ closure (openImage T.g) := hclos₂.symm ▸ huD
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (S₂.toPlaneSeparation hJ₂s).isOpen_U u huU
    rw [Metric.mem_closure_iff] at hucl
    obtain ⟨v, hvop, hvd⟩ := hucl ε hε
    have hvball : v ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, dist_comm]
      exact hvd
    exact Set.disjoint_left.mp (S₂.toPlaneSeparation hJ₂s).disjoint_UV (hball hvball) (hopen_g_V₂ hvop)
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
      windNumber_discCurve_eq_zero_uncond T.hf (fun hc => hzD₁ (by rwa [T.hfr] at hc))
    have hzg : windNumber (discCurve T.g).γ (discCurve T.g).cont z = 0 :=
      windNumber_discCurve_eq_zero_uncond T.hg (fun hc => hzD₂ (by rwa [T.hgr] at hc))
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
  refine ⟨S₁.V, S₂.U, S₁.preconn_V, S₂.preconn_U, ?_, ?_, ?_⟩
  · intro z hz hzM
    exact (Set.eq_empty_iff_forall_notMem.mp hA₁') z ⟨hzM, hz⟩
  · intro z hz hzM
    exact (Set.eq_empty_iff_forall_notMem.mp hA₂') z ⟨hzM, hz⟩
  · rw [← hTα, ← hTβ]
    intro u huA
    have huT₁ : u ∉ (T.cur i₀ j₀).trace := fun h => huA (T.cur_subset i₀ j₀ h)
    have huT₂ : u ∉ (T.cur (!i₀) (!j₀)).trace := fun h => huA (T.cur_subset (!i₀) (!j₀) h)
    by_cases hzero : windNumber (T.cur (!i₀) (!j₀)).γ (T.cur (!i₀) (!j₀)).cont u = 0
    · have hmem : u ∈ S₂.U ∪ S₂.V := by rw [S₂.union_eq]; exact huT₂
      rcases hmem with h | h
      · exact Or.inr h
      · exact absurd hzero (S₂.wind_ne_zero_of_mem_V h)
    · have hW₁ : windNumber (T.cur i₀ j₀).γ (T.cur i₀ j₀).cont u ≠ 0 := by
        rw [hAgree u huA]
        exact hzero
      have hmem : u ∈ S₁.U ∪ S₁.V := by rw [S₁.union_eq]; exact huT₁
      rcases hmem with h | h
      · exact absurd ((JSep.wind_zero_iff_U S₁ u huT₁).mpr h) hW₁
      · exact Or.inl h

/-! ## The at-most-two-components input -/

/-- **The at-most-two-components statement for the plane theta graph.** -/
theorem thetaAtMostTwoUncond : ThetaAtMostTwoUncond := by
  intro D₁ D₂ hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁
  obtain ⟨P, Q, hPpre, hQpre, hPsub, hQsub, hcov⟩ :=
    thetaSideDetermination_uncond hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint
      hsep hαβ₀ hαβ₁
  intro x y z hx hy hz
  exact atMostTwo_of_two_preconnected hPpre hQpre hPsub hQsub hcov hx hy hz

/-! ## The plane two-component theorem -/

theorem thetaPlaneTwoComponentsUncond : PlaneThetaTwoComponentsUncond :=
  fun {D₁ D₂} hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁ =>
    thetaPlane_twoComponents_of thetaAtMostTwoUncond hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁
      hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁

/-! ## The target -/

theorem thetaGraph_two_components
    {D₁ D₂ : Set Work.Smooth.SphereJordan.RiemannSphere}
    (hD₁ : ∃ f : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere),
      Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere),
      Function.Injective g ∧ Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, Work.Smooth.SphereJordan.RiemannSphere))
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 →
      α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 →
      β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩)
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩) :
    ∃ P₁ P₂ : Set Work.Smooth.SphereJordan.RiemannSphere,
      P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = Set.univ \ (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂ :=
  sphereThetaComponentsOfPlane thetaPlaneTwoComponentsUncond hD₁ hD₂ hdisj α β hαinj hβinj
    hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁

end

end Work.Smooth.SphereJordan
