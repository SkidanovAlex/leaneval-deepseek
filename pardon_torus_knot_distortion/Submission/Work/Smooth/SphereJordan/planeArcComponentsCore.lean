import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.DiscCurve
import Submission.Work.Smooth.SphereJordan.discCurveSpans
import Submission.Work.Smooth.SphereJordan.planeArcSetup
import Submission.Work.Smooth.SphereJordan.twoComponentsAux
import Submission.Work.Smooth.SphereJordan.thetaPlaneJordanCurve
import Submission.Work.Smooth.SphereJordan.DiscSpansAPI
import Submission.Work.Smooth.SphereJordan.openImage_isOpen
import Submission.Work.Smooth.SphereJordan.OpenImageAux
import Submission.Work.Smooth.SphereJordan.thetaPlaneAtMostTwo
import Submission.Work.Smooth.Jordan.plane_separation_unbounded
import Submission.Work.Smooth.JordanSeparation.ComplHelpers

namespace Work.Smooth.SphereJordan

noncomputable section

open Set

/-- **The closure of the interior of the range of an injective disc map is the range.** -/
theorem closure_interior_range (f : C(Disc, ℂ)) (hf : Function.Injective f) :
    closure (interior (Set.range f)) = Set.range f := by
  apply Subset.antisymm
  · exact closure_minimal interior_subset (isCompact_range f.continuous).isClosed
  · calc Set.range f = closure (openImage f) := (closure_openImage f).symm
      _ ⊆ closure (interior (Set.range f)) := closure_mono (by
            intro z hz
            exact interior_maximal (t := openImage f) (s := Set.range f)
              (by rintro w ⟨v, -, rfl⟩; exact ⟨v, rfl⟩) (openImage_isOpen hf) hz)

/-- **The theta graph is not preconnected.**

Two disjoint embedded discs joined by two disjoint arcs whose interiors avoid both discs: the
complement of the union is *not* preconnected.  This is the "at least two components" half of the
two-component statement.

Take a simple closed curve `K` inside the union whose trace contains both arcs
(`thetaPlaneJordanCurve`) with Schoenflies datum `S`.  The bounded side `S.V` avoids the union: if
it met `Dᵢ`, then (being open and `Dᵢ` being the closure of its interior) it would meet the
interior of `Dᵢ`, hence contain it by preconnectedness, hence — being open and so meeting the
boundary of `Dᵢ` — would contain points of that boundary, so by closedness the whole disc `Dᵢ`,
hence the trace of `K`, hence the arc, which leaves `Dᵢ` immediately.  Since `S.V` is bounded and
the union is compact, a point of the unbounded side `S.U` of large enough norm lies off the union.
Hence the complement of the union meets both sides of `K`, so it is not preconnected. -/
theorem thetaPlane_not_preconnected
    {D₁ D₂ : Set ℂ}
    (f : C(Disc, ℂ)) (hf : Function.Injective f) (hD₁ : Set.range f = D₁)
    (g : C(Disc, ℂ)) (hg : Function.Injective g) (hD₂ : Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, ℂ)) (hαinj : Function.Injective α)
    (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩)
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩)
    (h : PlaneHypothesis) :
    ¬ IsPreconnected ((D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ : Set ℂ) := by
  obtain ⟨K, hKsimple, hKsub, hKα, hKβ⟩ := thetaPlaneJordanCurve f hf hD₁ g hg hD₂ hdisj α β
    hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁
  obtain ⟨S⟩ := h K hKsimple
  set M : Set ℂ := D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β with hM
  have hMcomp : IsCompact M := by
    rw [hM, ← hD₁, ← hD₂]
    exact (((isCompact_range f.continuous).union (isCompact_range g.continuous)).union
      (isCompact_range α.continuous)).union (isCompact_range β.continuous)
  have htraceM : K.trace ⊆ M := by rw [hM]; exact hKsub
  have hVoff : S.V ⊆ K.traceᶜ := by rw [← S.union_eq]; exact Set.subset_union_right
  have htrace_closure : K.trace ⊆ closure S.V := by
    rintro x ⟨θ, rfl⟩
    rw [← S.boundary θ, ← S.range_e]
    exact ⟨circlePoint θ, rfl⟩
  have hsplit : Mᶜ ⊆ S.V ∪ S.U := by
    intro z hz
    have hzK : z ∉ K.trace := fun hc => hz (htraceM hc)
    have hzUV : z ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hzK
    rcases hzUV with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'
  -- a point of the complement of `M` in the unbounded side
  have hfar : (Mᶜ ∩ S.U).Nonempty := by
    obtain ⟨C, hC⟩ := (hMcomp.isBounded).exists_norm_le
    obtain ⟨z, hzU, hzC⟩ :=
      Work.Smooth.Jordan.plane_separation_unbounded S.toPlaneSeparation (C + 1)
    exact ⟨z, fun hzM => absurd (hC z hzM) (by linarith), hzU⟩
  -- a point of the complement of `M` in the bounded side
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
    have hD₁closed : IsClosed D₁ := by rw [← hD₁]; exact (isCompact_range f.continuous).isClosed
    have hD₂closed : IsClosed D₂ := by rw [← hD₂]; exact (isCompact_range g.continuous).isClosed
    have key₁ : S.V ⊆ D₁ → False := by
      intro hsub
      have hint : S.V ⊆ interior D₁ := by
        rw [← S.isOpen_V.interior_eq]
        exact interior_mono hsub
      have hclo : closure (interior D₁) = D₁ := by
        rw [← hD₁]
        exact closure_interior_range f hf
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
        rw [← hD₂]
        exact closure_interior_range g hg
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


/-- **A component of an open subset of `ℂ` is open.** -/
theorem isOpen_connectedComponentIn_of_isOpen' {F : Set ℂ} (hF : IsOpen F) (x : ℂ) :
    IsOpen (connectedComponentIn F x) := by
  rcases eq_or_ne (connectedComponentIn F x) ∅ with h | _
  · rw [h]; exact isOpen_empty
  · rw [isOpen_iff_mem_nhds]
    intro y hy
    have hyF : y ∈ F := connectedComponentIn_subset F x hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hF y hyF
    have hsub : Metric.ball y ε ⊆ connectedComponentIn F y :=
      Metric.isPreconnected_ball.subset_connectedComponentIn (Metric.mem_ball_self hε) hball
    have hyx : connectedComponentIn F y = connectedComponentIn F x :=
      (connectedComponentIn_eq hy).symm
    rw [← hyx]
    exact Filter.mem_of_superset (Metric.ball_mem_nhds y hε) hsub

/-- **The at-most-two-components input for the plane theta graph**: of any three points off
`D₁ ∪ D₂ ∪ α ∪ β`, two lie in the same connected component.  This is the single remaining
ingredient of the two-component statement (the "at least two" half is
`thetaPlane_not_preconnected`). -/
def ThetaAtMostTwo : Prop :=
  ∀ {D₁ D₂ : Set ℂ},
    (∃ f : C(Disc, ℂ), Function.Injective f ∧ Set.range f = D₁) →
    (∃ g : C(Disc, ℂ), Function.Injective g ∧ Set.range g = D₂) →
    Disjoint D₁ D₂ →
    ∀ (α β : C(Set.Icc (0 : ℝ) 1, ℂ)), Function.Injective α → Function.Injective β →
    α ⟨0, by norm_num⟩ ∈ D₁ → α ⟨1, by norm_num⟩ ∈ D₂ →
    β ⟨0, by norm_num⟩ ∈ D₁ → β ⟨1, by norm_num⟩ ∈ D₂ →
    (∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂) →
    (∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂) →
    (∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t) →
    α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩ →
    α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩ →
    PlaneHypothesis →
    ∀ x y z : ℂ, x ∉ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β →
      y ∉ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β →
      z ∉ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β →
      connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ x =
        connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ y ∨
      connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ x =
        connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ z ∨
      connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ y =
        connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ z

/-- **The two components of the complement of the theta graph** (from the at-most-two input).

The complement `Y` of the theta graph is open and, by `thetaPlane_not_preconnected`, not
preconnected; the at-most-two input says that two components suffice.  Two points of `Y` in
different components therefore generate all of `Y` (every point lies in one of their components),
and the two components are the required open preconnected sets. -/
theorem thetaPlane_components_of_atMostTwo (h2 : ThetaAtMostTwo)
    {D₁ D₂ : Set ℂ}
    (hD₁ : ∃ f : C(Disc, ℂ), Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Disc, ℂ), Function.Injective g ∧ Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, ℂ)) (hαinj : Function.Injective α)
    (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩)
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩)
    (h : PlaneHypothesis) :
    ∃ P₁ P₂ : Set ℂ, P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂ := by
  have h2' := h2 hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁ h
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
    exact thetaPlane_not_preconnected f hf hD₁' g hg hD₂' hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁
      hαint hβint hsep hαβ₀ hαβ₁ h
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


/-! ## The ingredients of the at-most-two statement

The four lemmas below are the classical inputs of the "at most two components" half of the theta
statement (the "at least two" half is `thetaPlane_not_preconnected`):

* `thetaBoundaryJordanCurve` — the boundary-arc Jordan curve of the configuration: the two arcs `α`,
  `β` together with one boundary arc of each disc bound a simple closed curve that contains both arcs
  and meets each disc exactly in a boundary arc of that disc;
* `isPreconnected_range_sdiff_arc` — the image of an injective disc map minus a boundary arc is
  preconnected (a disc minus a "bite" of its boundary);
* `bumpDiscSide` / `bumpDiscSideU` — removing a disc which is glued to one side of a Jordan curve
  along an arc: that side minus the disc is again a side of a Jordan curve. -/

/-- **Invariance of domain at the boundary of the disc** (proved here to keep this module free of
the annulus chapters): the interior of the image of an embedded disc is the image of the open disc.
Copied from the argument of `Work.Smooth.SphereJordan.interior_range_eq_openImage`. -/
theorem interior_range_openImage {f : C(Work.Smooth.SphereJordan.Disc, ℂ)}
    (hf : Function.Injective f) : interior (Set.range f) = openImage f := by
  apply Set.Subset.antisymm
  · rintro y hy
    obtain ⟨z, rfl⟩ := interior_subset hy
    refine ⟨z, ?_, rfl⟩
    by_contra hzlt
    have hznorm : ‖(z : ℂ)‖ = 1 := by
      have hle : ‖(z : ℂ)‖ ≤ 1 := by
        have h := z.2
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      exact le_antisymm hle (not_lt.mp hzlt)
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp isOpen_interior (f z) hy
    have hball : Metric.ball (f z) ε ⊆ Set.range f := hεsub.trans interior_subset
    have hcne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; linarith
    let F : C(Work.Smooth.SphereJordan.Disc, ℂ) :=
      ⟨fun w => f z + ((ε / 2 : ℝ) : ℂ) * (w : ℂ), by fun_prop⟩
    have hFapply : ∀ w : Work.Smooth.SphereJordan.Disc,
        F w = f z + ((ε / 2 : ℝ) : ℂ) * (w : ℂ) := fun w => rfl
    have hFinj : Function.Injective F := by
      intro a b hab
      rw [hFapply a, hFapply b] at hab
      have h2 : ((ε / 2 : ℝ) : ℂ) * (a : ℂ) = ((ε / 2 : ℝ) : ℂ) * (b : ℂ) :=
        add_left_cancel hab
      exact Subtype.ext (mul_left_cancel₀ hcne h2)
    have hFsub : Set.range F ⊆ Set.range f := by
      rintro p ⟨w, rfl⟩
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, hFapply w]
      have h1 : f z + ((ε / 2 : ℝ) : ℂ) * (w : ℂ) - f z = ((ε / 2 : ℝ) : ℂ) * (w : ℂ) := by
        ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
      have hw : ‖(w : ℂ)‖ ≤ 1 := by
        have h := w.2
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      nlinarith
    obtain ⟨g, hge, hginj⟩ := Work.Smooth.SphereJordan.exists_lift_of_range_subset hf hFinj hFsub
    have hg0 : g 0 = z := by
      apply hf
      rw [hge 0, hFapply 0]
      simp
    let g' : C(Work.Smooth.SphereJordan.Disc, ℂ) :=
      ⟨fun w => ((g w : Work.Smooth.SphereJordan.Disc) : ℂ),
        continuous_subtype_val.comp g.continuous⟩
    have hg'apply : ∀ w : Work.Smooth.SphereJordan.Disc,
        g' w = ((g w : Work.Smooth.SphereJordan.Disc) : ℂ) := fun w => rfl
    have hg'inj : Function.Injective g' := by
      intro a b hab
      rw [hg'apply a, hg'apply b] at hab
      exact hginj (Subtype.ext hab)
    have hmem := Work.Smooth.SphereJordan.mem_interior_image_of_norm_lt_one g' hg'inj (0 : Work.Smooth.SphereJordan.Disc) (by simp)
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp isOpen_interior (g' 0) hmem
    have hnormg0 : ‖g' 0‖ = 1 := by
      rw [hg'apply 0, hg0]; exact hznorm
    set q : ℂ := ((1 + ρ / 2 : ℝ) : ℂ) * (g' 0) with hqdef
    have hqball : q ∈ Metric.ball (g' 0) ρ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : q - g' 0 = ((ρ / 2 : ℝ) : ℂ) * (g' 0) := by
        rw [hqdef]; push_cast; ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hnormg0,
        mul_one]
      linarith
    have hqle : ‖q‖ ≤ 1 := by
      obtain ⟨s, hs, hsq⟩ := interior_subset (hρsub hqball)
      rw [← hsq, hg'apply s]
      have h := (g s).2
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    have hqnorm : ‖q‖ = 1 + ρ / 2 := by
      rw [hqdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < 1 + ρ / 2), hnormg0, mul_one]
    linarith
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact interior_mono (by rintro _ ⟨w, hw, rfl⟩; exact ⟨w, rfl⟩)
      (Work.Smooth.SphereJordan.mem_interior_image_of_norm_lt_one f hf z hz)

/-- **The image of the boundary circle lies in the frontier of the image of the disc.** -/
theorem image_circle_subset_frontier {f : C(Work.Smooth.SphereJordan.Disc, ℂ)}
    (hf : Function.Injective f) :
    f '' {z : Work.Smooth.SphereJordan.Disc | ‖(z : ℂ)‖ = 1} ⊆ frontier (Set.range f) := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hnotint : f z ∉ interior (Set.range f) := by
    rw [interior_range_openImage hf]
    rintro ⟨w, hw, hwx⟩
    have hwz : w = z := hf hwx
    rw [hwz] at hw
    have hz1 : ‖(z : ℂ)‖ = 1 := hz
    have hzlt : ‖(z : ℂ)‖ < 1 := hw
    linarith
  have hmem : f z ∈ interior (Set.range f) ∪ frontier (Set.range f) := by
    rw [← closure_eq_interior_union_frontier, (isCompact_range f.continuous).isClosed.closure_eq]
    exact ⟨z, rfl⟩
  rcases hmem with h | h
  · exact absurd h hnotint
  · exact h

/-- **The circle parametrisation is injective on an interval of length less than `2π`.** -/
theorem circlePoint_injOn_Icc {x y : ℝ} (hxy : y - x < 2 * Real.pi) :
    Set.InjOn (Work.Smooth.SphereJordan.circlePoint : ℝ → Work.Smooth.SphereJordan.Disc)
      (Set.Icc x y) := by
  intro a ha b hb hab
  have h : Complex.exp ((a : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I) := by
    have h1 := congrArg (fun z : Work.Smooth.SphereJordan.Disc => (z : ℂ)) hab
    simpa [Work.Smooth.Jordan.circlePoint_coe] using h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have h2 : a = b + (n : ℝ) * (2 * Real.pi) := by
    have h1 := congrArg Complex.im hn
    simpa [Complex.exp_ofReal_mul_I_im] using h1
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have h6 : ((|n| : ℤ) : ℝ) * (2 * Real.pi) < 2 * Real.pi := by
    have habs : |a - b| ≤ y - x :=
      abs_sub_le_iff.mpr ⟨by linarith [ha.2, hb.1], by linarith [hb.2, ha.1]⟩
    have h7 : ((|n| : ℤ) : ℝ) * (2 * Real.pi) = |a - b| := by
      have h8 : a - b = (n : ℝ) * (2 * Real.pi) := by linarith
      rw [h8, abs_mul, abs_of_pos hπ]
      push_cast
      ring
    rw [h7]
    linarith
  have hn0 : n = 0 := by
    have h7 : ((|n| : ℤ) : ℝ) < 1 := by nlinarith [h6, hπ]
    have h9 : |((n : ℝ))| < 1 := by rw [← Int.cast_abs]; exact h7
    have h10 : -(1 : ℝ) < (n : ℝ) ∧ (n : ℝ) < 1 := abs_lt.mp h9
    have h11 : (-1 : ℤ) < n := by exact_mod_cast h10.1
    have h12 : n < 1 := by exact_mod_cast h10.2
    omega
  subst hn0
  simpa using h2

/-- **A boundary arc of an embedded disc between distinct boundary parameters is injective.** -/
theorem discArc_injective {F : C(Work.Smooth.SphereJordan.Disc, ℂ)} (hF : Function.Injective F)
    {x y : ℝ} (hxy0 : x < y) (hxy : y - x < 2 * Real.pi) :
    Function.Injective (Work.Smooth.SphereJordan.discArc F x y) := by
  intro s t hst
  have h1 : Work.Smooth.SphereJordan.circlePoint (x + (s : ℝ) * (y - x)) =
      Work.Smooth.SphereJordan.circlePoint (x + (t : ℝ) * (y - x)) := hF hst
  have hs : x + (s : ℝ) * (y - x) ∈ Set.Icc x y := by
    constructor <;> nlinarith [s.2.1, s.2.2, hxy0]
  have ht : x + (t : ℝ) * (y - x) ∈ Set.Icc x y := by
    constructor <;> nlinarith [t.2.1, t.2.2, hxy0]
  have h2 : x + (s : ℝ) * (y - x) = x + (t : ℝ) * (y - x) :=
    circlePoint_injOn_Icc (x := x) (y := y) hxy hs ht h1
  have h3 : (s : ℝ) * (y - x) = (t : ℝ) * (y - x) := by linarith
  have h4 : y - x ≠ 0 := ne_of_gt (by linarith)
  have h5 : (s : ℝ) = (t : ℝ) := mul_right_cancel₀ h4 h3
  exact Subtype.ext h5

/-- The range of a boundary arc lies in the image of the boundary circle. -/
theorem discArc_range_subset_circle {F : C(Work.Smooth.SphereJordan.Disc, ℂ)} (x y : ℝ) :
    Set.range (Work.Smooth.SphereJordan.discArc F x y) ⊆
      F '' {z : Work.Smooth.SphereJordan.Disc | ‖(z : ℂ)‖ = 1} := by
  rintro _ ⟨t, rfl⟩
  refine ⟨Work.Smooth.Jordan.circlePoint (x + (t : ℝ) * (y - x)), ?_, rfl⟩
  show ‖((Work.Smooth.Jordan.circlePoint (x + (t : ℝ) * (y - x))) : ℂ)‖ = 1
  rw [Work.Smooth.Jordan.circlePoint_coe]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **Two distinct boundary points of an embedded disc span a boundary arc of length `< 2π`.** -/
theorem exists_aligned_param {f : C(Work.Smooth.SphereJordan.Disc, ℂ)}
    (hf : Function.Injective f) {p q : ℂ}
    (hp : p ∈ frontier (Set.range f)) (hq : q ∈ frontier (Set.range f)) (hpq : p ≠ q) :
    ∃ a b : ℝ, a < b ∧ b - a < 2 * Real.pi ∧
      f (Work.Smooth.Jordan.circlePoint a) = p ∧ f (Work.Smooth.Jordan.circlePoint b) = q := by
  obtain ⟨a, ha⟩ := Work.Smooth.SphereJordan.exists_circlePoint_eq_of_mem_trace
    (Work.Smooth.SphereJordan.mem_trace_discCurve_of_mem_frontier hf hp)
  obtain ⟨b₀, hb₀⟩ := Work.Smooth.SphereJordan.exists_circlePoint_eq_of_mem_trace
    (Work.Smooth.SphereJordan.mem_trace_discCurve_of_mem_frontier hf hq)
  have hper : Function.Periodic (Work.Smooth.Jordan.circlePoint :
      ℝ → Work.Smooth.SphereJordan.Disc) (2 * Real.pi) :=
    fun θ => Work.Smooth.SphereJordan.circlePoint_add_two_pi θ
  have hnot : ∀ k : ℤ, a + (k : ℝ) * (2 * Real.pi) ≠ b₀ := by
    intro k hk
    have h1 : Work.Smooth.Jordan.circlePoint b₀ = Work.Smooth.Jordan.circlePoint a := by
      rw [← hk]; exact hper.int_mul k a
    exact hpq (by rw [← ha, ← hb₀, h1])
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  set r : ℝ := b₀ - a - 2 * Real.pi * (⌊(b₀ - a) / (2 * Real.pi)⌋ : ℝ) with hr
  have hr0 : 0 ≤ r := by
    have h1 : (2 * Real.pi) * ((⌊(b₀ - a) / (2 * Real.pi)⌋ : ℝ)) ≤ b₀ - a := by
      have h2 := mul_le_mul_of_nonneg_left (Int.floor_le ((b₀ - a) / (2 * Real.pi)))
        (le_of_lt hπ)
      have h3 : (2 * Real.pi) * ((b₀ - a) / (2 * Real.pi)) = b₀ - a := by field_simp
      linarith [h2, h3]
    rw [hr]; linarith
  have hrlt : r < 2 * Real.pi := by
    have h1 : b₀ - a < ((⌊(b₀ - a) / (2 * Real.pi)⌋ : ℝ) + 1) * (2 * Real.pi) :=
      (div_lt_iff₀ hπ).mp (Int.lt_floor_add_one ((b₀ - a) / (2 * Real.pi)))
    rw [hr]; linarith
  have hrne : r ≠ 0 := by
    intro h0
    have hk : b₀ - a = ((⌊(b₀ - a) / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hr] at h0
      linarith
    exact hnot ⌊(b₀ - a) / (2 * Real.pi)⌋ (by linarith [hk])
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrne)
  refine ⟨a, a + r, by linarith, by linarith, ha, ?_⟩
  have hk : a + r = b₀ + ((-⌊(b₀ - a) / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast; rw [hr]; ring
  rw [hk, hper.int_mul (-⌊(b₀ - a) / (2 * Real.pi)⌋) b₀, hb₀]

/-- **The boundary-arc Jordan curve of the theta configuration.** -/
theorem thetaBoundaryJordanCurve
    {D₁ D₂ : Set ℂ}
    (f : C(Work.Smooth.SphereJordan.Disc, ℂ)) (hf : Function.Injective f)
    (hD₁ : Set.range f = D₁)
    (g : C(Work.Smooth.SphereJordan.Disc, ℂ)) (hg : Function.Injective g)
    (hD₂ : Set.range g = D₂)
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
    ∃ (K : Work.Smooth.Jordan.PlaneCurve), K.IsSimple ∧
      ∃ (δ₁ δ₂ : C(Set.Icc (0 : ℝ) 1, ℂ)),
      Function.Injective δ₁ ∧ Function.Injective δ₂ ∧
      Set.range δ₁ ⊆ frontier (Set.range f) ∧ Set.range δ₂ ⊆ frontier (Set.range g) ∧
      Set.range δ₁ = Set.range f ∩ K.trace ∧ Set.range δ₂ = Set.range g ∩ K.trace ∧
      Set.range α ∪ Set.range β ⊆ K.trace ∧
      K.trace ⊆ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β := by
  classical
  obtain ⟨hα₀fr, hβ₀fr, hα₁fr, hβ₁fr⟩ :=
    Work.Smooth.SphereJordan.endpoints_mem_frontier ⟨f, hf, hD₁⟩ ⟨g, hg, hD₂⟩ α β hα₀ hα₁ hβ₀
      hβ₁ hαint hβint
  have hβ₀fr' : β ⟨0, by norm_num⟩ ∈ frontier (Set.range f) := by rwa [← hD₁] at hβ₀fr
  have hα₀fr' : α ⟨0, by norm_num⟩ ∈ frontier (Set.range f) := by rwa [← hD₁] at hα₀fr
  have hα₁fr' : α ⟨1, by norm_num⟩ ∈ frontier (Set.range g) := by rwa [← hD₂] at hα₁fr
  have hβ₁fr' : β ⟨1, by norm_num⟩ ∈ frontier (Set.range g) := by rwa [← hD₂] at hβ₁fr
  obtain ⟨cβ, cα, hcβα, hcβαlt, hcβ_eq, hcα_eq⟩ := exists_aligned_param hf hβ₀fr' hα₀fr' hαβ₀.symm
  obtain ⟨cα', cβ', hcαβ, hcαβlt, hcα₁_eq, hcβ₁_eq⟩ :=
    exists_aligned_param hg hα₁fr' hβ₁fr' hαβ₁
  let δ₁ : C(Set.Icc (0 : ℝ) 1, ℂ) := Work.Smooth.SphereJordan.discArc f cβ cα
  let δ₂ : C(Set.Icc (0 : ℝ) 1, ℂ) := Work.Smooth.SphereJordan.discArc g cα' cβ'
  have hδ₁₀ : δ₁ ⟨0, by norm_num⟩ = β ⟨0, by norm_num⟩ := by
    show Work.Smooth.SphereJordan.discArc f cβ cα ⟨0, by norm_num⟩ = _
    rw [Work.Smooth.SphereJordan.discArc_zero]; exact hcβ_eq
  have hδ₁₁ : δ₁ ⟨1, by norm_num⟩ = α ⟨0, by norm_num⟩ := by
    show Work.Smooth.SphereJordan.discArc f cβ cα ⟨1, by norm_num⟩ = _
    rw [Work.Smooth.SphereJordan.discArc_one]; exact hcα_eq
  have hδ₂₀ : δ₂ ⟨0, by norm_num⟩ = α ⟨1, by norm_num⟩ := by
    show Work.Smooth.SphereJordan.discArc g cα' cβ' ⟨0, by norm_num⟩ = _
    rw [Work.Smooth.SphereJordan.discArc_zero]; exact hcα₁_eq
  have hδ₂₁ : δ₂ ⟨1, by norm_num⟩ = β ⟨1, by norm_num⟩ := by
    show Work.Smooth.SphereJordan.discArc g cα' cβ' ⟨1, by norm_num⟩ = _
    rw [Work.Smooth.SphereJordan.discArc_one]; exact hcβ₁_eq
  have hδ₁inj : Function.Injective δ₁ := discArc_injective hf hcβα hcβαlt
  have hδ₂inj : Function.Injective δ₂ := discArc_injective hg hcαβ hcαβlt
  have hδ₁f : Set.range δ₁ ⊆ Set.range f := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  have hδ₂g : Set.range δ₂ ⊆ Set.range g := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  have hδ₁D : Set.range δ₁ ⊆ D₁ := hD₁ ▸ hδ₁f
  have hδ₂D : Set.range δ₂ ⊆ D₂ := hD₂ ▸ hδ₂g
  have hδ₁fr : Set.range δ₁ ⊆ frontier (Set.range f) :=
    (discArc_range_subset_circle (F := f) cβ cα).trans (image_circle_subset_frontier hf)
  have hδ₂fr : Set.range δ₂ ⊆ frontier (Set.range g) :=
    (discArc_range_subset_circle (F := g) cα' cβ').trans (image_circle_subset_frontier hg)
  -- the four arcs as paths
  let P₁ : Path (α ⟨0, by norm_num⟩) (α ⟨1, by norm_num⟩) := ⟨α, rfl, rfl⟩
  let P₂ : Path (α ⟨1, by norm_num⟩) (β ⟨1, by norm_num⟩) := ⟨δ₂, hδ₂₀, hδ₂₁⟩
  let P₃ : Path (β ⟨0, by norm_num⟩) (β ⟨1, by norm_num⟩) := ⟨β, rfl, rfl⟩
  let P₄ : Path (β ⟨0, by norm_num⟩) (α ⟨0, by norm_num⟩) := ⟨δ₁, hδ₁₀, hδ₁₁⟩
  let P : Path (α ⟨0, by norm_num⟩) (β ⟨1, by norm_num⟩) := P₁.trans P₂
  let Q : Path (β ⟨1, by norm_num⟩) (α ⟨0, by norm_num⟩) := P₃.symm.trans P₄
  let L : Path (α ⟨0, by norm_num⟩) (α ⟨0, by norm_num⟩) := P.trans Q
  have hr₁ : Set.range (P₁ : ↑unitInterval → ℂ) = Set.range α := rfl
  have hr₂ : Set.range (P₂ : ↑unitInterval → ℂ) = Set.range δ₂ := rfl
  have hr₃ : Set.range (P₃ : ↑unitInterval → ℂ) = Set.range β := rfl
  have hr₄ : Set.range (P₄ : ↑unitInterval → ℂ) = Set.range δ₁ := rfl
  have hαD₁ : Set.range α ∩ D₁ = {α ⟨0, by norm_num⟩} :=
    Work.Smooth.SphereJordan.range_inter_left hdisj hα₀ hα₁ hαint
  have hαD₂ : Set.range α ∩ D₂ = {α ⟨1, by norm_num⟩} :=
    Work.Smooth.SphereJordan.range_inter_right hdisj hα₀ hα₁ hαint
  have hβD₁ : Set.range β ∩ D₁ = {β ⟨0, by norm_num⟩} :=
    Work.Smooth.SphereJordan.range_inter_left hdisj hβ₀ hβ₁ hβint
  have hβD₂ : Set.range β ∩ D₂ = {β ⟨1, by norm_num⟩} :=
    Work.Smooth.SphereJordan.range_inter_right hdisj hβ₀ hβ₁ hβint
  have hαR₁ : Set.range α ∩ Set.range f = {α ⟨0, by norm_num⟩} := by rw [hD₁]; exact hαD₁
  have hαR₂ : Set.range α ∩ Set.range g = {α ⟨1, by norm_num⟩} := by rw [hD₂]; exact hαD₂
  have hβR₁ : Set.range β ∩ Set.range f = {β ⟨0, by norm_num⟩} := by rw [hD₁]; exact hβD₁
  have hβR₂ : Set.range β ∩ Set.range g = {β ⟨1, by norm_num⟩} := by rw [hD₂]; exact hβD₂
  have hFGempty : Set.range f ∩ Set.range g = ∅ := by
    rw [hD₁, hD₂]
    exact Set.disjoint_iff_inter_eq_empty.mp hdisj
  have hdisjαβ : Disjoint (Set.range α) (Set.range β) :=
    Work.Smooth.SphereJordan.disjoint_range_of_ends hdisj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep
      hαβ₀ hαβ₁
  have hαβempty : Set.range α ∩ Set.range β = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisjαβ
  have hDempty : D₁ ∩ D₂ = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisj
  have h₁₂ : Set.range P₁ ∩ Set.range P₂ ⊆ {α ⟨1, by norm_num⟩} := by
    rw [hr₁, hr₂]
    intro x ⟨hx₁, hx₂⟩
    have hx : x ∈ Set.range α ∩ D₂ := ⟨hx₁, hδ₂D hx₂⟩
    rwa [hαD₂] at hx
  have h₃₄ : Set.range P₃.symm ∩ Set.range P₄ ⊆ {β ⟨0, by norm_num⟩} := by
    rw [Path.symm_range, hr₃, hr₄]
    intro x ⟨hx₁, hx₂⟩
    have hx : x ∈ Set.range β ∩ D₁ := ⟨hx₁, hδ₁D hx₂⟩
    rwa [hβD₁] at hx
  have hPQ : Set.range P ∩ Set.range Q ⊆ {α ⟨0, by norm_num⟩, β ⟨1, by norm_num⟩} := by
    have hP : Set.range P = Set.range α ∪ Set.range δ₂ := by
      rw [show P = P₁.trans P₂ from rfl, path_range_trans, hr₁, hr₂]
    have hQ : Set.range Q = Set.range β ∪ Set.range δ₁ := by
      rw [show Q = P₃.symm.trans P₄ from rfl, path_range_trans, Path.symm_range, hr₃, hr₄]
    rw [hP, hQ]
    rintro x ⟨hx | hx, hy | hy⟩
    · exfalso
      exact (Set.eq_empty_iff_forall_notMem.mp hαβempty x) ⟨hx, hy⟩
    · have hx' : x ∈ Set.range α ∩ D₁ := ⟨hx, hδ₁D hy⟩
      rw [hαD₁] at hx'
      exact Set.mem_insert_iff.mpr (Or.inl hx')
    · have hy' : x ∈ Set.range β ∩ D₂ := ⟨hy, hδ₂D hx⟩
      rw [hβD₂] at hy'
      exact Set.mem_insert_iff.mpr (Or.inr hy')
    · exfalso
      exact (Set.eq_empty_iff_forall_notMem.mp hDempty x) ⟨hδ₁D hy, hδ₂D hx⟩
  have hPinj : Function.Injective P := path_inj_trans P₁ P₂ hαinj hδ₂inj h₁₂
  have hQinj : Function.Injective Q :=
    path_inj_trans P₃.symm P₄ (path_injective_symm hβinj) hδ₁inj h₃₄
  have hLinj : Set.InjOn (⇑L) {t : ↑unitInterval | (t : ℝ) < 1} :=
    path_injOn_trans_loop P Q hPinj hQinj hPQ
  have hrangeL : Set.range (⇑(L : C(Set.Icc (0 : ℝ) 1, ℂ))) =
      Set.range α ∪ Set.range β ∪ Set.range δ₁ ∪ Set.range δ₂ := by
    show Set.range (⇑L) = Set.range α ∪ Set.range β ∪ Set.range δ₁ ∪ Set.range δ₂
    rw [show L = P.trans Q from rfl, path_range_trans,
      show P = P₁.trans P₂ from rfl, path_range_trans,
      show Q = P₃.symm.trans P₄ from rfl, path_range_trans, Path.symm_range,
      hr₁, hr₂, hr₃, hr₄]
    ext x
    simp only [Set.mem_union]
    tauto
  have hp : (L : C(Set.Icc (0 : ℝ) 1, ℂ)) ⟨0, by norm_num⟩ =
      (L : C(Set.Icc (0 : ℝ) 1, ℂ)) ⟨1, by norm_num⟩ :=
    (Path.source L).trans (Path.target L).symm
  let K : Work.Smooth.Jordan.PlaneCurve := loopCurve (L : C(Set.Icc (0 : ℝ) 1, ℂ)) hp
  have hKsimple : K.IsSimple := loopCurve_isSimple _ _ hLinj
  have hKtrace : K.trace = Set.range α ∪ Set.range β ∪ Set.range δ₁ ∪ Set.range δ₂ := by
    change Set.range ((loopCurve (L : C(Set.Icc (0 : ℝ) 1, ℂ)) hp).γ) =
      Set.range α ∪ Set.range β ∪ Set.range δ₁ ∪ Set.range δ₂
    rw [range_loopCurve, hrangeL]
  refine ⟨K, hKsimple, δ₁, δ₂, hδ₁inj, hδ₂inj, hδ₁fr, hδ₂fr, ?_, ?_, ?_, ?_⟩
  · -- the trace of `δ₁` in the trace of the curve
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      have hmem : x ∈ K.trace := by
        rw [hKtrace]
        exact Or.inl (Or.inr hx)
      exact ⟨hδ₁f hx, hmem⟩
    · intro x hx
      have hx' := hx.2
      rw [hKtrace] at hx'
      rcases hx' with ((hx' | hx') | hx') | hx'
      · have hmem : x ∈ Set.range α ∩ Set.range f := ⟨hx', hx.1⟩
        rw [hαR₁] at hmem
        rw [hmem]
        exact ⟨⟨1, by norm_num⟩, hδ₁₁⟩
      · have hmem : x ∈ Set.range β ∩ Set.range f := ⟨hx', hx.1⟩
        rw [hβR₁] at hmem
        rw [hmem]
        exact ⟨⟨0, by norm_num⟩, hδ₁₀⟩
      · exact hx'
      · exfalso
        exact (Set.eq_empty_iff_forall_notMem.mp hFGempty x) ⟨hx.1, hδ₂g hx'⟩
  · -- the trace of `δ₂` in the trace of the curve
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      have hmem : x ∈ K.trace := by
        rw [hKtrace]
        exact Or.inr hx
      exact ⟨hδ₂g hx, hmem⟩
    · intro x hx
      have hx' := hx.2
      rw [hKtrace] at hx'
      rcases hx' with ((hx' | hx') | hx') | hx'
      · have hmem : x ∈ Set.range α ∩ Set.range g := ⟨hx', hx.1⟩
        rw [hαR₂] at hmem
        rw [hmem]
        exact ⟨⟨0, by norm_num⟩, hδ₂₀⟩
      · have hmem : x ∈ Set.range β ∩ Set.range g := ⟨hx', hx.1⟩
        rw [hβR₂] at hmem
        rw [hmem]
        exact ⟨⟨1, by norm_num⟩, hδ₂₁⟩
      · exfalso
        exact (Set.eq_empty_iff_forall_notMem.mp hFGempty x) ⟨hδ₁f hx', hx.1⟩
      · exact hx'
  · intro x hx
    rw [hKtrace]
    simp only [Set.mem_union] at hx ⊢
    tauto
  · intro x hx
    rw [hKtrace] at hx
    simp only [Set.mem_union] at hx ⊢
    have h₁ : ∀ x, x ∈ Set.range δ₁ → x ∈ D₁ := fun x hx => hδ₁D hx
    have h₂ : ∀ x, x ∈ Set.range δ₂ → x ∈ D₂ := fun x hx => hδ₂D hx
    tauto

theorem isPreconnected_range_sdiff_arc {f : C(Work.Smooth.SphereJordan.Disc, ℂ)}
    (hf : Function.Injective f) {δ : C(Set.Icc (0 : ℝ) 1, ℂ)} (_hδ : Function.Injective δ)
    (hδsub : Set.range δ ⊆ frontier (Set.range f)) :
    IsPreconnected (Set.range f \ Set.range δ) := by
  have hA : IsPreconnected (openImage f) := openImage_preconnected f
  have hAint : openImage f ⊆ interior (Set.range f) :=
    interior_maximal (by rintro x ⟨z, hz, rfl⟩; exact ⟨z, rfl⟩)
      (openImage_isOpen_of_injective f hf)
  have hsub : openImage f ⊆ Set.range f \ Set.range δ := by
    rintro w ⟨z, hz, rfl⟩
    refine ⟨⟨z, rfl⟩, ?_⟩
    intro hwd
    have h1 : f z ∈ frontier (Set.range f) := hδsub hwd
    rw [frontier_eq_closure_inter_closure] at h1
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (f z) (hAint ⟨z, hz, rfl⟩)
    obtain ⟨y, hyc, hyε⟩ := Metric.mem_closure_iff.mp h1.2 (ε / 2) (by linarith)
    have hy : y ∈ Metric.ball (f z) ε := by
      rw [Metric.mem_ball, dist_comm]; linarith
    exact hyc (interior_subset (hball hy))
  have hcl : Set.range f \ Set.range δ ⊆ closure (openImage f) := by
    intro w hw
    rw [closure_openImage]
    exact hw.1
  exact hA.subset_closure hsub hcl

/-- **The at-most-two input**, the remaining ingredient. -/
theorem thetaAtMostTwo_input : ThetaAtMostTwo := by
  intro D₁ D₂ hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁ h
  exact Work.Smooth.SphereJordan.thetaPlaneAtMostTwo hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀
    hβ₁ hαint hβint hsep hαβ₀ hαβ₁ h

/-- **`Work.Smooth.SphereJordan.planeArcComponentsCore`**: the two components of the plane annulus
cut by two crosscuts. -/
theorem planeArcComponentsCore (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {D₁ D₂ : Set ℂ}
    (hD₁ : ∃ f : C(Work.Smooth.SphereJordan.Disc, ℂ), Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Work.Smooth.SphereJordan.Disc, ℂ), Function.Injective g ∧ Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, ℂ)) (hαinj : Function.Injective α)
    (hβinj : Function.Injective β)
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
      IsPreconnected P₁ ∧ IsPreconnected P₂ :=
  thetaPlane_components_of_atMostTwo thetaAtMostTwo_input hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁
    hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁ h

end

end Work.Smooth.SphereJordan
