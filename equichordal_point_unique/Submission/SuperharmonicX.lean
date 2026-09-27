import Submission.UnifDeps
import Submission.MaxPrincipleRegion
import Submission.SubharmonicAlgebra

/-!
# Superharmonic functions on `X`: negation, and the minimum principle on regions

The Riemann-surface theory of `Submission/RiemannSurface.lean` defines `SubharmonicOnX` and
`SuperharmonicOnX` independently (Hubbard's Definition 1.2.1, expressed by circle mean-value
inequalities in charts).  For the comparison arguments of the Green-function construction one
needs the two standard facts:

* `u` is superharmonic exactly where `-u` is subharmonic (`SuperharmonicAtChart.neg`,
  `SubharmonicAtChart.neg`, and the set-level versions `SuperharmonicOnX.neg`,
  `SubharmonicOnX.neg`);
* hence the *minimum* principle on a relatively compact region: a superharmonic function with
  `liminf ≥ a` at every frontier point is `≥ a` inside
  (`SuperharmonicOnX.nonneg_of_frontier_liminf`), which is the maximum principle
  `SubharmonicOnX.le_of_frontier_limsup` applied to the negation.

The local strong minimum principle (`SuperharmonicAtChart.eqOn_of_le`) is likewise the negation of
the local strong maximum principle for subharmonic functions.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The circle average of the pointwise negative is the negative of the circle average. -/
theorem circleAverage_neg_fun (f : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    Real.circleAverage (fun z => -f z) c R = -Real.circleAverage f c R := by
  have h := Real.circleAverage_fun_smul (f := f) (a := (-1 : ℝ)) (c := c) (R := R)
  simpa using h

/-! ## Negation of subharmonicity -/

theorem SubharmonicAtChart.neg {u : X → ℝ} {c : OpenPartialHomeomorph X ℂ} {x : X}
    (h : SubharmonicAtChart u c x) : SuperharmonicAtChart (fun y => -u y) c x := by
  obtain ⟨hsrc, ρ, hρ, hsub, hcont, hmvp⟩ := h
  refine ⟨hsrc, ρ, hρ, hsub, ?_, ?_⟩
  · have hfun : (fun y => -u y) ∘ c.symm = fun w => -(u ∘ c.symm) w := by
      funext w; rfl
    rw [hfun]
    exact hcont.neg
  · intro p hp r hr hrsub
    have hfun : (fun y => -u y) ∘ c.symm = fun w => -(u ∘ c.symm) w := by
      funext w; rfl
    rw [hfun, circleAverage_neg_fun]
    exact neg_le_neg (hmvp p hp r hr hrsub)

theorem SuperharmonicAtChart.neg {u : X → ℝ} {c : OpenPartialHomeomorph X ℂ} {x : X}
    (h : SuperharmonicAtChart u c x) : SubharmonicAtChart (fun y => -u y) c x := by
  obtain ⟨hsrc, ρ, hρ, hsub, hcont, hmvp⟩ := h
  refine ⟨hsrc, ρ, hρ, hsub, ?_, ?_⟩
  · have hfun : (fun y => -u y) ∘ c.symm = fun w => -(u ∘ c.symm) w := by
      funext w; rfl
    rw [hfun]
    exact hcont.neg
  · intro p hp r hr hrsub
    have hfun : (fun y => -u y) ∘ c.symm = fun w => -(u ∘ c.symm) w := by
      funext w; rfl
    rw [hfun, circleAverage_neg_fun]
    exact neg_le_neg (hmvp p hp r hr hrsub)

theorem SubharmonicOnXAt.neg {u : X → ℝ} {x : X} (h : SubharmonicOnXAt u x) :
    SuperharmonicOnXAt (fun y => -u y) x :=
  SubharmonicAtChart.neg h

theorem SuperharmonicOnXAt.neg {u : X → ℝ} {x : X} (h : SuperharmonicOnXAt u x) :
    SubharmonicOnXAt (fun y => -u y) x :=
  SuperharmonicAtChart.neg h

theorem SubharmonicOnX.neg {u : X → ℝ} {U : Set X} (h : SubharmonicOnX u U) :
    SuperharmonicOnX (fun y => -u y) U :=
  ⟨h.1.neg, fun x hx => SubharmonicOnXAt.neg (h.2 x hx)⟩

theorem SuperharmonicOnX.neg {u : X → ℝ} {U : Set X} (h : SuperharmonicOnX u U) :
    SubharmonicOnX (fun y => -u y) U :=
  ⟨h.1.neg, fun x hx => SuperharmonicOnXAt.neg (h.2 x hx)⟩

/-- **Transport of subharmonicity between two arbitrary charts.**  If `a` lies in the sources of
both charts and all transitions between the two charts are complex analytic, then subharmonicity at
`a` measured in the chart `c` is the same condition as subharmonicity at `a` measured in the
chart `d`. -/
theorem SubharmonicAtChart.transport
    {u : X → ℝ} {c d : OpenPartialHomeomorph X ℂ} {a : X}
    (hca : a ∈ c.source) (hda : a ∈ d.source)
    (hanaT : ∀ z : ℂ, z ∈ d.target → d.symm z ∈ c.source →
      AnalyticAt ℂ (fun z : ℂ => c (d.symm z)) z)
    (hanaS : ∀ w : ℂ, w ∈ c.target → c.symm w ∈ d.source →
      AnalyticAt ℂ (fun w : ℂ => d (c.symm w)) w) :
    SubharmonicAtChart u c a → SubharmonicAtChart u d a := by
  intro h
  obtain ⟨-, ρ₀, hρ₀, -, hc₀, hm₀⟩ := h
  exact transport_subharmonic hca hda hanaT hanaS hρ₀ le_rfl hc₀ hm₀

/-- **Transport of superharmonicity between two arbitrary charts** (the dual of
`SubharmonicAtChart.transport`). -/
theorem SuperharmonicAtChart.transport
    {u : X → ℝ} {c d : OpenPartialHomeomorph X ℂ} {a : X}
    (hca : a ∈ c.source) (hda : a ∈ d.source)
    (hanaT : ∀ z : ℂ, z ∈ d.target → d.symm z ∈ c.source →
      AnalyticAt ℂ (fun z : ℂ => c (d.symm z)) z)
    (hanaS : ∀ w : ℂ, w ∈ c.target → c.symm w ∈ d.source →
      AnalyticAt ℂ (fun w : ℂ => d (c.symm w)) w)
    (h : SuperharmonicAtChart u c a) : SuperharmonicAtChart u d a := by
  have hsc : SubharmonicAtChart (fun y => -u y) c a := h.neg
  obtain ⟨-, ρ₀, hρ₀, -, hc₀, hm₀⟩ := hsc
  have hsd : SubharmonicAtChart (fun y => -u y) d a :=
    transport_subharmonic hca hda hanaT hanaS hρ₀ le_rfl hc₀ hm₀
  obtain ⟨hda', ρ, hρ, htgt, hcont, hmvp⟩ := hsd
  have hfun : (fun y : X => -u y) ∘ d.symm = fun w : ℂ => -(u (d.symm w)) := by
    funext w; rfl
  rw [hfun] at hcont hmvp
  refine ⟨hda', ρ, hρ, htgt, ?_, ?_⟩
  · exact hcont.neg.congr (fun w _ => by simp)
  · intro p hp r hr hpr
    have h1 := hmvp p hp r hr hpr
    have h2 : Real.circleAverage (fun w : ℂ => -(u (d.symm w))) p r
        = -Real.circleAverage (fun w : ℂ => u (d.symm w)) p r :=
      circleAverage_neg_fun (fun w : ℂ => u (d.symm w)) p r
    rw [h2] at h1
    have h1' : -(u (d.symm p)) ≤ -Real.circleAverage (fun w : ℂ => u (d.symm w)) p r := by
      simpa using h1
    change Real.circleAverage (fun w : ℂ => u (d.symm w)) p r ≤ u (d.symm p)
    linarith [h1']


/-! ## Pointwise minima are superharmonic

The minimum of two superharmonic functions is superharmonic (the dual of the fact that the
maximum of two subharmonic functions is subharmonic).  This is the closure property needed to
build *downward directed* (balayage) families of superharmonic functions. -/

theorem SuperharmonicOnXAt.min {u v : X → ℝ} {x : X} (hu : SuperharmonicOnXAt u x)
    (hv : SuperharmonicOnXAt v x) : SuperharmonicOnXAt (fun y => Min.min (u y) (v y)) x := by
  have h' : SubharmonicOnXAt (fun y => -Min.min (u y) (v y)) x := by
    have hsup := SubharmonicOnXAt.sup (SuperharmonicOnXAt.neg hu) (SuperharmonicOnXAt.neg hv)
    have hfun : (fun y => -Min.min (u y) (v y)) =
        Max.max (fun y => -u y) (fun y => -v y) := by
      funext y
      rcases le_total (u y) (v y) with hh | hh
      · simp only [min_eq_left hh]
        exact (max_eq_left (neg_le_neg hh)).symm
      · simp only [min_eq_right hh]
        exact (max_eq_right (neg_le_neg hh)).symm
    rwa [hfun]
  simpa using h'.neg

theorem SuperharmonicOnX.min {u v : X → ℝ} {U : Set X} (hu : SuperharmonicOnX u U)
    (hv : SuperharmonicOnX v U) : SuperharmonicOnX (fun y => Min.min (u y) (v y)) U := by
  have h' : SubharmonicOnX (fun y => -Min.min (u y) (v y)) U := by
    have hsup := SubharmonicOnX.sup (SuperharmonicOnX.neg hu) (SuperharmonicOnX.neg hv)
    have hfun : (fun y => -Min.min (u y) (v y)) =
        Max.max (fun y => -u y) (fun y => -v y) := by
      funext y
      rcases le_total (u y) (v y) with hh | hh
      · simp only [min_eq_left hh]
        exact (max_eq_left (neg_le_neg hh)).symm
      · simp only [min_eq_right hh]
        exact (max_eq_right (neg_le_neg hh)).symm
    rwa [hfun]
  simpa using h'.neg

/-! ## The minimum principle on a relatively compact region -/

section Region

variable [T2Space X] [PreconnectedSpace X]

/-- **Minimum principle on a relatively compact region, liminf form.**  If `v` is superharmonic
on an open set `U` with compact closure and nonempty frontier, and the liminf of `v` at every
frontier point is at least `a`, then `v ≥ a` on `U`. -/
theorem SuperharmonicOnX.nonneg_of_frontier_liminf {U : Set X} (hU : IsOpen U) {v : X → ℝ}
    (hv : SuperharmonicOnX v U) (hcomp : IsCompact (closure U)) (hne : (frontier U).Nonempty)
    {a : ℝ} (hlim : ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[U] ξ, a - ε ≤ v z) :
    ∀ z ∈ U, a ≤ v z := by
  have hle := SubharmonicOnX.le_of_frontier_limsup (U := U) hU (hv.neg) hcomp hne
    (a := -a) (fun ξ hξ ε hε => (hlim ξ hξ ε hε).mono (fun z hz => by
      show -v z ≤ -a + ε
      linarith))
  intro z hz
  have h := hle z hz
  simpa using neg_le_neg h

/-- **Local strong minimum principle for superharmonic functions.**  If `u` is superharmonic at
`x` and `u ≥ u x` on a neighbourhood of `x`, then `u = u x` on a neighbourhood of `x`. -/
theorem SuperharmonicOnXAt.eqOn_of_ge {u : X → ℝ} {x : X} (hu : SuperharmonicOnXAt u x)
    {U : Set X} (hU : U ∈ 𝓝 x) (hge : ∀ y ∈ U, u x ≤ u y) :
    ∃ V ∈ 𝓝 x, ∀ y ∈ V, u y = u x := by
  obtain ⟨V, hV, hVeq⟩ := SubharmonicOnXAt.eqOn_of_le (hu.neg) hU (fun y hy => by
    show -u y ≤ -u x
    linarith [hge y hy])
  exact ⟨V, hV, fun y hy => by
    have h : -u y = -u x := hVeq y hy
    exact neg_inj.mp h⟩

end Region

end Submission
