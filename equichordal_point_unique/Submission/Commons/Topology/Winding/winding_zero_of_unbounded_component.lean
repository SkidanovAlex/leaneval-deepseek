import Submission.Commons.Topology.Curve.argument_lift_of_close
import Submission.Commons.Topology.Curve.argument_lift_of_far

namespace Commons.Topology.Winding

set_option autoImplicit false

open Set Metric Filter

noncomputable section

/-- `HasArg f p` says that the closed curve `t ↦ f t - p` admits a continuous `1`-periodic
argument function. -/
def HasArg (f : ℝ → ℂ) (p : ℂ) : Prop :=
  ∃ θ : ℝ → ℝ, Continuous θ ∧ (∀ t, θ (t + 1) = θ t) ∧
    ∀ t, f t - p = (‖f t - p‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)

/-- The range of a continuous `1`-periodic function `ℝ → ℂ` is compact (because it is the image
of the compact interval `[0, 1]`). -/
theorem isCompact_range_of_periodic {f : ℝ → ℂ} (hf : Continuous f)
    (hper : Function.Periodic f 1) : IsCompact (Set.range f) := by
  rw [← hper.image_Icc (by norm_num : (0 : ℝ) < 1) 0]
  exact isCompact_Icc.image hf

/-- **A closed curve does not wind around the unbounded component of its complement.** Let `f : ℝ → ℂ` be continuous and `1`-periodic, and let `p : ℂ` be a point not on the curve whose connected component in the complement `(Set.range f)ᶜ` is unbounded. Then the closed curve `t ↦ f t - p` has winding number zero around the origin: there is a continuous `1`-periodic argument function `θ` with `f t - p = ‖f t - p‖ * exp (θ t * I)`.

Suggested proof route, in three steps. (1) If the whole curve avoids a ball around `p` with a uniform positive radius, then the argument stays in an arc of length `< pi` (because `‖f t‖ < R` and `‖p‖ > 2R` imply `|arg(f t - p) - arg(-p)| <= arcsin(‖f t‖/‖p‖) < pi/2`), so `θ` can be taken bounded, whence its drift is `0`. (2) The drift (as a function of `p`) is locally constant on `ℂ \ (range f)`: this follows from the homotopy invariance of the drift, since a small perturbation of `p` perturbs the closed curve `t ↦ f t - p` through zero-free curves. (3) The unbounded component of `(range f)ᶜ` is connected, contains points of arbitrarily large norm (where step (1) applies), and the drift is locally constant on it, hence identically `0` there.

The hypothesis `¬ Bornology.IsBounded (connectedComponentIn (Set.range f)ᶜ p)` says exactly that `p` lies in the unbounded component of the complement of the curve. -/
theorem winding_zero_of_unbounded_component
    {f : ℝ → ℂ} (hf : Continuous f) (hper : Function.Periodic f 1)
    {p : ℂ} (hp : p ∉ Set.range f)
    (hunb : ¬ Bornology.IsBounded (connectedComponentIn (Set.range f)ᶜ p)) :
    ∃ θ : ℝ → ℝ, Continuous θ ∧ (∀ t, θ (t+1) = θ t) ∧
      ∀ t, f t - p = (‖f t - p‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I) := by
  have hKcpt : IsCompact (Set.range f) := isCompact_range_of_periodic hf hper
  have hKclosed : IsClosed (Set.range f) := hKcpt.isClosed
  have hKne : (Set.range f).Nonempty := ⟨f 0, mem_range_self 0⟩
  set V : Set ℂ := (Set.range f)ᶜ with hV
  set C : Set ℂ := connectedComponentIn (Set.range f)ᶜ p with hC
  set A : Set ℂ := {x | HasArg f x} with hA
  have hCV : C ⊆ V := connectedComponentIn_subset _ _
  have hρpos : ∀ x ∈ V, 0 < Metric.infDist x (Set.range f) := fun x hx =>
    (hKclosed.notMem_iff_infDist_pos hKne).mp hx
  -- The set `A ∩ V` is open: near a point where the argument exists, the same curve
  -- with the basepoint moved slightly still has a periodic argument.
  have hopen : IsOpen (A ∩ V) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨hxA, hxV⟩ := hx
    obtain ⟨θ, hθc, hθper, hθrep⟩ := hxA
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x (by linarith [hρpos x hxV] :
        (0:ℝ) < Metric.infDist x (Set.range f) / 2)) ?_
    intro y hy
    have hyd : ‖y - x‖ < Metric.infDist x (Set.range f) / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    refine ⟨?_, ?_⟩
    · exact Commons.Topology.Curve.argument_lift_of_close hf hper hxV hθc hθper hθrep hyd
    · intro hyK
      have hdist : dist x y < Metric.infDist x (Set.range f) := by
        rw [dist_eq_norm, norm_sub_rev]
        linarith [hρpos x hxV]
      exact Metric.notMem_of_dist_lt_infDist (s := Set.range f) hdist hyK
  -- Points outside `A` inside `C` have a ball disjoint from `A`.
  have hnotA_ball : ∀ x ∈ C, x ∉ A →
      Metric.ball x (Metric.infDist x (Set.range f) / 4) ⊆ Aᶜ := by
    intro x hxC hxA y hy hyA
    obtain ⟨φ, hφc, hφper, hφrep⟩ := hyA
    have hxV : x ∈ V := hCV hxC
    have hρx : 0 < Metric.infDist x (Set.range f) := hρpos x hxV
    have hd : ‖y - x‖ < Metric.infDist x (Set.range f) / 4 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    have hyV : y ∉ Set.range f := by
      intro hyK
      have h1 := Metric.infDist_le_dist_of_mem (s := Set.range f) (x := x) (y := y) hyK
      rw [dist_eq_norm, norm_sub_rev] at h1
      linarith
    have h2 := Metric.infDist_le_infDist_add_dist (s := Set.range f) (x := x) (y := y)
    rw [dist_eq_norm, norm_sub_rev] at h2
    have h3 : ‖x - y‖ < Metric.infDist y (Set.range f) / 2 := by
      rw [norm_sub_rev]
      linarith
    exact hxA (Commons.Topology.Curve.argument_lift_of_close hf hper hyV hφc hφper hφrep h3)
  -- The union of the small balls around `C \ A` is open and disjoint from `A`.
  have hvopen : IsOpen (⋃ x : ↥(C \ A), Metric.ball (x : ℂ)
      (Metric.infDist (x : ℂ) (Set.range f) / 4)) :=
    isOpen_iUnion fun x => Metric.isOpen_ball
  have hvdisj : Disjoint (A ∩ V) (⋃ x : ↥(C \ A), Metric.ball (x : ℂ)
      (Metric.infDist (x : ℂ) (Set.range f) / 4)) := by
    refine Set.disjoint_left.mpr ?_
    intro y hyA hyv
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hyv
    exact (hnotA_ball (x : ℂ) x.2.1 x.2.2) hx hyA.1
  have hcover : C ⊆ (A ∩ V) ∪ (⋃ x : ↥(C \ A), Metric.ball (x : ℂ)
      (Metric.infDist (x : ℂ) (Set.range f) / 4)) := by
    intro x hxC
    by_cases hxA : x ∈ A
    · exact Or.inl ⟨hxA, hCV hxC⟩
    · refine Or.inr (Set.mem_iUnion.mpr ⟨⟨x, hxC, hxA⟩, ?_⟩)
      have hρx : 0 < Metric.infDist x (Set.range f) := hρpos x (hCV hxC)
      simp only [Metric.mem_ball, dist_eq_norm, sub_self, norm_zero]
      linarith
  -- The component is unbounded, so it contains a point far enough away that the argument
  -- can be taken bounded.
  obtain ⟨R, hR⟩ := Commons.Topology.Curve.argument_lift_of_far hf hper
  have hCunb : ∃ x ∈ C, R < ‖x‖ := by
    by_contra hcon
    push Not at hcon
    exact hunb (isBounded_iff_forall_norm_le.mpr ⟨R, hcon⟩)
  obtain ⟨x, hxC, hxR⟩ := hCunb
  have hpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hsub : C ⊆ A ∩ V :=
    IsPreconnected.subset_left_of_subset_union hopen hvopen hvdisj hcover
      ⟨x, hxC, hR x hxR, hCV hxC⟩ hpre
  exact (hsub (mem_connectedComponentIn (show p ∈ (Set.range f)ᶜ from hp))).1

end

end Commons.Topology.Winding
