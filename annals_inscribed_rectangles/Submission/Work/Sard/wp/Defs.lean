import Mathlib

/-!
# Weak Sard's theorem: shared definitions and elementary topological tools

This file holds the definitions and the elementary tools (a topological "slice" lemma and a Baire
category lemma) shared by the proof of the *weak* form of Sard's theorem for smooth maps
`ρ : E → F` with `finrank ℝ E = finrank ℝ F + 1`: the set of critical values of `ρ` on an open set
has empty interior.

* `Work.Sard.wp.WeakSard m` : the statement at level `m`.
* `Work.Sard.wp.HolderTwo`, `Work.Sard.wp.HolderThree` : the pointwise Hölder estimates which are
  the analytic input for the "flat" part of the proof.
* `Work.Sard.wp.interior_iUnion_slices_eq_empty` : if every slice has empty interior, so has the
  union of the slices; this is the step that lets one reduce the codimension by one.
* `Work.Sard.wp.interior_eq_empty_iUnion_isClosed` : Baire category.
-/

open scoped ContDiff Topology NNReal
open MeasureTheory Set Filter

namespace Work.Sard.wp

/-- `WeakSard m` is the weak Sard statement at level `m`: for a smooth map `ρ : E → F` between
finite dimensional real normed spaces with `finrank ℝ F = m` and `finrank ℝ E = finrank ℝ F + 1`,
the image of the set of points of an open set `U` where `ρ` is not a submersion has empty
interior. -/
def WeakSard.{u, v} (m : ℕ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F],
    Module.finrank ℝ F = m → Module.finrank ℝ E = Module.finrank ℝ F + 1 →
    ∀ (U : Set E), IsOpen U → ∀ (ρ : E → F),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U →
      interior (ρ '' (U ∩ {z : E | ¬ Function.Surjective (fderivWithin ℝ ρ U z)})) = ∅

/-- `WeakSardGlobal m` is the weak Sard statement at level `m` for *globally* smooth maps on the
whole space: the critical values of a smooth `ρ : E → F` with `finrank ℝ F = m` and
`finrank ℝ E = finrank ℝ F + 1` have empty interior. -/
def WeakSardGlobal.{u, v} (m : ℕ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F],
    Module.finrank ℝ F = m → Module.finrank ℝ E = Module.finrank ℝ F + 1 →
    ∀ (ρ : E → F), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ →
      interior (ρ '' {z : E | ¬ Function.Surjective (fderiv ℝ ρ z)}) = ∅

/-- Pointwise `2`-Hölder estimate on the zero set of the derivative: if `f` is smooth at `x` and
`fderiv ℝ f x = 0`, then, near `x` along the zero set of `fderiv ℝ f`, the map `f` is
`2`-Hölder. -/
def HolderTwo.{u, v} (E : Type u) (F : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) : Prop :=
  ∀ (K : Set E) (x : E), ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f x → fderiv ℝ f x = 0 →
    ∃ C : ℝ≥0, ∃ t ∈ 𝓝[K ∩ {y : E | fderiv ℝ f y = 0}] x, HolderOnWith C 2 f t

/-- Pointwise `2`-Hölder estimate on the common zero set of the first and second derivative. -/
def HolderThree.{u, v} (E : Type u) (F : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) : Prop :=
  ∀ (K : Set E) (x : E), ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f x → fderiv ℝ f x = 0 →
    fderiv ℝ (fun y => fderiv ℝ f y) x = 0 →
    ∃ C : ℝ≥0,
      ∃ t ∈ 𝓝[K ∩ {y : E | fderiv ℝ f y = 0 ∧ fderiv ℝ (fun z => fderiv ℝ f z) y = 0}] x,
        HolderOnWith C 3 f t

theorem exists_contDiff_eq_nhds_local {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) (y₀ : E)
    (s : Set E) (hs : s ∈ nhds y₀) (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g s) :
    ∃ G : E → F, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧ G =ᶠ[nhds y₀] g := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
  let b : ContDiffBump y₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hbRin : b.rIn = ε / 4 := rfl
  have hbRout : b.rOut = ε / 2 := rfl
  refine ⟨fun y => b y • g y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Metric.ball y₀ ε
    · have hxB : Metric.ball y₀ ε ∈ 𝓝 x := Metric.isOpen_ball.mem_nhds hx
      exact (b.contDiff.contDiffAt).smul ((hg.mono hεs).contDiffAt hxB)
    · have hxsupp : x ∉ tsupport (b : E → ℝ) := by
        rw [b.tsupport_eq, hbRout]
        exact fun hxc => hx (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε) hxc)
      have h0 : (fun _ : E => (0 : F)) =ᶠ[𝓝 x] (fun y => b y • g y) := by
        filter_upwards [(isClosed_tsupport (b : E → ℝ)).isOpen_compl.mem_nhds hxsupp] with y hy
        have hy' : b y = 0 := by
          by_contra hb
          exact hy (subset_tsupport (b : E → ℝ) hb)
        simp [hy']
      exact contDiffAt_const.congr_of_eventuallyEq h0.symm
  · filter_upwards [Metric.ball_mem_nhds y₀ (by positivity : (0:ℝ) < ε / 4)] with y hy
    have hy' : y ∈ Metric.closedBall y₀ b.rIn := by
      rw [hbRin]; exact Metric.ball_subset_closedBall hy
    rw [b.one_of_mem_closedBall hy', one_smul]

/-- **Slice lemma.** If every slice `S u` has empty interior, then the union of the slices
`{u} ×ˢ S u` has empty interior. -/
theorem interior_iUnion_slices_eq_empty {G W : Type*} [TopologicalSpace G] [TopologicalSpace W]
    (S : G → Set W) (hS : ∀ u, interior (S u) = ∅) :
    interior (⋃ u : G, ({u} : Set G) ×ˢ S u) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro p
  rw [mem_closure_iff_nhds]
  intro T hT
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hsubT : T ⊆ ⋃ u : G, ({u} : Set G) ×ˢ S u := by
    intro x hxT
    by_contra hxU
    have hx : x ∈ (∅ : Set (G × W)) := by rw [← hne]; exact Set.mem_inter hxT hxU
    simp at hx
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hT
  obtain ⟨u, hu⟩ := Filter.nonempty_of_mem hU
  have hVsub : V ⊆ S u := by
    intro w hw
    have h1 : (u, w) ∈ (⋃ v : G, ({v} : Set G) ×ˢ S v) := hsubT (hUV ⟨hu, hw⟩)
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp h1
    rw [Set.mem_prod] at hv
    obtain ⟨hv1, hv2⟩ := hv
    rw [Set.mem_singleton_iff] at hv1
    subst hv1
    exact hv2
  have hmem : p.2 ∈ interior (S u) :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hV hVsub)
  rw [hS u] at hmem
  exact hmem

/-- **Baire lemma.** A countable union of closed sets with empty interior has empty interior. -/
theorem interior_eq_empty_iUnion_isClosed {X : Type*} [TopologicalSpace X] [BaireSpace X]
    {ι : Type*} [Countable ι] {F : ι → Set X} (hF : ∀ i, IsClosed (F i))
    (hFi : ∀ i, interior (F i) = ∅) : interior (⋃ i, F i) = ∅ := by
  have hmeag : IsMeagre (⋃ i, F i) :=
    isMeagre_iUnion fun i => (hF i).isNowhereDense_iff.mpr (hFi i) |>.isMeagre
  rw [interior_eq_empty_iff_dense_compl]
  exact dense_of_mem_residual hmeag

end Work.Sard.wp
