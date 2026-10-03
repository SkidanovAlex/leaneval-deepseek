import Mathlib
import Submission.Work.BasinSC.cover_basic

/-!
# Auxiliary topology for `proper_of_covering_LF`

Elementary facts about openness of components, discreteness of fibres of local homeomorphisms,
and path-connectedness of plane domains, used in the proof of `Work.Horn.HB.proper_of_covering_LF`.
-/

namespace Work.Horn.HB

open Set Metric Filter Topology

/-- `D ∩ g ⁻¹' V` is open when `D`, `V` are open and `g` is continuous at every point of `D`. -/
theorem isOpen_inter_preimage_of_continuousAt {g : ℂ → ℂ} {D V : Set ℂ} (hD : IsOpen D)
    (hV : IsOpen V) (hg : ∀ z ∈ D, ContinuousAt g z) : IsOpen (D ∩ g ⁻¹' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hzD, hzV⟩
  exact Filter.inter_mem (hD.mem_nhds hzD) ((hg z hzD).preimage_mem_nhds (hV.mem_nhds hzV))

/-- Near a point of its domain, a local homeomorphism is not locally constant. -/
theorem not_eventually_eq_of_isLocalHomeomorphOn {g : ℂ → ℂ} {s : Set ℂ}
    (hloc : IsLocalHomeomorphOn g s) {z : ℂ} (hz : z ∈ s) :
    ¬ ∀ᶠ u in 𝓝 z, g u = g z := by
  intro hev
  obtain ⟨e, hze, hge⟩ := hloc z hz
  have hge' : ∀ u, g u = e u := fun u => congrFun hge u
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hev
  set U : Set ℂ := Metric.ball z ε ∩ e.source with hU
  have hUopen : IsOpen U := Metric.isOpen_ball.inter e.open_source
  have hzU : z ∈ U := ⟨Metric.mem_ball_self hεpos, hze⟩
  have hUsrc : U ⊆ e.source := Set.inter_subset_right
  have himg : e '' U = {g z} := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      have h1 : g u = g z := hεsub (Metric.mem_ball.mp hu.1)
      rw [← hge' u]
      exact h1
    · rintro rfl
      exact ⟨z, hzU, (hge' z).symm⟩
  have hopen : IsOpen (e '' U) := e.isOpen_image_of_subset_source hUopen hUsrc
  rw [himg] at hopen
  obtain ⟨η, hηpos, hηsub⟩ := Metric.isOpen_iff.mp hopen (g z) (Set.mem_singleton _)
  have hmem : g z + (η / 2 : ℝ) ∈ Metric.ball (g z) η := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    have hnormsq : ‖((η / 2 : ℝ) : ℂ)‖ ^ 2 = (η / 2) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    have hcast : ‖((η / 2 : ℝ) : ℂ)‖ = η / 2 := by
      nlinarith [norm_nonneg ((η / 2 : ℝ) : ℂ)]
    rw [hcast]; linarith
  have h2 := hηsub hmem
  rw [Set.mem_singleton_iff] at h2
  have h3 : ((η / 2 : ℝ) : ℂ) = 0 := by
    have := congrArg (fun w : ℂ => w - g z) h2
    simpa using this
  have h4 : η / 2 = 0 := Complex.ofReal_eq_zero.mp h3
  linarith

/-- **Fibres of a local homeomorphism are discrete.** -/
theorem isDiscrete_fiber_of_isLocalHomeomorphOn {g : ℂ → ℂ} {s : Set ℂ}
    (hloc : IsLocalHomeomorphOn g s) {y : ℂ} :
    IsDiscrete (s ∩ g ⁻¹' {y}) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  rintro z hz
  obtain ⟨e, hze, hge⟩ := hloc z hz.1
  have hge' : ∀ u, g u = e u := fun u => congrFun hge u
  refine ⟨e.source, e.open_source, ?_⟩
  ext w
  constructor
  · rintro ⟨hw, hws, hwy⟩
    have hwy' : g w = y := hwy
    have hzy : g z = y := hz.2
    have h1 : e w = e z := by rw [← hge' w, ← hge' z, hwy', hzy]
    have h2 : w = z := e.injOn hw hze h1
    rw [Set.mem_singleton_iff]
    exact h2
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨hze, hz⟩

/-- A nonempty preconnected, locally path connected space is path connected. -/
theorem pathConnectedSpace_of_preconnected_of_locallyPathConnected (X : Type*)
    [TopologicalSpace X] [PreconnectedSpace X] [LocallyPathConnectedSpace X] (hne : Nonempty X) :
    PathConnectedSpace X := by
  obtain ⟨x⟩ := hne
  rw [pathConnectedSpace_iff_eq]
  refine ⟨x, ?_⟩
  rw [pathComponent_eq_connectedComponent, PreconnectedSpace.connectedComponent_eq_univ]

end Work.Horn.HB
