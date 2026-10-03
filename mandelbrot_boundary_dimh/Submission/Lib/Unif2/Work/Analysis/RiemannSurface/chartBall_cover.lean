import Mathlib
import Submission.Lib.Unif2.RiemannSurface
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.chartBall_open

/-!
# A finite cover of a compact set by open chart balls (item 1 of the shell cover, `NOTES_…` §39.7)

For a compact `K` and an open `U ⊇ K`: finitely many points of `K` (as a `Finset ↥K`, so that the
subtype carries membership in `K ⊆ U`) and radii `ρ i > 0` such that the chart balls
`Submission.chartBall (chartAt ℂ i) ((chartAt ℂ i) i) (ρ i)` cover `K` and each lies inside `U`.

Proof: for `x ∈ U`, `(chartAt ℂ x) '' (U ∩ (chartAt ℂ x).source)` is open and contains
`(chartAt ℂ x) x`; intersecting with the target and applying `Metric.isOpen_iff` gives a radius whose
chart ball lies in `U`.  `IsCompact.elim_finite_subcover` on the subtype `↥K` gives the finite
subcover; indexing by the subtype is what makes the "balls lie inside `U`" clause provable, since every
index is a point of `K`.

Running this on the shells `K_{n+1} \ interior K_n` of
`Submission.SurfaceTopology.exists_compactExhaustion` gives the locally finite family of item 2.
-/

open scoped Topology Manifold

namespace Work.Analysis.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **A chart ball inside a prescribed neighbourhood of its centre.** -/
theorem exists_chartBall_subset_of_mem_isOpen {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ ⊆ U := by
  have hsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hopen : IsOpen ((chartAt ℂ x) '' (U ∩ (chartAt ℂ x).source)) :=
    (chartAt ℂ x).isOpen_image_of_subset_source (hU.inter (chartAt ℂ x).open_source)
      Set.inter_subset_right
  have hmem : (chartAt ℂ x) x
      ∈ (chartAt ℂ x) '' (U ∩ (chartAt ℂ x).source) ∩ (chartAt ℂ x).target :=
    ⟨⟨x, ⟨hx, hsrc⟩, rfl⟩, (chartAt ℂ x).map_source hsrc⟩
  obtain ⟨ρ, hρ, hsub⟩ :=
    (Metric.isOpen_iff.mp (hopen.inter (chartAt ℂ x).open_target)) ((chartAt ℂ x) x) hmem
  refine ⟨ρ, hρ, ?_⟩
  intro y hy
  obtain ⟨hy_src, hy_ball⟩ := hy
  obtain ⟨z, hzU, hz⟩ := (hsub hy_ball).1
  have hyz : y = z := by
    calc y = (chartAt ℂ x).symm ((chartAt ℂ x) y) := ((chartAt ℂ x).left_inv hy_src).symm
      _ = (chartAt ℂ x).symm ((chartAt ℂ x) z) := by rw [← hz]
      _ = z := (chartAt ℂ x).left_inv hzU.2
  rw [hyz]
  exact hzU.1

/-- **A finite cover of a compact set by open chart balls lying inside a prescribed open
neighbourhood.** -/
theorem exists_finite_chartBall_cover {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (t : Finset ↥K) (ρ : X → ℝ), (∀ i ∈ t, 0 < ρ (i : X)) ∧
      K ⊆ ⋃ i ∈ t,
        Submission.chartBall (chartAt ℂ (i : X)) ((chartAt ℂ (i : X)) (i : X)) (ρ (i : X)) ∧
      ∀ i ∈ t,
        Submission.chartBall (chartAt ℂ (i : X)) ((chartAt ℂ (i : X)) (i : X)) (ρ (i : X)) ⊆ U := by
  classical
  let ρ : X → ℝ := fun x =>
    if hx : x ∈ U then Classical.choose (exists_chartBall_subset_of_mem_isOpen hU hx) else 1
  have hρpos : ∀ x : X, x ∈ U → 0 < ρ x := by
    intro x hx
    simp only [ρ, dif_pos hx]
    exact (Classical.choose_spec (exists_chartBall_subset_of_mem_isOpen hU hx)).1
  have hρsub : ∀ x : X, x ∈ U →
      Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) (ρ x) ⊆ U := by
    intro x hx
    simp only [ρ, dif_pos hx]
    exact (Classical.choose_spec (exists_chartBall_subset_of_mem_isOpen hU hx)).2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun i : ↥K => Submission.chartBall (chartAt ℂ (i : X)) ((chartAt ℂ (i : X)) (i : X)) (ρ (i : X)))
    (fun i => isOpen_chartBall _ _ _)
    (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩,
      ⟨mem_chart_source ℂ y, Metric.mem_ball_self (hρpos y (hKU hy))⟩⟩)
  exact ⟨t, ρ, fun i _ => hρpos (i : X) (hKU i.2), ht, fun i _ => hρsub (i : X) (hKU i.2)⟩

end Work.Analysis.RiemannSurface
