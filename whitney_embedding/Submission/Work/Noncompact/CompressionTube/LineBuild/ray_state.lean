import Mathlib
import Submission.Work.Noncompact.CompressionTube.LineBuild.centered_chart
import Submission.Work.Noncompact.CompressionTube.LineBuild.arc_separation
import Submission.Work.Noncompact.CompressionTube.LineBuild.stage_piece

/-!
# The state of the line construction

The line inside a canal is built piece by piece: at level `i` the construction has already produced a
piece `P i : ℝ → M` running from the junction `q b (i-1)` to the junction `q b i`, together with

* the chart `c` at the current junction (centred there, with smooth inverse) and the *terminal germ*
  of the piece: inside the chart ball of radius `ρ` the piece is the straight radius in the
  direction `u`;
* the confinement invariants that make the final assembly work: the piece lies in the region
  `D b i`, and it misses the deeper regions `D b m`, `m ≥ i+2` (the "two-shell" separation, which
  makes every *later* piece disjoint from it except at the junction).

`RaySeed` is the data needed before the first piece is built (the base point `b = q b (lev b)`, its
centred chart, a direction and a germ radius); `RayState` is what each step produces and consumes.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology Filter
open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*}

/-- **Chart balls shrink to their centre.**  If `c` is a chart with `c z = 0` and `U` is a
neighbourhood of `z`, then for small `δ > 0` the closed chart ball of radius `δ` lies in `U`. -/
theorem ncChartBall_subset_nhds [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {z : M}
    (hcsrc : z ∈ c.source) (hcz : c z = 0) {U : Set M} (hU : U ∈ nhds z) :
    ∃ δ : ℝ, 0 < δ ∧ c.symm '' Metric.closedBall 0 δ ⊆ U := by
  have h0 : c.symm 0 = z := by rw [← hcz]; exact c.left_inv hcsrc
  have htgt : (0 : EuclideanSpace ℝ (Fin n)) ∈ c.target := by
    rw [← hcz]; exact c.map_source hcsrc
  have hcont : ContinuousAt (⇑c.symm) 0 := c.continuousAt_symm htgt
  have hpre : (⇑c.symm) ⁻¹' U ∈ nhds (0 : EuclideanSpace ℝ (Fin n)) := by
    apply hcont.preimage_mem_nhds
    rwa [h0]
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨δ / 2, by positivity, ?_⟩
  rintro y ⟨v, hv, rfl⟩
  exact hδsub (by
    rw [Metric.mem_ball, dist_zero_right]
    have hv' : ‖v‖ ≤ δ / 2 := by simpa [Metric.mem_closedBall, dist_zero_right] using hv
    linarith)

/-- The data needed to build the *first* piece: the centred chart at the base point, a direction
and a germ radius. -/
structure RaySeed (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M] where
  c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  z : M
  hcsrc : z ∈ c.source
  hcz : c z = 0
  hcsymm : ContMDiffOn (MC n) (MC n) smoothOrder (⇑c.symm) c.target
  u : EuclideanSpace ℝ (Fin n)
  hu : ‖u‖ = 1
  ρ : ℝ
  hρ : 0 < ρ

/-- The state of the construction after the piece at level `i` has been built. -/
structure RayState (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    (W : Set M) (D : ℕ → Set M) where
  /-- the level of the current junction `z` -/
  i : ℕ
  z : M
  /-- the junction reached by the previous piece -/
  zprev : M
  c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  hcsrc : z ∈ c.source
  hcz : c z = 0
  hcsymm : ContMDiffOn (MC n) (MC n) smoothOrder (⇑c.symm) c.target
  /-- the direction of the terminal germ of the piece -/
  u : EuclideanSpace ℝ (Fin n)
  hu : ‖u‖ = 1
  ρ : ℝ
  hρ : 0 < ρ
  P : ℝ → M
  hPsm : ContMDiff MCreal (MC n) smoothOrder P
  hP0 : ∀ t : ℝ, t ≤ 0 → P t = zprev
  hP1 : ∀ t : ℝ, 1 ≤ t → P t = z
  hPinj : Set.InjOn P (Set.Icc (0:ℝ) 1)
  /-- the terminal germ: inside the ball of radius `ρ` the piece is the straight radius in the
  direction `u` -/
  hPgerm : P '' Set.Icc (0:ℝ) 1 ∩ c.symm '' Metric.ball 0 ρ ⊆
    c.symm '' {y : EuclideanSpace ℝ (Fin n) | ∃ s : ℝ, 0 ≤ s ∧ s < ρ ∧ y = s • u}
  /-- confinement: the piece lies in the region one level below its right end (the access part of
  the piece starts at `q b (i-1) ∈ D (i-1) ∖ D i`, while its middle and arrival lie in `D i`) -/
  hmem : P '' Set.Icc (0:ℝ) 1 ⊆ D (i - 1)
  /-- the two-shell separation: the piece misses all *deeper* regions, one level beyond the two
  levels that the confinement `hmem` already controls.  (This is the invariant that makes the
  trace of the chain in the next region a single arc.) -/
  h2sh : ∀ m : ℕ, i + 1 ≤ m → Disjoint (P '' Set.Icc (0:ℝ) 1) (D m)

/-- A unit vector in `ℝ^n`, `n ≥ 1`. -/
theorem exists_unit_vector {n : ℕ} (hn : 1 ≤ n) :
    ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 :=
  ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by
    rw [EuclideanSpace.norm_single]; norm_num⟩

end Work.Noncompact.CompressionTube
