import Mathlib
import Submission.Work.Embedding.exists_unique_closest_point
import Submission.Work.Embedding.local_retraction_model
import Submission.Work.Embedding.chartRepN_adjoint_min

/-!
# Local chart data for the nearest-point map of a compact smooth submanifold

Let `e : M → ℝ^N` be a smooth injective immersion of a compact smooth `n`-manifold, and let
`np : ℝ^N → M` be a nearest-point selection: for `y` with `infDist y (range e) < ε` we have
`dist y (e (np y)) = infDist y (range e)`.

The statement proved here is that near each `e p` the chart-coordinates of `np` are given by a
`C^∞` function: there are an open `O ∋ e p` and a `C^∞` function `η` on `O` with
`η y = (chartAt p) (np y)` and `np y ∈ (chartAt p).source` for all `y ∈ O`.

The proof is a local model computation.  In the chart at `p`, `e` is the map
`ψ = chartRepN e p`, whose derivative at `c p` is injective; the implicit function theorem for the
normal equation `(fderiv ψ u)† (y - ψ u) = 0` (`Work.Embedding.smooth_implicit_function_local`)
produces a `C^∞` solution `η` near `ψ (c p) = e p`.  First-order optimality at a closest point
(`Work.Embedding.chartRepN_adjoint_min`) says exactly that the chart coordinates of any closest
point `q` of `y` satisfy the normal equation, so `η y = c q`; and
(`Work.Embedding.minimizers_eventually_mem`) all closest points of `y` near `e p` lie in the chart
source, at bounded chart distance from `c p`, which is what makes the implicit-function
neighbourhood applicable.  No uniqueness of the closest point is assumed: uniqueness on `O` is a
byproduct.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff
open Topology Metric Filter

set_option linter.unusedVariables false

theorem exists_local_chart_data {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M]
    (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (hinj : Function.Injective e)
    (himm : ∀ x, Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) e x))
    {ε : ℝ} (hεpos : 0 < ε)
    (np : EuclideanSpace ℝ (Fin N) → M)
    (hnp : ∀ y, Metric.infDist y (Set.range e) < ε → dist y (e (np y)) = Metric.infDist y (Set.range e))
    (p : M) :
    ∃ (O : Set (EuclideanSpace ℝ (Fin N))) (η : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n)),
      IsOpen O ∧ e p ∈ O ∧
      (∀ y ∈ O, Metric.infDist y (Set.range e) < ε) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η O ∧
      (∀ y ∈ O, np y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source ∧
        η y = (chartAt (EuclideanSpace ℝ (Fin n)) p) (np y)) := by
  classical
  let c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) p
  let ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N) := Work.Embedding.chartRepN e p
  have hψc : ∀ x ∈ c.source, ψ (c x) = e x := fun x hx => Work.Embedding.chartRepN_chart e p x hx
  have hbase : ψ (c p) = e p := hψc p (mem_chart_source (EuclideanSpace ℝ (Fin n)) p)
  have hctarget : c p ∈ c.target := c.map_source (mem_chart_source (EuclideanSpace ℝ (Fin n)) p)
  -- The implicit function theorem for the normal equation in the chart at `p`.
  obtain ⟨η, O₁, hO₁open, hO₁mem, _hηbase, hηsm, hIFT⟩ :=
    Work.Embedding.smooth_implicit_function_local ψ c.open_target hctarget
      (Work.Embedding.contMDiffOn_chartRepN e he p).contDiffOn
      (Work.Embedding.injective_fderiv_chartRep_infty e he himm p hctarget)
  obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp hIFT
  -- All closest points of points near `e p` lie in the chart source, close to `c p`.
  have hVopen : IsOpen (c.source ∩ c ⁻¹' ball (c p) r) := c.isOpen_inter_preimage isOpen_ball
  have hpV : p ∈ c.source ∩ c ⁻¹' ball (c p) r :=
    ⟨mem_chart_source _ p, mem_ball_self hrpos⟩
  obtain ⟨δ, hδpos, hδ⟩ := Work.Embedding.minimizers_eventually_mem e he hinj p hVopen hpV
  have hρpos : 0 < min δ (min r ε) := lt_min hδpos (lt_min hrpos hεpos)
  have hδε : min δ (min r ε) ≤ ε := le_trans (min_le_right _ _) (min_le_right _ _)
  have hδδ : min δ (min r ε) ≤ δ := min_le_left _ _
  have hδr : min δ (min r ε) ≤ r := le_trans (min_le_right _ _) (min_le_left _ _)
  refine ⟨O₁ ∩ ball (e p) (min δ (min r ε)), η,
    hO₁open.inter isOpen_ball, ?_, ?_, ?_, ?_⟩
  · exact ⟨hbase ▸ hO₁mem, mem_ball_self hρpos⟩
  · intro y hy
    have h3 : dist y (e p) < min δ (min r ε) := mem_ball.mp hy.2
    have h1 : Metric.infDist y (Set.range e) ≤ dist y (e p) :=
      Metric.infDist_le_dist_of_mem (Set.mem_range_self p)
    linarith
  · exact hηsm.mono (fun y hy => hy.1)
  · intro y hy
    have hyball : dist y (e p) < min δ (min r ε) := mem_ball.mp hy.2
    have hyδ : dist y (e p) < δ := lt_of_lt_of_le hyball hδδ
    have hyr : dist y (e p) < r := lt_of_lt_of_le hyball hδr
    have hyε : Metric.infDist y (Set.range e) < ε := by
      have h1 : Metric.infDist y (Set.range e) ≤ dist y (e p) :=
        Metric.infDist_le_dist_of_mem (Set.mem_range_self p)
      linarith
    -- `np y` is a closest point of `y`
    have hnpmin : dist y (e (np y)) = Metric.infDist y (Set.range e) := hnp y hyε
    have hmin : ∀ z : M, dist y (e (np y)) ≤ dist y (e z) := fun z => by
      rw [hnpmin]; exact Metric.infDist_le_dist_of_mem (Set.mem_range_self z)
    have hV := hδ y hyδ (np y) hnpmin
    have hsrc : np y ∈ c.source := hV.1
    have hcq : dist (c (np y)) (c p) < r := mem_ball.mp hV.2
    -- first-order optimality: the chart coordinates solve the normal equation
    have hadj : (fderiv ℝ ψ (c (np y))).adjoint (y - e (np y)) = 0 :=
      Work.Embedding.chartRepN_adjoint_min e he hsrc hmin
    -- the implicit-function neighbourhood applies and identifies the chart coordinates
    have hz_mem : (y, c (np y)) ∈ ball ((ψ (c p), c p)) r := by
      rw [Metric.mem_ball, Prod.dist_eq]
      refine max_lt ?_ hcq
      rw [hbase]; exact hyr
    have hIFT_at := hrsub hz_mem
    simp only [Set.mem_setOf_eq] at hIFT_at
    rw [hψc (np y) hsrc] at hIFT_at
    exact ⟨hsrc, hIFT_at.mp hadj⟩

end Work.Drive.N2
