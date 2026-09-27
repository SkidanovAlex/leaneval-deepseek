import Mathlib
import Submission.Work.Drive.chartSourceReality
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.ChartBridge

namespace Work.Drive

/-- **A finite chart-per-piece cover of the base triple locus.**

For a jointly continuous family `G` of triples of chains into a charted `4`-manifold, there is a finite
family of pairs `(p i, K i, δ i)` such that the compact sets `K i` cover the base triple locus
(`meet3` of `G 0` inside the nine-box) by interiors, and on each `K i`, for every parameter of norm
`< δ i`, all three chains take their values in the source of the chart at `p i`.

This is the cover that the *localized* (chart-per-piece) parametric Sard consumes: per piece the chart
`chr (p i)` contains all the values appearing on that piece, while no single chart contains them all
(the canonical chart of the capping space has an opaque source, see
`Submission/Work/Drive/CHART_SOURCE_OPACITY.md`).  `p i` is intended to be the *base value* at the point
`y i` whose compact neighbourhood `K i` is; the last conjunct of the intended proof therefore is
`p i = G 0 0 (bPartC 0 (y i))`, which the caller does not need in the statement. -/
theorem baseCover
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {m : ℕ} (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hcont : ∀ k : Fin 3, Continuous
      fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2) :
    ∃ (ι : Type) (_ : Fintype ι) (K : ι → Set (EuclideanSpace ℝ (Fin 9)))
      (δ : ι → ℝ) (p : ι → M),
      (∀ i, IsCompact (K i)) ∧ (∀ i, 0 < δ i) ∧
      (∀ y₀, y₀ ∈ Submission.Drive.unitBox 8 → Work.Drive.TParity.meet3 (G 0) y₀ →
        ∃ i, y₀ ∈ interior (K i)) ∧
      (∀ (i : ι) (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)),
        ‖t‖ < δ i → y ∈ K i → ∀ k : Fin 3,
          G t k (Work.Drive.TParity.bPartC k y) ∈ (Work.Drive.chr (p i)).source) := by
  classical
  -- the base triple locus
  set B : Set (EuclideanSpace ℝ (Fin 9)) :=
    {y | y ∈ Submission.Drive.unitBox 8 ∧ Work.Drive.TParity.meet3 (G 0) y} with hB
  have hBcomp : IsCompact B := by
    rw [hB]
    refine (isCompact_unitBox 8).of_isClosed_subset ?_ (fun y hy => hy.1)
    exact (isClosed_unitBox 8).inter (isClosed_meet3 (fun k =>
      (hcont k).comp (continuous_const.prodMk continuous_id)))
  -- at each base point: a compact neighbourhood and a parameter radius on which the chart at the
  -- base value contains all the values of the three chains
  have hpt : ∀ y : B, ∃ (K : Set (EuclideanSpace ℝ (Fin 9))) (ε : ℝ), IsCompact K ∧ 0 < ε ∧
      (y : EuclideanSpace ℝ (Fin 9)) ∈ interior K ∧
      (∀ (t : EuclideanSpace ℝ (Fin m)) (y' : EuclideanSpace ℝ (Fin 9)), ‖t‖ < ε → y' ∈ K →
        ∀ k : Fin 3, G t k (Work.Drive.TParity.bPartC k y') ∈
          (Work.Drive.chr (G 0 0 (Work.Drive.TParity.bPartC 0
            (y : EuclideanSpace ℝ (Fin 9))))).source) := by
    intro y
    obtain ⟨K, ε, hK, hε, hint, hres⟩ :=
      exists_compact_nhds_of_base_point (G := G) hcont y.2.2
    exact ⟨K, ε, hK, hε, hint, fun t y' ht hy k => by
      simpa only [Work.Drive.chr] using hres t y' ht hy k⟩
  choose K ε hK hε hint hres using hpt
  -- a finite subcover of the base locus by the interiors
  obtain ⟨t, ht⟩ := hBcomp.elim_finite_subcover (fun i : B => interior (K i))
      (fun i => isOpen_interior) (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hint ⟨y, hy⟩⟩)
  refine ⟨{i : B // i ∈ t}, inferInstance, (fun i => K i.1), (fun i => ε i.1),
    (fun i => G 0 0 (Work.Drive.TParity.bPartC 0 (i.1 : EuclideanSpace ℝ (Fin 9)))),
    fun i => hK i.1, fun i => hε i.1, ?_, ?_⟩
  · intro y₀ hybox hm
    have hyB : y₀ ∈ B := ⟨hybox, hm⟩
    obtain ⟨i, hit, hyi⟩ := Set.mem_iUnion₂.mp (ht hyB)
    exact ⟨⟨i, hit⟩, hyi⟩
  · intro i t y ht' hy k
    exact hres i.1 t y ht' hy k

end Work.Drive
