import Submission.FundSol


/-!
# A chart cover of an arbitrary smooth curve

`Submission.CurveCover` provides `exists_partition_chart_coord_smooth` and the structure
`SmoothCurveCover`: a chart cover of a `C^∞` curve `γ` on `[a,b]` (partition, charts, rooms) on
which the chart coordinates of `γ` and of the chart velocity `deriv (chartCoord)` are `C^∞`.

This is the curve-level analogue of `Submission.ParallelGlobal.GeodesicCover` (which requires the
geodesic equation) and is the carrier of the parallel transport along an arbitrary smooth curve
(Roadmap §115.5, Step A).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.JacobiTensor
open Submission.Jacobi

namespace Submission.CurveCover

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]

/-! ## §1 A chart partition of a smooth curve -/

/-- **A chart partition of a smooth curve.**  For a curve that is `C^∞` on an open set containing
`[a,b]`, there is a partition `a = c 0 < ⋯ < c N = b`, charts `x k` and open intervals
`Ioo (A k) (B k)` containing `[c k, c (k+1)]` on which the curve stays in the chart source and the
chart coordinates are `C^∞`. -/
theorem exists_partition_chart_coord_smooth
    {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {a b : ℝ} (hab : a ≤ b) (hVab : Icc a b ⊆ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) :
    ∃ (N : ℕ) (c : ℕ → ℝ) (x : ℕ → M) (A B : ℕ → ℝ),
      c 0 = a ∧ c N = b ∧ (∀ k, k < N → c k < c (k + 1)) ∧
      (∀ k, k < N → A k < c k ∧ c (k + 1) < B k) ∧
      (∀ k, k < N → ∀ t, t ∈ Ioo (A k) (B k) → γ t ∈ (chartAt H (x k)).source) ∧
      (∀ k, k < N → ContDiffOn ℝ ∞ (fun t : ℝ => (extChartAt I (x k)) (γ t)) (Ioo (A k) (B k))) := by
  classical
  -- the local chart datum at every point of `[a,b]`
  have hloc : ∀ s : ℝ, ∃ (x : M) (η : ℝ), s ∈ Icc a b → 0 < η ∧
      Ioo (s - η) (s + η) ⊆ V ∧
      (∀ t ∈ Ioo (s - η) (s + η), γ t ∈ (chartAt H x).source) ∧
      ContDiffOn ℝ ∞ (fun t : ℝ => (extChartAt I x) (γ t)) (Ioo (s - η) (s + η)) := by
    intro s
    by_cases hs : s ∈ Icc a b
    · have hsV : s ∈ V := hVab hs
      have hcont : ContinuousAt γ s := hγ.continuousOn.continuousAt (hV.mem_nhds hsV)
      have hchart : ∀ᶠ t in 𝓝 s, γ t ∈ (chartAt H (γ s)).source :=
        hcont.preimage_mem_nhds
          ((chartAt H (γ s)).open_source.mem_nhds (mem_chart_source H (γ s)))
      obtain ⟨r, hrpos, hrsub⟩ :=
        Metric.mem_nhds_iff.mp (hchart.and (hV.mem_nhds hsV))
      set η : ℝ := r / 2 with hηdef
      have hη : 0 < η := by rw [hηdef]; linarith
      have hηr : η < r := by rw [hηdef]; linarith
      have hball : Ioo (s - η) (s + η) ⊆ Metric.ball s r := by
        intro t ht
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        rw [mem_Ioo] at ht
        exact ⟨by linarith [ht.1, hηr], by linarith [ht.2, hηr]⟩
      have hsubV : Ioo (s - η) (s + η) ⊆ V := fun t ht => (hrsub (hball ht)).2
      have hsubsrc : ∀ t ∈ Ioo (s - η) (s + η), γ t ∈ (chartAt H (γ s)).source :=
        fun t ht => (hrsub (hball ht)).1
      refine ⟨γ s, η, fun _ => ⟨hη, hsubV, hsubsrc, ?_⟩⟩
      have hγ' : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (s - η) (s + η)) := hγ.mono hsubV
      exact Submission.SecondVarGlobal.contDiffOn_chartCoord (I := I)
        (z₀ := γ s) hγ' hsubsrc
    · exact ⟨γ a, (1 : ℝ), fun h => absurd h hs⟩
  choose x η hη using hloc
  -- the induced open cover of `[a,b]`
  have hcov : Icc a b ⊆ ⋃ s : {s : ℝ // s ∈ Icc a b}, Ioo ((s : ℝ) - η s) ((s : ℝ) + η s) := by
    intro t ht
    refine Set.mem_iUnion.mpr ⟨⟨t, ht⟩, ?_⟩
    simp only [Set.mem_Ioo]
    exact ⟨by linarith [(hη t ht).1], by linarith [(hη t ht).1]⟩
  obtain ⟨sf, hsf⟩ := isCompact_Icc.elim_finite_subcover
    (fun s : {s : ℝ // s ∈ Icc a b} => Ioo ((s : ℝ) - η s) ((s : ℝ) + η s))
    (fun _ => isOpen_Ioo) hcov
  -- the subordinate partition
  obtain ⟨N, c, hc0, hcN, hmono, hpiece⟩ :=
    Commons.Topology.Order.exists_partition_subordinate_Icc
      (U := fun i : {s : {s : ℝ // s ∈ Icc a b} // s ∈ sf} =>
        Ioo (((i : {s : ℝ // s ∈ Icc a b}) : ℝ) - η i) (((i : {s : ℝ // s ∈ Icc a b}) : ℝ) + η i))
      (fun _ => isOpen_Ioo) hab (by
        intro t ht
        obtain ⟨s, hst, hts⟩ := Set.mem_iUnion₂.mp (hsf ht)
        exact Set.mem_iUnion.mpr ⟨⟨s, hst⟩, hts⟩)
  have hex : ∀ k : ℕ, ∃ i : {s : {s : ℝ // s ∈ Icc a b} // s ∈ sf},
      k < N → Icc (c k) (c (k + 1)) ⊆
        Ioo (((i : {s : ℝ // s ∈ Icc a b}) : ℝ) - η i)
          (((i : {s : ℝ // s ∈ Icc a b}) : ℝ) + η i) := by
    intro k
    by_cases hk : k < N
    · obtain ⟨i, hi⟩ := hpiece k hk
      exact ⟨i, fun _ => hi⟩
    · have hsne : sf.Nonempty := by
        obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp (hsf (left_mem_Icc.mpr hab : a ∈ Icc a b))
        exact ⟨i, hi⟩
      obtain ⟨t₀, ht₀⟩ := hsne
      exact ⟨⟨t₀, ht₀⟩, fun h => absurd h hk⟩
  choose w hw using hex
  refine ⟨N, c, fun k => x (w k).val.val, fun k => ((w k).val.val : ℝ) - η (w k).val,
    fun k => ((w k).val.val : ℝ) + η (w k).val, hc0, hcN, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact hmono k hk
  · -- the local interval contains the piece
    intro k hk
    have h := hw k hk
    exact ⟨(Set.mem_Ioo.mp (h (left_mem_Icc.mpr (hmono k hk).le))).1,
      (Set.mem_Ioo.mp (h (right_mem_Icc.mpr (hmono k hk).le))).2⟩
  · -- the source condition
    intro k hk t ht
    exact (hη (w k).val (w k).val.property).2.2.1 t ht
  · -- `C^∞` of the chart coordinates
    intro k hk
    exact (hη (w k).val (w k).val.property).2.2.2


/-! ## §2 The smooth curve cover -/

/-- **A smooth curve cover**: a chart cover of a `C^∞` curve on `[a,b]` — the partition, the charts
and the rooms as in `ParallelGlobal.GeodesicCover`, but with the *geodesic* equation replaced by the
smoothness data of the coordinate curve and of its velocity.  This is the structure that carries the
parallel transport along an arbitrary smooth curve (Roadmap §115.5, Step A). -/
structure SmoothCurveCover (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (γ : ℝ → M) (a b : ℝ) where
  N : ℕ
  c : ℕ → ℝ
  x : ℕ → M
  A : ℕ → ℝ
  B : ℕ → ℝ
  c_zero : c 0 = a
  c_last : c N = b
  mono : ∀ k, k < N → c k < c (k + 1)
  room : ∀ k, k < N → A k < c k ∧ c (k + 1) < B k
  src : ∀ k, k < N → ∀ t ∈ Set.Ioo (A k) (B k), γ t ∈ (chartAt H (x k)).source
  smooth : ∀ k, k < N → ContDiffOn ℝ ∞ (fun t : ℝ => (extChartAt I (x k)) (γ t))
    (Set.Ioo (A k) (B k))
  smoothVel : ∀ k, k < N → ContDiffOn ℝ ∞
    (fun t : ℝ => deriv (fun s : ℝ => (extChartAt I (x k)) (γ s)) t) (Set.Ioo (A k) (B k))

variable {γ : ℝ → M} {a b : ℝ}

/-- The derivative of a `C^∞` function on an open set is `C^∞`. -/
theorem contDiffOn_deriv_of_isOpen {u : ℝ → E} {s : Set ℝ} (hs : IsOpen s)
    (hu : ContDiffOn ℝ ∞ u s) : ContDiffOn ℝ ∞ (deriv u) s := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ u) s :=
    hu.fderiv_of_isOpen hs (le_of_eq (by simp))
  refine (h1.clm_apply (contDiffOn_const (c := (1 : ℝ)))).congr (fun x _ => ?_)
  exact (fderiv_apply_one_eq_deriv).symm

/-- **The smooth curve cover exists** for any `C^∞` curve. -/
theorem exists_smoothCurveCover (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {V : Set ℝ} (hV : IsOpen V) (hab : a ≤ b) (hVab : Icc a b ⊆ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) : Nonempty (SmoothCurveCover cov γ a b) := by
  obtain ⟨N, c, x, A, B, hc0, hcN, hmono, hroom, hsrc, hsm⟩ :=
    exists_partition_chart_coord_smooth (I := I) hV hab hVab hγ
  exact ⟨{ N := N, c := c, x := x, A := A, B := B, c_zero := hc0, c_last := hcN, mono := hmono, room := hroom, src := hsrc, smooth := hsm, smoothVel := fun k hk => contDiffOn_deriv_of_isOpen (isOpen_Ioo) (hsm k hk) }⟩

end

end Submission.CurveCover
