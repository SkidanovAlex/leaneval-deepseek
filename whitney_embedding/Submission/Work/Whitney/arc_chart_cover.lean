import Mathlib

/-!
# A finite chart cover of a curve

`Work.Whitney.arc_chart_cover`: a continuous path in a charted space is covered by finitely many
chart-source neighbourhoods of points of the path.  This is the finite cover on which the
finger-level assembly of the Whitney collar (`Submission/Work/Whitney/CutPush/TubeData.lean`,
`Work.Whitney.CutPush.exists_tube_data_of_chart`) is built: the per-chart tubular data are glued
along the arc, one chart at a time.

The proof is the standard compactness argument, in the form in which the gluing consumes it: at each
point `x` of the interval a radius `ρ` (of a ball inside the target of the chart at `γ x`) and a
radius `δ` (of an interval around `x` on which the three properties hold) are produced from the
continuity of `s ↦ chartAt (γ x) (γ s)`; the intervals `ball x δ` cover the compact `Icc 0 1`, and a
finite subcover gives the parameters `t i` and radii `ρ i`.
-/

open scoped Topology
open Set Metric

set_option linter.unusedVariables false

namespace Work.Whitney

/-- **A finite chart cover of a curve.**  A continuous path in a charted space is covered by
finitely many chart-source neighbourhoods of points of the path: there are finitely many parameters
`t i ∈ [0,1]` and radii `ρ i > 0` such that for every `s ∈ [0,1]` the point `γ s` lies in the source
of the chart at `γ (t i)` for some `i`, its image under that chart lies in the ball of radius `ρ i`
around the image of `γ (t i)`, and that ball is contained in the chart's target. -/
theorem arc_chart_cover {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (γ : ℝ → M) (hγ : Continuous γ) :
    ∃ (N : ℕ) (hN : 0 < N) (t : Fin N → ℝ) (ρ : Fin N → ℝ),
      (∀ i, 0 < ρ i) ∧ (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ i : Fin N,
        γ s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))).source ∧
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))) (γ (t i))) (ρ i) ⊆
          (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))).target ∧
        (chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))) (γ s) ∈
          Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ (t i))) (γ (t i))) (ρ i) := by
  classical
  -- ## local data at every point of the interval
  have hloc : ∀ x : Set.Icc (0 : ℝ) 1, ∃ (ρ δ : ℝ), 0 < ρ ∧ 0 < δ ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, |s - x.val| < δ →
        γ s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ x.val)).source ∧
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ x.val)) (γ x.val)) ρ ⊆
          (chartAt (EuclideanSpace ℝ (Fin n)) (γ x.val)).target ∧
        (chartAt (EuclideanSpace ℝ (Fin n)) (γ x.val)) (γ s) ∈
          Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ x.val)) (γ x.val)) ρ := by
    intro x
    set c := chartAt (EuclideanSpace ℝ (Fin n)) (γ x.val) with hc
    have hmem : c (γ x.val) ∈ c.target := c.map_source (mem_chart_source _ _)
    obtain ⟨ρ, hρpos, hball⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds hmem)
    have hcx : ContinuousAt (fun s : ℝ => c (γ s)) x.val :=
      (c.continuousOn_toFun.continuousAt
        (c.open_source.mem_nhds (mem_chart_source _ _))).comp hγ.continuousAt
    have hsrc : ∀ᶠ s in 𝓝 x.val, γ s ∈ c.source :=
      hγ.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds (mem_chart_source _ _))
    have htb : ∀ᶠ s in 𝓝 x.val, c (γ s) ∈ Metric.ball (c (γ x.val)) ρ :=
      hcx.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by
        rw [Metric.mem_ball, dist_self]; exact hρpos))
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (hsrc.and htb)
    refine ⟨ρ, δ, hρpos, hδpos, fun s _hs hsδ => ⟨?_, hball, ?_⟩⟩
    · exact (hδsub (by rw [Metric.mem_ball, Real.dist_eq]; exact hsδ)).1
    · exact (hδsub (by rw [Metric.mem_ball, Real.dist_eq]; exact hsδ)).2
  choose ρ δ hρpos hδpos hprop using hloc
  -- ## the finite subcover of the compact interval
  obtain ⟨T, hT⟩ := isCompact_Icc.elim_finite_subcover
    (fun x : Set.Icc (0 : ℝ) 1 => Metric.ball x.val (δ x)) (fun _ => Metric.isOpen_ball)
    (fun s hs => Set.mem_iUnion.mpr ⟨⟨s, hs⟩, by
      rw [Metric.mem_ball, dist_self]
      exact hδpos ⟨s, hs⟩⟩)
  -- ## the parameters of the cover
  have hcard : 0 < T.card := by
    obtain ⟨x, hxT, -⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_Icc.mpr ⟨le_refl 0, zero_le_one⟩))
    exact Finset.card_pos.mpr ⟨x, hxT⟩
  refine ⟨T.card, hcard,
    fun i => (((T.equivFin.symm i : {x // x ∈ T}) : Set.Icc (0 : ℝ) 1)).val,
    fun i => ρ ((T.equivFin.symm i : {x // x ∈ T}) : Set.Icc (0 : ℝ) 1),
    fun i => hρpos _, fun i => (((T.equivFin.symm i : {x // x ∈ T}) :
      Set.Icc (0 : ℝ) 1)).property, fun s hs => ?_⟩
  obtain ⟨x, hxT, hsx⟩ := Set.mem_iUnion₂.mp (hT hs)
  have hdist : |s - x.val| < δ x := by
    rw [Metric.mem_ball, Real.dist_eq] at hsx
    exact hsx
  have hprop' := hprop x s hs hdist
  have hsub : ((T.equivFin.symm (T.equivFin ⟨x, hxT⟩) : {y // y ∈ T}) :
      Set.Icc (0 : ℝ) 1) = x := by
    rw [Equiv.symm_apply_apply]
  refine ⟨T.equivFin ⟨x, hxT⟩, ?_, ?_, ?_⟩
  · simp only []
    rw [hsub]
    exact hprop'.1
  · simp only []
    rw [hsub]
    exact hprop'.2.1
  · simp only []
    rw [hsub]
    exact hprop'.2.2
/-- **The crossing pieces.**  From the finite chart cover of the arc one reads off two pieces — one
for each end of the arc, hence for each of the two crossing points `p₂ = γ₂ 0` and `q₂ = γ₂ 1` — in
whose chart-source neighbourhoods those points lie.  (The two indices may coincide; then a single
piece carries both crossings, which the construction allows.)

These are the pieces on which the amplitudes have to be non-zero: every other piece of the cover
carries the zero amplitude and therefore acts trivially on the target
(`Work.Whitney.CutPush.slabPush_eq_self_of_vanishes`), and the crossings themselves must be moved to
give the non-attainment of the double-point values. -/
theorem exists_crossing_pieces {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (γ₂ : ℝ → M) (hγ₂ : Continuous γ₂) (p₂ q₂ : M) (hp : γ₂ 0 = p₂) (hq : γ₂ 1 = q₂) :
    ∃ (N : ℕ) (hN : 0 < N) (t : Fin N → ℝ) (ρ : Fin N → ℝ) (i₀ i₁ : Fin N),
      (∀ i, 0 < ρ i) ∧
      p₂ ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ₂ (t i₀))).source ∧
      (chartAt (EuclideanSpace ℝ (Fin n)) (γ₂ (t i₀))) p₂ ∈
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ₂ (t i₀))) (γ₂ (t i₀))) (ρ i₀) ∧
      q₂ ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (γ₂ (t i₁))).source ∧
      (chartAt (EuclideanSpace ℝ (Fin n)) (γ₂ (t i₁))) q₂ ∈
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (γ₂ (t i₁))) (γ₂ (t i₁))) (ρ i₁) := by
  obtain ⟨N, hN, t, ρ, hρ, _ht, hcov⟩ := arc_chart_cover (n := n) γ₂ hγ₂
  obtain ⟨i₀, hs₀, _hb₀, himg₀⟩ :=
    hcov 0 (Set.mem_Icc.mpr ⟨le_refl (0 : ℝ), zero_le_one⟩)
  obtain ⟨i₁, hs₁, _hb₁, himg₁⟩ :=
    hcov 1 (Set.mem_Icc.mpr ⟨zero_le_one, le_refl (1 : ℝ)⟩)
  exact ⟨N, hN, t, ρ, i₀, i₁, hρ, hp ▸ hs₀, hp ▸ himg₀, hq ▸ hs₁, hq ▸ himg₁⟩

end Work.Whitney
