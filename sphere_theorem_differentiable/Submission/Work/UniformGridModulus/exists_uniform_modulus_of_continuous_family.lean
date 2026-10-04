import Mathlib
import Submission.Work.OddBound.polygonValue.balancing.continuousRiemannianDist

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.UniformGridModulus

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-- **A uniform modulus of continuity in the second variable, for a continuous two-parameter
family on the compact square.**  If `F : ℝ → ℝ → M` is continuous as a function on `ℝ × ℝ` (for the
manifold topology of `M`) and `ρ > 0`, then there is `δ > 0` such that for every `s ∈ [0,1]` and all
`u, u' ∈ [0,1]` with `|u - u'| < δ` the Riemannian distance between `F s u` and `F s u'` is `< ρ`. -/
theorem exists_uniform_modulus_of_continuous_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {F : ℝ → ℝ → M} (hF : Continuous (fun q : ℝ × ℝ => F q.1 q.2)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s u u' : ℝ, s ∈ Set.Icc (0:ℝ) 1 → u ∈ Set.Icc (0:ℝ) 1 →
      u' ∈ Set.Icc (0:ℝ) 1 → |u - u'| < δ →
      Manifold.riemannianEDist I (F s u) (F s u') < ENNReal.ofReal ρ := by
  -- Mathlib does not provide the instance `IsContinuousRiemannianBundle` from the smooth one.
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have hρ2 : (0 : ℝ) < ρ / 2 := by linarith
  have hρ2e : (0 : ℝ≥0∞) < ENNReal.ofReal (ρ / 2) := ENNReal.ofReal_pos.2 hρ2
  -- the compact square `[0,1] × [0,1]`
  set K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  -- around each point of the square, `F` takes values in the `ρ/2`-ball of its value at that point
  have key : ∀ q : ↥K, ∃ r : ℝ, 0 < r ∧
      ∀ p : ℝ × ℝ, dist p (q : ℝ × ℝ) < r →
        Manifold.riemannianEDist I (F (q : ℝ × ℝ).1 (q : ℝ × ℝ).2) (F p.1 p.2)
          < ENNReal.ofReal (ρ / 2) := by
    intro q
    have hV : {y : M | Manifold.riemannianEDist I (F (q : ℝ × ℝ).1 (q : ℝ × ℝ).2) y
        < ENNReal.ofReal (ρ / 2)} ∈ 𝓝 (F (q : ℝ × ℝ).1 (q : ℝ × ℝ).2) :=
      Submission.EDist.eventually_riemannianEDist_lt (I := I) _ hρ2e
    have hpre : (fun p : ℝ × ℝ => F p.1 p.2) ⁻¹'
        {y : M | Manifold.riemannianEDist I (F (q : ℝ × ℝ).1 (q : ℝ × ℝ).2) y
          < ENNReal.ofReal (ρ / 2)} ∈ 𝓝 (q : ℝ × ℝ) :=
      hF.continuousAt.preimage_mem_nhds hV
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hpre
    exact ⟨r, hr, fun p hp => hball (Metric.mem_ball.mpr hp)⟩
  choose r hr using key
  -- the corresponding balls cover the square
  have hcover : K ⊆ ⋃ q : ↥K, Metric.ball (q : ℝ × ℝ) (r q) := by
    intro p hp
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, Metric.mem_ball_self (hr ⟨p, hp⟩).1⟩
  -- Lebesgue number of this open cover
  obtain ⟨δ, hδ, hLeb⟩ :=
    lebesgue_number_lemma_of_metric hKc (fun q => Metric.isOpen_ball) hcover
  refine ⟨δ, hδ, ?_⟩
  intro s u u' hs hu hu' hlt
  have hsu : (s, u) ∈ K := by
    rw [hK]; exact Set.mem_prod.mpr ⟨hs, hu⟩
  have hsu' : (s, u') ∈ K := by
    rw [hK]; exact Set.mem_prod.mpr ⟨hs, hu'⟩
  obtain ⟨i, hi⟩ := hLeb (s, u) hsu
  -- `(s,u')` lies in the same ball of the cover
  have hmem : (s, u') ∈ Metric.ball (s, u) δ := by
    rw [Metric.mem_ball, Prod.dist_eq, dist_self, max_eq_right (abs_nonneg _), Real.dist_eq,
      abs_sub_comm]
    exact hlt
  have h1 : Manifold.riemannianEDist I (F (i : ℝ × ℝ).1 (i : ℝ × ℝ).2) (F s u)
      < ENNReal.ofReal (ρ / 2) :=
    (hr i).2 (s, u) (Metric.mem_ball.mp (hi (Metric.mem_ball_self hδ)))
  have h2 : Manifold.riemannianEDist I (F (i : ℝ × ℝ).1 (i : ℝ × ℝ).2) (F s u')
      < ENNReal.ofReal (ρ / 2) :=
    (hr i).2 (s, u') (Metric.mem_ball.mp (hi hmem))
  calc Manifold.riemannianEDist I (F s u) (F s u')
      ≤ Manifold.riemannianEDist I (F s u) (F (i : ℝ × ℝ).1 (i : ℝ × ℝ).2)
        + Manifold.riemannianEDist I (F (i : ℝ × ℝ).1 (i : ℝ × ℝ).2) (F s u') :=
        Manifold.riemannianEDist_triangle
    _ = Manifold.riemannianEDist I (F (i : ℝ × ℝ).1 (i : ℝ × ℝ).2) (F s u)
        + Manifold.riemannianEDist I (F (i : ℝ × ℝ).1 (i : ℝ × ℝ).2) (F s u') := by
        rw [Manifold.riemannianEDist_comm (x := F s u) (y := F (i : ℝ × ℝ).1 (i : ℝ × ℝ).2)]
    _ < ENNReal.ofReal (ρ / 2) + ENNReal.ofReal (ρ / 2) := ENNReal.add_lt_add h1 h2
    _ = ENNReal.ofReal ρ := by
        rw [← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ ρ / 2) (by linarith : (0:ℝ) ≤ ρ / 2)]
        congr 1
        ring

end Work.UniformGridModulus
