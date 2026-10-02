import Mathlib
import Submission.Work.Tubular.Foot

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# The normal total space is closed, and the disc bundle is compact

`NormalTotal E = {p : V.pt × ℝ^N | p.2 ∈ ν_{p.1}}` is a closed subset of the product: in a chart `i`,
`w ∈ ν_x` is the equation `A_x† w = 0` (`Work.Tubular.tangentFrame_adjoint_eq_zero_iff`), whose
left-hand side is continuous in `(x,w)` on the chart's source.  Since `V.pt` is compact and
`ν_x ⊆ ℝ^N` is closed over each compact piece, the closed `ε`-disc bundle
`NormalDiscSub E ε` is compact — the topological input of the Pontryagin–Thom collapse.
-/

open scoped Manifold ContDiff Topology InnerProduct
open Function Filter

namespace Work.Tubular

open Work.ThomBordism Work.ThomBordism.PontryaginThom

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The tangent frame depends continuously on the point, near a given point of `V`. -/
theorem continuousAt_tangentFrame (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt)
    {x₀ : V.pt} (hx : x₀ ∈ i.1.source) (y : Euc (8 + k)) :
    ContinuousAt (fun p : V.pt × Euc (8 + k) => tangentFrame E i p.1) (x₀, y) := by
  have hd : ContDiffAt ℝ ∞ (fun τ : Euc 8 => tauFrame E i τ) (i.1 x₀) :=
    (contDiffOn_tauFrame E i).contDiffAt (i.1.open_target.mem_nhds (i.1.map_source hx))
  have hB : Tendsto (fun z : V.pt => i.1 z) (𝓝 x₀) (𝓝 (i.1 x₀)) := i.1.continuousAt hx
  have hC : Tendsto (fun τ : Euc 8 => tauFrame E i τ) (𝓝 (i.1 x₀))
      (𝓝 (tauFrame E i (i.1 x₀))) := hd.continuousAt
  have hD : Tendsto (fun p : V.pt × Euc (8 + k) => p.1) (𝓝 (x₀, y)) (𝓝 x₀) :=
    continuousAt_fst
  exact (hC.comp hB).comp hD

/-- The scalar function `p ↦ ⟪p.2, A_{p.1} v⟫` is continuous near a point of the chart. -/
theorem continuousAt_inner_tangentFrame (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt)
    {x₀ : V.pt} (hx : x₀ ∈ i.1.source) (y : Euc (8 + k)) (v : Euc 8) :
    ContinuousAt (fun p : V.pt × Euc (8 + k) => inner ℝ p.2 ((tangentFrame E i p.1) v))
      (x₀, y) := by
  have h1 := continuousAt_tangentFrame E i hx y
  exact continuousAt_snd.inner (h1.clm_apply continuousAt_const)

/-- **The normal total space is closed** in `V.pt × ℝ^N`: `p.2 ∈ ν_{p.1}` is a closed condition. -/
theorem isClosed_normalGraph (E : EmbeddingData V (8 + k)) :
    IsClosed {p : V.pt × Euc (8 + k) | p.2 ∈ normalSpace E p.1} := by
  refine isClosed_of_closure_subset fun x hx => ?_
  set i := chartAtIdx x.1 with hi
  have hxs : x.1 ∈ i.1.source := mem_chart_source (Euc 8) x.1
  have hzero : ∀ v : Euc 8, inner ℝ x.2 ((tangentFrame E i x.1) v) = 0 := by
    intro v
    by_contra hne
    have hc : inner ℝ x.2 ((tangentFrame E i x.1) v) ≠ 0 := hne
    have hpos : 0 < |inner ℝ x.2 ((tangentFrame E i x.1) v)| := abs_pos.mpr hc
    have hball : Metric.ball (inner ℝ x.2 ((tangentFrame E i x.1) v))
        (|inner ℝ x.2 ((tangentFrame E i x.1) v)| / 2) ∈
        𝓝 (inner ℝ x.2 ((tangentFrame E i x.1) v)) :=
      Metric.ball_mem_nhds _ (by positivity)
    have hmem : (fun p : V.pt × Euc (8 + k) =>
        inner ℝ p.2 ((tangentFrame E i p.1) v)) ⁻¹'
        Metric.ball (inner ℝ x.2 ((tangentFrame E i x.1) v))
          (|inner ℝ x.2 ((tangentFrame E i x.1) v)| / 2) ∈ 𝓝 x :=
      (continuousAt_inner_tangentFrame E i hxs x.2 v).preimage_mem_nhds hball
    have hU : {p : V.pt × Euc (8 + k) | p.1 ∈ i.1.source} ∈ 𝓝 x :=
      (i.1.open_source.preimage continuous_fst).mem_nhds hxs
    obtain ⟨p, hp⟩ := (mem_closure_iff_nhds.mp hx _
      (Filter.inter_mem hU hmem))
    obtain ⟨hp1, hpG⟩ := hp
    obtain ⟨hpU, hpB⟩ := hp1
    have hpk : (tangentFrame E i p.1).adjoint p.2 = 0 :=
      (tangentFrame_adjoint_eq_zero_iff E i hpU p.2).mpr hpG
    have hkey : inner ℝ p.2 ((tangentFrame E i p.1) v) = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_left (tangentFrame E i p.1) v p.2, hpk,
        inner_zero_left]
    have hd : dist (inner ℝ p.2 ((tangentFrame E i p.1) v))
        (inner ℝ x.2 ((tangentFrame E i x.1) v))
        < |inner ℝ x.2 ((tangentFrame E i x.1) v)| / 2 := Metric.mem_ball.mp hpB
    rw [Real.dist_eq, hkey, zero_sub, abs_neg] at hd
    linarith [hpos, hd]
  have hker : (tangentFrame E i x.1).adjoint x.2 = 0 := by
    have h2 : inner ℝ ((tangentFrame E i x.1).adjoint x.2)
        ((tangentFrame E i x.1).adjoint x.2) = 0 := by
      rw [ContinuousLinearMap.adjoint_inner_left (tangentFrame E i x.1)
        ((tangentFrame E i x.1).adjoint x.2) x.2]
      exact hzero _
    exact inner_self_eq_zero.mp h2
  exact (tangentFrame_adjoint_eq_zero_iff E i hxs x.2).mp hker

/-- **The closed `ε`-disc bundle is compact**, as a set of the product. -/
theorem isCompact_discGraph (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    IsCompact {p : V.pt × Euc (8 + k) | p.2 ∈ normalSpace E p.1 ∧ ‖p.2‖ ≤ ε} :=
  IsCompact.of_isClosed_subset
    ((isCompact_univ (X := V.pt)).prod (isCompact_closedBall (0 : Euc (8 + k)) ε))
    ((isClosed_normalGraph E).inter (isClosed_le continuous_snd.norm continuous_const))
    (fun p hp => ⟨Set.mem_univ _, by simpa using hp.2⟩)

/-- The closed `ε`-disc bundle, as a set of the normal total space, is compact. -/
theorem isCompact_normalClosedDiscSet (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    IsCompact {p : NormalTotal E | normalNorm E p ≤ ε} := by
  rw [Subtype.isCompact_iff]
  convert isCompact_discGraph E ε using 1
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, by simpa [normalNorm] using hp⟩
  · rintro ⟨hq, hle⟩
    exact ⟨⟨q, hq⟩, by simpa [normalNorm] using hle, rfl⟩

/-- **The closed `ε`-disc bundle of the normal bundle is compact.** -/
theorem compactSpace_normalDiscSub (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    CompactSpace (NormalDiscSub E ε) := by
  have h : IsCompact {p : NormalTotal E | normalNorm E p ≤ ε} :=
    isCompact_normalClosedDiscSet E ε
  rw [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ, Subtype.range_coe_subtype]
  simpa using h

end

end Work.Tubular
