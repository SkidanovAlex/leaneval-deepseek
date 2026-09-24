import Mathlib
import Submission.RiemannSurface
import Submission.Work.Modulus.puncturedConnected
import Submission.Work.SimplyConnected.ABS.isPreconnected_diff_chartClosedBall

namespace Work.Analysis.RiemannSurface

open Set Metric

/-!
# The hull condition for a chart annulus

This file proves `Work.Analysis.RiemannSurface.chartAnnulus_hullCondition`, the concrete
instance of the hull condition required by the Behnke--Stein interface
`Work.Analysis.RiemannSurface.PuncturedGlobalApproximation`.

On a non-compact connected Riemann surface `X`, the compact "chart annulus"
`A = chartClosedBall c a r' \ chartBall c a r` (with `c = chartAt ℂ x₀`, `a = c x₀`,
`0 < r < r'`) cuts the punctured surface `X \ {x₀}` into exactly two connected components:

* the punctured open chart ball `chartBall c a r \ {x₀}`, whose closure contains `x₀`;
* the complement `X \ chartClosedBall c a r'` of the closed chart disc, which is
  preconnected (it is `univ \ chartClosedBall c a r'`, the case `Ω = univ` of
  `Work.SimplyConnected.ABS.isPreconnected_diff_chartClosedBall`) and whose closure
  fails to be compact, because `X` would otherwise be the union of the two compact
  sets `chartClosedBall c a r'` and `closure (X \ chartClosedBall c a r')`.

Consequently every relatively compact connected component of `X \ {x₀}` avoiding `A`
contains `x₀` in its closure.
-/

section ChartBallImage

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The open chart ball is the image of the Euclidean ball under the inverse chart, provided
the Euclidean ball lies in the chart target (so that no junk values appear). -/
theorem chartBall_eq_image_of_subset {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hsub : Metric.ball a ρ ⊆ c.target) :
    Submission.chartBall c a ρ = c.symm '' Metric.ball a ρ := by
  ext x
  rw [Submission.mem_chartBall]
  constructor
  · rintro ⟨hx, hcx⟩
    exact ⟨c x, hcx, c.left_inv hx⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨c.map_target (hsub hz), by rw [c.right_inv (hsub hz)]; exact hz⟩

/-- Puncturing the open chart ball: `chartBall c a r \ {x₀}` is the image of the punctured
Euclidean ball `ball a r \ {a}` when `a = c x₀`. -/
theorem chartBall_sdiff_singleton_eq_image {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {r : ℝ}
    {x₀ : X} (hsub : Metric.ball a r ⊆ c.target) (ha : a = c x₀) (hx₀ : x₀ ∈ c.source) :
    Submission.chartBall c a r \ {x₀} = c.symm '' (Metric.ball a r \ {a}) := by
  have hx₀' : c.symm a = x₀ := by rw [ha, c.left_inv hx₀]
  rw [chartBall_eq_image_of_subset hsub, ← hx₀']
  ext y
  constructor
  · rintro ⟨hy, hyne⟩
    obtain ⟨w, hw, rfl⟩ := hy
    refine ⟨w, ⟨hw, ?_⟩, rfl⟩
    intro hwa
    have hwa' : w = a := hwa
    exact hyne (by simpa [hwa'])
  · rintro ⟨w, ⟨hw, hwa⟩, rfl⟩
    refine ⟨⟨w, hw, rfl⟩, ?_⟩
    intro h
    refine hwa ?_
    have h3 : c (c.symm w) = c (c.symm a) := congrArg c h
    rw [c.right_inv (hsub hw)] at h3
    rw [hx₀'] at h3
    exact h3.trans ha.symm

/-- The open chart ball of radius `ρ` sits inside the closed chart ball of any larger radius. -/
theorem chartBall_subset_chartClosedBall_of_le {c : OpenPartialHomeomorph X ℂ} {a : ℂ}
    {ρ ρ' : ℝ} (h : ρ ≤ ρ') :
    Submission.chartBall c a ρ ⊆ Submission.chartClosedBall c a ρ' := by
  intro y hy
  rw [Submission.mem_chartBall] at hy
  refine ⟨hy.1, Metric.mem_closedBall.mpr ?_⟩
  have h' : dist (c y) a < ρ := Metric.mem_ball.mp hy.2
  linarith

/-- `x₀` lies in the closed chart ball of radius `r' ≥ 0` around `a = c x₀`. -/
theorem mem_chartClosedBall_self_of_eq {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {r' : ℝ}
    {x₀ : X} (ha : a = c x₀) (hx₀ : x₀ ∈ c.source) (h : 0 ≤ r') :
    x₀ ∈ Submission.chartClosedBall c a r' := by
  rw [Submission.mem_chartClosedBall]
  exact ⟨hx₀, by rw [← ha]; exact Metric.mem_closedBall_self h⟩

/-- A punctured open chart ball is preconnected (it is the image of the punctured Euclidean
ball, `Work.Modulus.isPreconnected_ball_diff_center`). -/
theorem isPreconnected_chartBall_sdiff_singleton {c : OpenPartialHomeomorph X ℂ} {a : ℂ}
    {r r' : ℝ} {x₀ : X} (h0 : 0 < r) (hrr' : r < r')
    (hsub : Metric.closedBall a r' ⊆ c.target) (ha : a = c x₀) (hx₀ : x₀ ∈ c.source) :
    IsPreconnected (Submission.chartBall c a r \ {x₀}) := by
  have hball : Metric.ball a r ⊆ c.target := fun z hz =>
    hsub (Metric.mem_closedBall.mpr (le_trans (Metric.mem_ball.mp hz).le hrr'.le))
  rw [chartBall_sdiff_singleton_eq_image hball ha hx₀]
  exact (Work.Modulus.isPreconnected_ball_diff_center h0).image c.symm
    (c.continuousOn_symm.mono (fun z hz => hball hz.1))

/-- The point `x₀ = c.symm a` lies in the closure of the punctured open chart ball. -/
theorem mem_closure_chartBall_sdiff_singleton {c : OpenPartialHomeomorph X ℂ} {a : ℂ}
    {r : ℝ} {x₀ : X} (h0 : 0 < r) (ha : a = c x₀) (hx₀ : x₀ ∈ c.source) :
    x₀ ∈ closure (Submission.chartBall c a r \ {x₀}) := by
  rw [_root_.mem_closure_iff]
  intro U hUo hx₀U
  set W : Set ℂ := c '' (c.source ∩ U) with hW
  have hWopen : IsOpen W := c.isOpen_image_source_inter hUo
  have haW : a ∈ W := by
    rw [ha]
    exact ⟨x₀, ⟨hx₀, hx₀U⟩, rfl⟩
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.isOpen_iff.mp (hWopen.inter Metric.isOpen_ball) a
      ⟨haW, Metric.mem_ball_self h0⟩
  set t : ℝ := min ε r / 2 with ht
  have htpos : 0 < t := by
    rw [ht]
    have : 0 < min ε r := lt_min hε h0
    linarith
  have htε : t < ε := by
    rw [ht]
    have h : min ε r ≤ ε := min_le_left _ _
    linarith
  have hzt : dist (a + (t : ℂ)) a = t := by
    rw [dist_eq_norm]
    have hsub' : a + (t : ℂ) - a = (t : ℂ) := by ring
    rw [hsub']
    simp [abs_of_pos htpos]
  have hzmem : a + (t : ℂ) ∈ W ∩ Metric.ball a r :=
    hεsub (by rw [Metric.mem_ball, hzt]; exact htε)
  obtain ⟨y, ⟨hysrc, hyU⟩, hyz⟩ := hzmem.1
  refine ⟨y, hyU, ?_, ?_⟩
  · rw [Submission.mem_chartBall]
    exact ⟨hysrc, by rw [hyz]; exact hzmem.2⟩
  · intro hyx
    have hyx' : y = x₀ := hyx
    have hzeq : a + (t : ℂ) = a := by rw [← hyz, hyx', ← ha]
    have hzero : dist (a + (t : ℂ)) a = 0 := by rw [hzeq, dist_self]
    rw [hzt] at hzero
    exact htpos.ne' hzero

/-- The punctured surface minus the compact chart annulus is the disjoint union of the
punctured open chart ball and the complement of the closed chart ball. -/
theorem sdiff_chartAnnulus_eq_union {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {r r' : ℝ}
    {x₀ : X} (hx₀ : x₀ ∈ Submission.chartClosedBall c a r') :
    (Set.univ \ {x₀}) \ (Submission.chartClosedBall c a r' \ Submission.chartBall c a r)
      = (Submission.chartBall c a r \ {x₀})
        ∪ (Set.univ \ Submission.chartClosedBall c a r') := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_sdiff] at hy
    obtain ⟨hy0, hyA⟩ := hy
    rw [Set.mem_sdiff] at hy0
    by_cases hyB : y ∈ Submission.chartBall c a r
    · exact Or.inl (by rw [Set.mem_sdiff]; exact ⟨hyB, hy0.2⟩)
    · refine Or.inr ?_
      rw [Set.mem_sdiff]
      refine ⟨trivial, ?_⟩
      intro hyCB
      exact hyA (by rw [Set.mem_sdiff]; exact ⟨hyCB, hyB⟩)
  · intro hy
    rcases hy with hyB | hyCB
    · rw [Set.mem_sdiff] at hyB
      refine ⟨?_, ?_⟩
      · rw [Set.mem_sdiff]; exact ⟨trivial, hyB.2⟩
      · rw [Set.mem_sdiff]; exact fun h => h.2 hyB.1
    · rw [Set.mem_sdiff] at hyCB
      have hyne : y ∉ ({x₀} : Set X) := fun h => hyCB.2 (by rw [show y = x₀ from h]; exact hx₀)
      refine ⟨?_, ?_⟩
      · rw [Set.mem_sdiff]; exact ⟨trivial, hyne⟩
      · rw [Set.mem_sdiff]; exact fun h => hyCB.2 h.1

end ChartBallImage

/-- On a non-compact connected Riemann surface, for the compact chart annulus `chartClosedBall c a r' \ chartBall c a r` around a point `x₀`, the hull condition required by the Behnke--Stein interface `Work.Analysis.RiemannSurface.PuncturedGlobalApproximation` holds: every relatively compact connected component of the complement of the annulus inside `X \ {x₀}` has `x₀` in its closure.  This is the concrete instance showing that the interface is applicable in the divisor chapter (the annulus is the compact set on which the local pole datum is uniformly approximated).

Route.  Writing `A` for the annulus and `V := X \ {x₀}`, the set `V \ A` is the disjoint union of `chartBall c a r \ {x₀}` (open in `V \ A`; preconnected because a chart ball minus one point is connected; its complement in `V \ A` is open, so it is a union of connected components) and `X \ chartClosedBall c a r'` (preconnected by `Work.SimplyConnected.ABS.isPreconnected_diff_chartClosedBall` applied with `Ω := X`).  The first is a single component whose closure contains `x₀` (it lies in the open chart ball since `a = c x₀` and `r > 0`); the second is a single component whose closure is *not* compact, because `X` would otherwise be the union of the two compact sets `chartClosedBall c a r'` and that closure.  Hence `IsCompact (closure C) → x₀ ∈ closure C`. -/
theorem chartAnnulus_hullCondition {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (x₀ : X) (hX : ¬ CompactSpace X)
    {a : ℂ} {r r' : ℝ} (h0 : 0 < r) (hrr' : r < r')
    (hsub : Metric.closedBall a r' ⊆ (chartAt ℂ x₀).target)
    (ha : a = (chartAt ℂ x₀) x₀) :
    ∀ C : Set X,
      (∃ x ∈ (Set.univ \ {x₀}) \ (Submission.chartClosedBall (chartAt ℂ x₀) a r' \
          Submission.chartBall (chartAt ℂ x₀) a r),
        C = connectedComponentIn ((Set.univ \ {x₀}) \
          (Submission.chartClosedBall (chartAt ℂ x₀) a r' \
            Submission.chartBall (chartAt ℂ x₀) a r)) x) →
      IsCompact (closure C) → x₀ ∈ closure C := by
  intro C hC hcomp
  obtain ⟨x, hxZ, rfl⟩ := hC
  -- abbreviations for the annulus, the punctured surface, and its two pieces
  set A : Set X :=
    Submission.chartClosedBall (chartAt ℂ x₀) a r' \ Submission.chartBall (chartAt ℂ x₀) a r
    with hA
  set Z : Set X := (Set.univ \ {x₀}) \ A with hZ
  set U1 : Set X := Submission.chartBall (chartAt ℂ x₀) a r \ {x₀} with hU1
  set U2 : Set X := Set.univ \ Submission.chartClosedBall (chartAt ℂ x₀) a r' with hU2
  have hx₀src : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  have hx₀CB : x₀ ∈ Submission.chartClosedBall (chartAt ℂ x₀) a r' :=
    mem_chartClosedBall_self_of_eq ha hx₀src (le_of_lt (lt_trans h0 hrr'))
  have hZU : Z = U1 ∪ U2 := by
    rw [hZ, hA, hU1, hU2]
    exact sdiff_chartAnnulus_eq_union hx₀CB
  have hU1pc : IsPreconnected U1 := by
    rw [hU1]
    exact isPreconnected_chartBall_sdiff_singleton h0 hrr' hsub ha hx₀src
  have hU2pc : IsPreconnected U2 := by
    rw [hU2]
    exact Work.SimplyConnected.ABS.isPreconnected_diff_chartClosedBall (Ω := Set.univ)
      isOpen_univ isPreconnected_univ hsub (fun _ _ => trivial)
  have hU1open : IsOpen U1 := by
    rw [hU1]
    exact (Submission.chartBall_isOpen (chartAt ℂ x₀) a r).sdiff isClosed_singleton
  have hU2open : IsOpen U2 := by
    have h : U2 = (Submission.chartClosedBall (chartAt ℂ x₀) a r')ᶜ := by
      rw [hU2]; ext y; simp
    rw [h]
    exact (Submission.isClosed_chartClosedBall hsub).isOpen_compl
  have hU1U2 : U1 ∩ U2 = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨y, hy⟩
    rw [Set.mem_inter_iff] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [hU1] at hy1
    rw [hU2] at hy2
    rw [Set.mem_sdiff] at hy1 hy2
    exact hy2.2 (chartBall_subset_chartClosedBall_of_le hrr'.le hy1.1)
  have hsubU : connectedComponentIn Z x ⊆ U1 ∪ U2 := by
    rw [← hZU]
    exact connectedComponentIn_subset Z x
  have hdisj : connectedComponentIn Z x ∩ (U1 ∩ U2) = ∅ := by
    rw [hU1U2, Set.inter_empty]
  have hsplit : connectedComponentIn Z x ⊆ U1 ∨ connectedComponentIn Z x ⊆ U2 :=
    (isPreconnected_iff_subset_of_disjoint.mp isPreconnected_connectedComponentIn)
      U1 U2 hU1open hU2open hsubU hdisj
  rcases hsplit with hCU1 | hCU2
  · -- the component is the punctured chart ball: its closure contains `x₀`
    have hxU1 : x ∈ U1 := hCU1 (mem_connectedComponentIn hxZ)
    have hU1Z : U1 ⊆ Z := by rw [hZU]; exact Set.subset_union_left
    have hU1sub : U1 ⊆ connectedComponentIn Z x :=
      hU1pc.subset_connectedComponentIn hxU1 hU1Z
    have heq : connectedComponentIn Z x = U1 := subset_antisymm hCU1 hU1sub
    rw [heq, hU1]
    exact mem_closure_chartBall_sdiff_singleton h0 ha hx₀src
  · -- the component is the complement of the closed chart ball: it cannot have compact closure
    have hxU2 : x ∈ U2 := hCU2 (mem_connectedComponentIn hxZ)
    have hU2Z : U2 ⊆ Z := by rw [hZU]; exact Set.subset_union_right
    have hU2sub : U2 ⊆ connectedComponentIn Z x :=
      hU2pc.subset_connectedComponentIn hxU2 hU2Z
    have heq : connectedComponentIn Z x = U2 := subset_antisymm hCU2 hU2sub
    rw [heq] at hcomp
    exfalso
    have hXsub : (Set.univ : Set X) ⊆
        Submission.chartClosedBall (chartAt ℂ x₀) a r' ∪ closure U2 := by
      intro y _
      by_cases hy : y ∈ Submission.chartClosedBall (chartAt ℂ x₀) a r'
      · exact Or.inl hy
      · refine Or.inr (subset_closure ?_)
        rw [hU2]
        exact ⟨trivial, hy⟩
    have huniv : IsCompact (Set.univ : Set X) :=
      ((Submission.isCompact_chartClosedBall hsub).union hcomp).of_isClosed_subset
        isClosed_univ hXsub
    exact hX (isCompact_univ_iff.mp huniv)

end Work.Analysis.RiemannSurface
