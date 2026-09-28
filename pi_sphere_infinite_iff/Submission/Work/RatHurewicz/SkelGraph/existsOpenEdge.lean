import Mathlib
import Submission.Work.RatHurewicz.SkelGraph.goodDefs

namespace Work.RatHurewicz.SkelGraph

/- Please state and prove this as `Work.RatHurewicz.SkelGraph.existsOpenEdge`, i.e. inside `namespace Work.RatHurewicz.SkelGraph`, in the file `Submission/Work/RatHurewicz/SkelGraph/existsOpenEdge.lean` (it must import `Submission.Work.RatHurewicz.SkelGraph.goodDefs`).  Prefix any helper lemmas you add with `existsOpenEdge_`.

**A neighbourhood of an interior point of an edge of the model consisting of "good" points.**

`Work.RatHurewicz.SkelGraph.GoodAux.good D U` is the set of low dimensional raw points whose
canonical graph data `Work.RatHurewicz.SkelGraph.wOf` lies in `U`.

Plan.  Take `N` to be a ball in the copy `Δ^{n+2}` of `Raw D`, of radius `δ > 0` with
`δ < min(s, 1-s)` and `δ ≤ ε` where `ε` is given by `GoodAux.exists_nhds_pair` applied to
`hU` and `hmem`.  A low dimensional `y' = Sum.inl ⟨i, x'⟩` with `dist x' (sdPt p q s) < δ` has
support exactly `{p,q}`: the coordinates at `p` and `q` stay positive while all others are `< δ`,
and there are at most two non-zero coordinates.  Then `x' = sdPt p q s'` for
`s' = x' q` with `|s' - s| < δ ≤ ε` (`GoodAux.exists_sdPt_of_supp`), and
`GoodAux.wOf_sdPt` identifies the graph data of `y'` with
`Sum.inr (eCl D (Sum.inl ⟨i, (⟨(p,q),hpq⟩ : EdgeRaw D)⟩), s')`, which lies in `U` because
`|s' - s| < ε`. -/
theorem existsOpenEdge {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    (D : Work.RatHurewicz.MData X n x₀)
    {U : Set (Work.RatHurewicz.SkelGraph.V D ⊕
      (Work.RatHurewicz.SkelGraph.E D × unitInterval))}
    (hU : IsOpen U)
    {i : D.Idx} {p q : Fin (n + 2)} (hpq : p < q) {s : unitInterval}
    (h0 : 0 < (s : ℝ)) (h1 : (s : ℝ) < 1)
    (hmem : Sum.inr (Work.RatHurewicz.SkelGraph.eCl D (Sum.inl (⟨i,
        (⟨(p, q), hpq⟩ : {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2})⟩ :
        Σ _ : D.Idx, {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2})), s) ∈ U) :
    ∃ N : Set (Work.RatHurewicz.Raw D), IsOpen N ∧
      (Sum.inl (⟨i, Work.RatHurewicz.SkelGraph.sdPt p q s⟩ :
        Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))) : Work.RatHurewicz.Raw D) ∈ N ∧
      ∀ y' ∈ N, Work.RatHurewicz.isLowDim D y' →
        y' ∈ Work.RatHurewicz.SkelGraph.GoodAux.good D U := by
  classical
  -- a window of parameters of the edge around `s` contained in `U`
  obtain ⟨ε, hεpos, hεU⟩ := GoodAux.exists_nhds_pair hU hmem
  -- the radius of the ball: smaller than `s`, `1 - s` and `ε`
  set δ : ℝ := min ε (min (s : ℝ) (1 - (s : ℝ))) / 2 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    have : 0 < min ε (min (s : ℝ) (1 - (s : ℝ))) := lt_min hεpos (lt_min h0 (by linarith))
    linarith
  have hδle : δ ≤ ε := by
    rw [hδ]
    have := min_le_left ε (min (s : ℝ) (1 - (s : ℝ)))
    linarith
  have hδs : δ < (s : ℝ) := by
    rw [hδ]
    have h1' := min_le_right ε (min (s : ℝ) (1 - (s : ℝ)))
    have h2' := min_le_left (s : ℝ) (1 - (s : ℝ))
    linarith
  have hδ1s : δ < 1 - (s : ℝ) := by
    rw [hδ]
    have h1' := min_le_right ε (min (s : ℝ) (1 - (s : ℝ)))
    have h2' := min_le_right (s : ℝ) (1 - (s : ℝ))
    linarith
  refine ⟨Sum.inl '' (Sigma.mk i '' Metric.ball (sdPt p q s) δ :
      Set (Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2)))), ?_, ?_, ?_⟩
  · -- the ball in the copy of `Δ^{n+2}` is open in `Raw D`
    apply isOpenMap_inl
    apply isOpenMap_sigmaMk
    exact Metric.isOpen_ball
  · -- it contains the point `sdPt p q s`
    exact ⟨⟨i, sdPt p q s⟩, ⟨sdPt p q s, Metric.mem_ball_self hδpos, rfl⟩, rfl⟩
  · -- and every low dimensional point of it is good
    intro y' hy'N hy'low
    rcases hy'N with ⟨a, ⟨x', hx'ball, rfl⟩, rfl⟩
    have hdist : dist x' (sdPt p q s) < δ := hx'ball
    have hlow : (supp x').card ≤ 2 := (GoodAux.isLowDim_inl_iff i x').mp hy'low
    -- each coordinate of `x'` is within `δ` of the corresponding coordinate of `sdPt p q s`
    have hpiece : ∀ k : Fin (n + 2),
        dist (x'.1 k) ((sdPt p q s).1 k) ≤ dist x' (sdPt p q s) := by
      intro k
      rw [Subtype.dist_eq]
      exact dist_le_pi_dist x'.1 (sdPt p q s).1 k
    have hpval : (sdPt p q s).1 p = 1 - (s : ℝ) := sdPt_apply_left hpq.ne s
    have hqval : (sdPt p q s).1 q = (s : ℝ) := sdPt_apply_right hpq.ne s
    -- the coordinates at `p` and at `q` of `x'` are positive
    have hppos : 0 < x'.1 p := by
      have h1' : dist (x'.1 p) (1 - (s : ℝ)) < δ := by
        rw [← hpval]; exact lt_of_le_of_lt (hpiece p) hdist
      rw [Real.dist_eq] at h1'
      have h2' := (abs_sub_lt_iff.mp h1').2
      linarith
    have hqpos : 0 < x'.1 q := by
      have h1' : dist (x'.1 q) (s : ℝ) < δ := by
        rw [← hqval]; exact lt_of_le_of_lt (hpiece q) hdist
      rw [Real.dist_eq] at h1'
      have h2' := (abs_sub_lt_iff.mp h1').2
      linarith
    -- hence, using low dimensionality, the support of `x'` is exactly `{p, q}`
    have hsupp : supp x' = {p, q} := by
      have hsub : ({p, q} : Finset (Fin (n + 2))) ⊆ supp x' := by
        intro k hk
        rw [Finset.mem_insert, Finset.mem_singleton] at hk
        rw [mem_supp]
        rcases hk with rfl | rfl
        · exact ne_of_gt hppos
        · exact ne_of_gt hqpos
      have hcard : (supp x').card ≤ ({p, q} : Finset (Fin (n + 2))).card := by
        rw [Finset.card_pair hpq.ne]; exact hlow
      exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
    -- so `x'` is on the edge through `p` and `q`
    obtain ⟨s', hs'x', hs'q, hs'0, hs'1⟩ := GoodAux.exists_sdPt_of_supp hpq hsupp
    have hεss : |(s' : ℝ) - (s : ℝ)| < ε := by
      rw [hs'q]
      have h1' : dist (x'.1 q) ((sdPt p q s).1 q) < δ := lt_of_le_of_lt (hpiece q) hdist
      rw [hqval, Real.dist_eq] at h1'
      exact lt_of_lt_of_le h1' hδle
    subst hs'x'
    refine GoodAux.mem_good_of hy'low ?_
    rw [GoodAux.wOf_sdPt hpq hs'0 hs'1 hy'low]
    exact hεU s' hεss

end Work.RatHurewicz.SkelGraph
