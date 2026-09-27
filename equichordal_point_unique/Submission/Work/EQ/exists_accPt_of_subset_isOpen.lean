import Mathlib

namespace Work.EQ

/-! ### A countable compact cover of an open subset of `ℂ`

Every open `U ⊆ ℂ` is the union of the countably many compact sets `covSet U k`,
`k : ℕ`, where `covSet U k` consists of the points of norm at most `k` whose open
ball of radius `1/(k+1)` is contained in `U`.  These are closed (as the complement
of the `r`-thickening of `Uᶜ`) and bounded, hence compact; and they cover `U`
because `U` is open.  Pigeonholing an uncountable `S ⊆ U` over this cover and
applying Bolzano–Weierstrass yields the accumulation point. -/

/-- For `k : ℕ`, the set of points `x` with `‖x‖ ≤ k` whose open ball of radius `1/(k+1)`
is contained in `U`. -/
private def covSet (U : Set ℂ) (k : ℕ) : Set ℂ :=
  {x : ℂ | ‖x‖ ≤ (k : ℝ)} ∩ {x : ℂ | Metric.ball x (((k : ℝ) + 1)⁻¹) ⊆ U}

private lemma isClosed_ball_subset (U : Set ℂ) (r : ℝ) :
    IsClosed {x : ℂ | Metric.ball x r ⊆ U} := by
  rw [show {x : ℂ | Metric.ball x r ⊆ U} = (Metric.thickening r Uᶜ)ᶜ from by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Metric.mem_thickening_iff]
    constructor
    · rintro hsub ⟨z, hzU, hxz⟩
      exact hzU (hsub (Metric.mem_ball.mpr (by rw [dist_comm]; exact hxz)))
    · intro hnot y hy
      by_contra hyU
      exact hnot ⟨y, hyU, by rw [dist_comm]; exact Metric.mem_ball.mp hy⟩]
  exact Metric.isOpen_thickening.isClosed_compl

private lemma isClosed_covSet (U : Set ℂ) (k : ℕ) : IsClosed (covSet U k) :=
  (isClosed_le continuous_norm continuous_const).inter (isClosed_ball_subset U _)

private lemma covSet_subset (U : Set ℂ) (k : ℕ) : covSet U k ⊆ U := by
  intro x hx
  exact hx.2 (Metric.mem_ball.mpr (by rw [dist_self]; positivity))

private lemma covSet_subset_closedBall (U : Set ℂ) (k : ℕ) :
    covSet U k ⊆ Metric.closedBall (0 : ℂ) (k : ℝ) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  simpa using hx.1

private lemma isCompact_covSet (U : Set ℂ) (k : ℕ) : IsCompact (covSet U k) :=
  (isCompact_closedBall (0 : ℂ) (k : ℝ)).of_isClosed_subset
    (isClosed_covSet U k) (covSet_subset_closedBall U k)

private lemma subset_iUnion_covSet {U : Set ℂ} (hU : IsOpen U) : U ⊆ ⋃ k, covSet U k := by
  intro z hz
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hU z hz
  obtain ⟨k, hk⟩ := exists_nat_gt (max ‖z‖ (ε⁻¹ + 1))
  have hzk : ‖z‖ ≤ (k : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hk)
  have hk1 : ε⁻¹ + 1 < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
  have hr : ((k : ℝ) + 1)⁻¹ < ε := by
    rw [inv_lt_comm₀ (by positivity) hεpos]
    linarith
  refine Set.mem_iUnion.mpr ⟨k, hzk, ?_⟩
  intro y hy
  exact hεsub (Metric.mem_ball.mpr (lt_trans (Metric.mem_ball.mp hy) hr))

/-- **An uncountable subset of an open subset of `ℂ` has an accumulation point inside.**
Route: `U` is the countable union of the closed rational balls `B̄` with `B` a rational
(centre in `ℚ[i]`, rational radius) ball and `B̄ ⊆ U`; uncountably many points of `S` must lie in
one such `B`, then Bolzano–Weierstrass (`Set.Infinite.exists_accPt_of_subset_isCompact`) on the
compact `B̄` gives `x ∈ B̄ ⊆ U` with `AccPt x (𝓟 (S ∩ B))`, hence `AccPt x (𝓟 S)`. -/
theorem exists_accPt_of_subset_isOpen {U S : Set ℂ} (hU : IsOpen U) (hS : S ⊆ U)
    (h : ¬ S.Countable) : ∃ x ∈ U, AccPt x (Filter.principal S) := by
  have hsub : S ⊆ ⋃ k, covSet U k := hS.trans (subset_iUnion_covSet hU)
  have heq : S = ⋃ k, (S ∩ covSet U k) := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hsub hz)
      exact Set.mem_iUnion.mpr ⟨k, hz, hk⟩
    · intro z hz
      obtain ⟨k, hz1, _⟩ := Set.mem_iUnion.mp hz
      exact hz1
  have hex : ∃ k, (S ∩ covSet U k).Infinite := by
    by_contra hc
    simp only [not_exists] at hc
    refine h ?_
    rw [heq]
    exact Set.countable_iUnion fun k => (Set.not_infinite.mp (hc k)).countable
  obtain ⟨k, hk⟩ := hex
  obtain ⟨x, hxK, hxacc⟩ := hk.exists_accPt_of_subset_isCompact (isCompact_covSet U k)
    Set.inter_subset_right
  exact ⟨x, covSet_subset U k hxK,
    hxacc.mono (Filter.principal_mono.mpr Set.inter_subset_left)⟩

end Work.EQ
