import Mathlib
import Submission.Work.WilG1.Cell.Stair.Basic

noncomputable section

namespace Work.WilG1.Cell.Stair

/-- **The fibre step of the staircase.**  If the fibre of `h` in direction `k` at the base point
`stair x y k` is differentiable at every point of the segment between `x k` and `y k` (which is
what `hex` supplies, since all the points `stairSeg x y k t` lie in `V`), then the one-coordinate
increment `h (stair x y (k+1)) - h (stair x y k)` of the staircase is `(x k - y k)` times the
junk partial of `h` in direction `k` at some point `p` of that segment, and this `p` is no
further from `y` than `x` is. -/
theorem exists_stair_decomp {n : ℕ} (h : (Fin n → ℝ) → ℝ) {V : Set (Fin n → ℝ)}
    (hex : ∀ i : Fin n, ∀ z ∈ V, DifferentiableAt ℝ (fibreMap h i z) (z i))
    {x y : Fin n → ℝ} (k : Fin n)
    (hseg : ∀ t ∈ Set.Icc (min (x k) (y k)) (max (x k) (y k)), stairSeg x y k t ∈ V) :
    ∃ p ∈ V, ‖p - y‖ ≤ ‖x - y‖ ∧
      h (stair x y ((k : ℕ) + 1)) - h (stair x y (k : ℕ)) = (x k - y k) * junkP h k p := by
  -- The one-variable fibre function whose mean value theorem controls the increment.
  let g : ℝ → ℝ := fibreMap h k (stair x y (k : ℕ))
  -- `g` is differentiable at every point of the segment: each such point lies in `V`.
  have hdiff : ∀ t ∈ Set.Icc (min (x k) (y k)) (max (x k) (y k)), DifferentiableAt ℝ g t := by
    intro t ht
    have hfib := hex k (stairSeg x y k t) (hseg t ht)
    rw [fibreMap_stairSeg] at hfib
    have hk : stairSeg x y k t k = t := by simp
    rw [hk] at hfib
    exact hfib
  -- Every segment point stays inside the sup-ball of radius `‖x - y‖` around `y`.
  have hmem : ∀ t ∈ Set.Icc (min (x k) (y k)) (max (x k) (y k)),
      ‖stairSeg x y k t - y‖ ≤ ‖x - y‖ := fun t ht => stairSeg_sub_le' x y k ht
  -- The junk partial at a segment point is the genuine derivative of `g` there.
  have hjunk : ∀ t ∈ Set.Icc (min (x k) (y k)) (max (x k) (y k)),
      junkP h k (stairSeg x y k t) = deriv g t := by
    intro t _
    have hk : stairSeg x y k t k = t := by simp
    simp only [junkP, hk, fibreMap_stairSeg]
    rfl
  -- The increment is the two-endpoint difference of `g`.
  have hgx : g (x k) = h (stair x y ((k : ℕ) + 1)) := by
    change h (Function.update (stair x y (k : ℕ)) k (x k)) = h (stair x y ((k : ℕ) + 1))
    rw [stair_succ]
  have hgy : g (y k) = h (stair x y (k : ℕ)) := by
    change h (Function.update (stair x y (k : ℕ)) k (y k)) = h (stair x y (k : ℕ))
    rw [Function.update_eq_self_iff.mpr (by simp)]
  by_cases hxy : x k = y k
  · -- Degenerate case: the two endpoints coincide, so the increment vanishes.
    refine ⟨stairSeg x y k (x k), hseg (x k) ⟨min_le_left _ _, le_max_left _ _⟩,
      hmem (x k) ⟨min_le_left _ _, le_max_left _ _⟩, ?_⟩
    simp [stair_succ_of_eq hxy, hxy]
  · rcases lt_or_gt_of_ne hxy with hlt | hlt
    · -- Case `x k < y k`.
      have hmin : min (x k) (y k) = x k := min_eq_left (le_of_lt hlt)
      have hmax : max (x k) (y k) = y k := max_eq_right (le_of_lt hlt)
      have hmem' : ∀ t ∈ Set.Icc (x k) (y k),
          t ∈ Set.Icc (min (x k) (y k)) (max (x k) (y k)) := by
        intro t ht; rw [hmin, hmax]; exact ht
      have hdiffIcc : DifferentiableOn ℝ g (Set.Icc (x k) (y k)) :=
        fun t ht => (hdiff t (hmem' t ht)).differentiableWithinAt
      obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope g hlt hdiffIcc.continuousOn
        (hdiffIcc.mono Set.Ioo_subset_Icc_self)
      have hcseg : c ∈ Set.Icc (min (x k) (y k)) (max (x k) (y k)) :=
        hmem' c (Set.Ioo_subset_Icc_self hc)
      have hne : y k - x k ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt)
      have h2 : g (y k) - g (x k) = deriv g c * (y k - x k) := by
        rw [hcd, div_mul_cancel₀ (g (y k) - g (x k)) hne]
      refine ⟨stairSeg x y k c, hseg c hcseg, hmem c hcseg, ?_⟩
      rw [hjunk c hcseg, ← hgx, ← hgy]
      nlinarith [h2]
    · -- Case `y k < x k`.
      have hmin : min (x k) (y k) = y k := min_eq_right (le_of_lt hlt)
      have hmax : max (x k) (y k) = x k := max_eq_left (le_of_lt hlt)
      have hmem' : ∀ t ∈ Set.Icc (y k) (x k),
          t ∈ Set.Icc (min (x k) (y k)) (max (x k) (y k)) := by
        intro t ht; rw [hmin, hmax]; exact ht
      have hdiffIcc : DifferentiableOn ℝ g (Set.Icc (y k) (x k)) :=
        fun t ht => (hdiff t (hmem' t ht)).differentiableWithinAt
      obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope g hlt hdiffIcc.continuousOn
        (hdiffIcc.mono Set.Ioo_subset_Icc_self)
      have hcseg : c ∈ Set.Icc (min (x k) (y k)) (max (x k) (y k)) :=
        hmem' c (Set.Ioo_subset_Icc_self hc)
      have hne : x k - y k ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt)
      have h2 : g (x k) - g (y k) = deriv g c * (x k - y k) := by
        rw [hcd, div_mul_cancel₀ (g (x k) - g (y k)) hne]
      refine ⟨stairSeg x y k c, hseg c hcseg, hmem c hcseg, ?_⟩
      rw [hjunk c hcseg, ← hgx, ← hgy]
      nlinarith [h2]

end Work.WilG1.Cell.Stair
