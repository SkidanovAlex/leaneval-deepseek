import Mathlib
import Submission.Work.SINGMV.Defs

/-!
# A convex combination of close points is close (Area SINGMV, mesh estimates)

If `q i` are points of the standard `n`-simplex which are pairwise at distance at most `d`
(in the sup metric on `ℝ^{n+1}`, i.e. after applying `toE`), then every point of the convex hull of
the `q i` is within `d` of any `q i₀`. This is the elementary estimate behind the fact that the
mesh of the barycentric subdivision shrinks by the expected factor.

The proof reduces to the one-dimensional statement that a weighted average of numbers, each within
`d` of `b`, is within `d` of `b` (`abs_weighted_sum_le` below).
-/

noncomputable section

open Convexity

namespace Work.SingMV

/-- A weighted average of reals lies within the extremes: if every `a i` is within `d` of `b` and
the weights are a probability distribution (`w` is a point of the standard simplex), then so is the
weighted average of the `a i`. -/
private lemma abs_weighted_sum_le {ι : Type*} [Fintype ι] (w a : ι → ℝ) (b d : ℝ)
    (hw : ∀ i, 0 ≤ w i) (htot : ∑ i, w i = 1) (ha : ∀ i, |a i - b| ≤ d) :
    |∑ i, w i * a i - b| ≤ d := by
  have hb : b = ∑ i, w i * b := by rw [← Finset.sum_mul, htot, one_mul]
  rw [hb, ← Finset.sum_sub_distrib]
  calc |∑ i, (w i * a i - w i * b)| ≤ ∑ i, |w i * a i - w i * b| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i * |a i - b| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (hw i)]
    _ ≤ ∑ i, w i * d := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ha i) (hw i)
    _ = d := by rw [← Finset.sum_mul, htot, one_mul]

/-- **A point of the convex hull of a `d`-close family of points of `Δⁿ` is `d`-close to any member
of the family.** Writing `x` for the barycentric coordinates, the convex combination
`iConvexComb x q` has `j`-th coordinate `∑ i, x.weights i * toE (q i) j`, and each summand is within
`d` of `toE (q i₀) j`; the estimate is then the one-dimensional weighted-average bound.

This is the metric input to the shrinking of the mesh under barycentric subdivision. -/
theorem bary_dist_le {n k : ℕ} (x : Convexity.StdSimplex ℝ (Fin (k+1)))
    (q : Fin (k+1) → Convexity.StdSimplex ℝ (Fin (n+1))) (d : ℝ) (i₀ : Fin (k+1))
    (hd : ∀ i j, dist (Work.SingMV.toE (q i)) (Work.SingMV.toE (q j)) ≤ d) :
    dist (Work.SingMV.toE (Convexity.iConvexComb (R := ℝ) x q))
      (Work.SingMV.toE (q i₀)) ≤ d := by
  have hd0 : 0 ≤ d := le_trans dist_nonneg (hd i₀ i₀)
  -- the sup metric on `Fin (n+1) → ℝ` is computed coordinatewise
  rw [dist_pi_le_iff hd0]
  intro j
  rw [Real.dist_eq]
  show |(Convexity.iConvexComb (R := ℝ) x q).weights j - (q i₀).weights j| ≤ d
  rw [weights_iConvexComb_apply x q j]
  exact abs_weighted_sum_le (fun i => x.weights i) (fun i => (q i).weights j) ((q i₀).weights j) d
    (fun i => x.weights_nonneg i) x.total_of_fintype
    (fun i => by
      have h := (dist_pi_le_iff hd0).1 (hd i i₀) j
      rwa [Real.dist_eq] at h)

end Work.SingMV
