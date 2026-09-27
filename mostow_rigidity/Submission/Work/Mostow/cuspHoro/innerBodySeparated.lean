import Mathlib
import Submission.Work.Mostow.cuspHoro.voronoiDefs
import Submission.Work.Mostow.cuspHoro.unboundedSeparated

/-!
# Separation in the inner parallel body of an unbounded convex set

Let `D ⊆ ℝ^m` be convex and unbounded, and suppose that `innerBody η D` is nonempty, i.e. some
point of `ℝ^m` has its open `η`-ball contained in `D`.  Then the inner parallel body at the
smaller scale `η/2` is unbounded, and hence contains `N` points that are pairwise at distance
at least `2ε`, for every `N` and every `ε > 0`.

The geometric input is elementary: if the `η`-ball around `y₀` lies in `D` and `x ∈ D`, then for
every `t ≤ 1/2` the point `y₀ + t • (x - y₀)` has its `η/2`-ball inside `D` — a point of
`B(y₀ + t•(x-y₀), η/2)` is a convex combination with weights `1 - t` and `t` of a point of
`B(y₀, η)` and of `x`.  Since `D` is unbounded, `x` can be taken arbitrarily far from `y₀`, so
`innerBody (η/2) D` is unbounded.

The passage from unboundedness to `N` pairwise `2ε`-separated points is a greedy/packing
argument, recorded for an arbitrary (pseudo)metric space as `unboundedSeparated` (a separate lemma).
-/

namespace Work.Mostow.cuspHoro

open Metric

/-- The inner parallel bodies are monotone in the scale. -/
lemma innerBody_mono {m : ℕ} {D : Set (EuclideanSpace ℝ (Fin m))} {ε η : ℝ} (h : ε ≤ η) :
    innerBody η D ⊆ innerBody ε D :=
  fun _ hy z hz => hy z (lt_of_lt_of_le hz h)

/-- The distance from the midpoint `y₀ + (1/2) • (x - y₀)` to `y₀` is half the distance from
`x` to `y₀`. -/
lemma dist_mid_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (y₀ x : E) :
    dist (y₀ + (1 / 2 : ℝ) • (x - y₀)) y₀ = (1 / 2) * dist x y₀ := by
  rw [dist_eq_norm, dist_eq_norm]
  have h1 : y₀ + (1 / 2 : ℝ) • (x - y₀) - y₀ = (1 / 2 : ℝ) • (x - y₀) := by abel
  rw [h1, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- An unbounded subset of a metric space has points arbitrarily far from any prescribed point. -/
lemma exists_dist_gt_of_not_isBounded {α : Type*} [PseudoMetricSpace α] {A : Set α}
    (h : ¬ Bornology.IsBounded A) (c : α) (r : ℝ) : ∃ x ∈ A, r < dist x c := by
  by_contra hc
  push Not at hc
  exact h ((Metric.isBounded_iff_subset_closedBall c).2
    ⟨r, fun x hx => Metric.mem_closedBall.2 (hc x hx)⟩)

/-- Convexity input for the inner parallel body: if the `η`-ball around `y₀` is contained in `D`
and `x ∈ D`, then for every `t ≤ 1/2` the point `y₀ + t • (x - y₀)` has its `η/2`-ball inside
`D`. -/
lemma smul_mem_innerBody {m : ℕ} {D : Set (EuclideanSpace ℝ (Fin m))} (hconv : Convex ℝ D)
    {η : ℝ} (_hη : 0 < η) {y₀ x : EuclideanSpace ℝ (Fin m)}
    (hy₀ : y₀ ∈ innerBody η D) (hx : x ∈ D)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    y₀ + t • (x - y₀) ∈ innerBody (η / 2) D := by
  intro z hz
  have ht1 : 0 < 1 - t := by linarith
  have hinvpos : 0 < (1 - t)⁻¹ := inv_pos.mpr ht1
  have hz2 : ‖z - (y₀ + t • (x - y₀))‖ < η / 2 := by
    rw [← dist_eq_norm, dist_comm]; exact hz
  have hinv : (1 - t)⁻¹ ≤ 2 := by
    have := inv_anti₀ (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 : ℝ) / 2 ≤ 1 - t by linarith)
    simpa using this
  have hnorm : ‖(1 - t)⁻¹ • (z - (y₀ + t • (x - y₀)))‖ < η := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinvpos]
    calc (1 - t)⁻¹ * ‖z - (y₀ + t • (x - y₀))‖
        ≤ 2 * ‖z - (y₀ + t • (x - y₀))‖ :=
          mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
      _ < 2 * (η / 2) := by linarith
      _ = η := by ring
  have hw : y₀ + (1 - t)⁻¹ • (z - (y₀ + t • (x - y₀))) ∈ D := by
    apply hy₀
    rw [dist_comm, dist_eq_norm]
    have h1 : (y₀ + (1 - t)⁻¹ • (z - (y₀ + t • (x - y₀)))) - y₀
        = (1 - t)⁻¹ • (z - (y₀ + t • (x - y₀))) := by abel
    rw [h1]; exact hnorm
  have hz3 : (1 - t) • (y₀ + (1 - t)⁻¹ • (z - (y₀ + t • (x - y₀)))) + t • x = z := by
    rw [smul_add, smul_inv_smul₀ (ne_of_gt ht1)]
    module
  rw [← hz3]
  exact hconv hw hx (by linarith) ht0 (by ring)

/-- **Separation in the inner parallel body.** If `D` is convex, unbounded, and has nonempty
inner parallel body at scale `η > 0`, then for every `ε > 0` and every `N` the inner parallel
body at scale `η/2` contains `N` points that are pairwise at distance at least `2ε`. -/
theorem innerBodySeparated {m : ℕ} (D : Set (EuclideanSpace ℝ (Fin m))) (hconv : Convex ℝ D)
    {η : ℝ} (hη : 0 < η) (hne : (Work.Mostow.cuspHoro.innerBody η D).Nonempty)
    (hunbdd : ¬ Bornology.IsBounded D)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin m)), S.card = N ∧
      (∀ y ∈ S, y ∈ Work.Mostow.cuspHoro.innerBody (η / 2) D) ∧
      ∀ y ∈ S, ∀ y' ∈ S, y ≠ y' → 2 * ε ≤ dist y y' := by
  have hA : ¬ Bornology.IsBounded (Work.Mostow.cuspHoro.innerBody (η / 2) D) := by
    intro hb
    obtain ⟨y₀, hy₀⟩ := hne
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall y₀).1 hb
    obtain ⟨x, hx, hxr⟩ : ∃ x ∈ D, 2 * (r + 1) < dist x y₀ :=
      exists_dist_gt_of_not_isBounded hunbdd y₀ (2 * (r + 1))
    have hp : y₀ + (1 / 2 : ℝ) • (x - y₀) ∈ Work.Mostow.cuspHoro.innerBody (η / 2) D :=
      smul_mem_innerBody hconv hη hy₀ hx (t := 1 / 2) (by norm_num) le_rfl
    have hpr : dist (y₀ + (1 / 2 : ℝ) • (x - y₀)) y₀ ≤ r := Metric.mem_closedBall.1 (hr hp)
    rw [dist_mid_eq] at hpr
    linarith
  exact unboundedSeparated hA hε N

end Work.Mostow.cuspHoro
