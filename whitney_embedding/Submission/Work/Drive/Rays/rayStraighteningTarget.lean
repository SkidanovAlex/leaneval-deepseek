import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Drive.Rays.rayStraightening

/-!
# The chart-target ("room") row of a straightened germ

`Work.Routing.inter_subset_singleton_of_germ_avoid` and the gluing engines consume the germ of a
piece in the *strong* form

    `c (r t₀) + (t - t₀) • w ∈ c.target`   and   `r t = c.symm (c (r t₀) + (t - t₀) • w)`,

because `c.symm` is only injective on `c.target`: the identity alone is not enough (a
`c.symm A = c.symm B` with `A ∉ c.target` carries no information).  `Work.Drive.Rays.rayStraightening`
delivers only the identity.  Here we add the *short* target row, which is all that is needed once the
germ window is shrunk (and the germ windows of the routing are existential, so they may be shrunk).

The argument is one line of continuity: `t ↦ c (r t₀) + (t - t₀) • w` is continuous at `t₀` and its
value there is `c (r t₀) ∈ c.target`, an open set.
-/

namespace Work.Drive.Rays

open Set Topology
open Work.Noncompact.CompressionTube (MC MCreal smoothOrder)

/-- **The straightened germ of a ray, with its chart-target row on a short window.**

For a `C^∞` immersion `r` of `[0,∞)` into a smooth `n`-manifold (`n ≥ 2`) and any `t₀ ≥ 0` there are
a chart `c` of the maximal atlas, a direction `w ≠ 0` and an extent `e > 0` with

* `c (r t₀) + (t - t₀) • w ∈ c.target` for `0 ≤ t`, `|t - t₀| ≤ e`  (the room row), and
* `r t = c.symm (c (r t₀) + (t - t₀) • w)` for the same `t` (the germ row).

The room row is what makes the germ usable with the separation and gluing engines. -/
theorem rayStraightening_target {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {r : ℝ → M}
    (hrsm : ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ici (0:ℝ)))
    (hrimm : ∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) r t))
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (w : EuclideanSpace ℝ (Fin n)) (e : ℝ),
      w ≠ 0 ∧ 0 < e ∧ c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ r t₀ ∈ c.source ∧
      (∀ t : ℝ, 0 ≤ t → |t - t₀| ≤ e → c (r t₀) + (t - t₀) • w ∈ c.target) ∧
      (∀ t : ℝ, 0 ≤ t → |t - t₀| ≤ e →
        r t = c.symm (c (r t₀) + (t - t₀) • w)) := by
  obtain ⟨c, w, e, hw, he, hc, hsrc, hgerm⟩ := rayStraightening (n := n) (M := M) hn hrsm hrimm ht₀
  -- the room row is a continuity statement at `t₀`
  have hcont : ContinuousAt (fun t : ℝ => c (r t₀) + (t - t₀) • w) t₀ := by fun_prop
  have hmem : (fun t : ℝ => c (r t₀) + (t - t₀) • w) t₀ ∈ c.target := by
    simpa using c.map_source hsrc
  have hev : ∀ᶠ t in 𝓝 t₀, c (r t₀) + (t - t₀) • w ∈ c.target :=
    hcont.eventually (c.open_target.mem_nhds hmem)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨c, w, min e (δ / 2), hw, lt_min he (by linarith), hc, hsrc, ?_, ?_⟩
  · intro t _ ht
    refine hδ ?_
    have h1 : |t - t₀| ≤ δ / 2 := le_trans ht (min_le_right _ _)
    rw [Metric.mem_ball, Real.dist_eq]
    linarith [abs_nonneg (t - t₀)]
  · intro t ht0 ht
    exact hgerm t ht0 (le_trans ht (min_le_left _ _))

end Work.Drive.Rays
