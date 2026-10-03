import Mathlib
import Submission.Work.Pert.Ksub2.deriv_phi_bounds_walk
import Submission.Work.Pert.deriv_phi_bounds_walk_at

/-!
# `Work.Pert.Ksub2.deriv_phi_bounds_walk_bdd`

The **bounded-radius** form of `Work.Pert.Ksub2.deriv_phi_bounds_walk`: here the radius `T₀` is not
produced by compactness of `K'` but is *tied to a supplied bound* `Tb` for `K'`
(`∀ w ∈ K', ‖w‖ ≤ Tb`, `1 ≤ Tb`), namely `T₀ ≤ Tb + 1`.

The content is the same two-sided uniform-in-`M` bound for `‖deriv φ₀‖` along the walk
`u, u+1, …, u+n = w` with `w ∈ K'` and `u` in the deep strip `Dstrip M (T₀+1)`.

Since `Dstrip M T = {-M-1 ≤ Re ≤ -M, |Im| ≤ T}` is monotone *increasing* in `T`, a caller who
already owns a radius `T₀` for `K'` cannot use a radius produced from compactness (which is
incomparable with `T₀`); it is therefore useful to have the conclusion at a radius `T₀` that is
guaranteed to satisfy `T₀ ≤ Tb + 1`.

The supplied `Tb` itself is the optimal choice: it is positive (from `1 ≤ Tb`), it bounds `K'` by
hypothesis, it satisfies `Tb ≤ Tb + 1`, and it is legitimate as the strip parameter, so the result
is exactly `Work.Pert.deriv_phi_bounds_walk_at` at `T₀ := Tb`.

* **Clause 1 (upper)**: for `i ≤ n` the ball `ball (u+i) ρe` lies in `Dφ` and `‖deriv φ₀‖ ≤ Ce₀`
  there — deep points by the asymptotic upper bound `deriv_phi_deep_upper`, shallow points because
  they are of the form `w - m` with `m ≤ m₀` bounded, so their `ρe`-balls sit inside the fixed
  compact `Z = ⋃_{m ≤ m₀} (cthickening ρe K' - m) ⊆ Dφ`, where `deriv φ₀` is bounded by compactness.
* **Clause 2 (lower)**: `cc₀ / M² ≤ ‖deriv φ₀ z‖` for `z ∈ Dφ` with `‖z - u‖ ≤ ρe`
  (`deriv_phi_strip_lower`).
-/

namespace Work.Pert.Ksub2

open MandelDim Complex Set Metric

noncomputable section

theorem deriv_phi_bounds_walk_bdd {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ} (hK'c : IsCompact K') (hK' : K' ⊆ d.Dφ) {Tb : ℝ} (hTb : ∀ w ∈ K', ‖w‖ ≤ Tb)
    (hTb1 : (1 : ℝ) ≤ Tb) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ Tb + 1 ∧ (∀ w ∈ K', ‖w‖ ≤ T₀) ∧
    ∃ ρe : ℝ, 0 < ρe ∧ (∀ w ∈ K', Metric.ball w ρe ⊆ d.Dφ) ∧
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∃ Ce₀ cc₀ : ℝ, 0 < Ce₀ ∧ 0 < cc₀ ∧
      ∀ M : ℝ, M₀ ≤ M → ∀ w ∈ K', ∀ u ∈ Work.Pert.Dstrip M (T₀ + 1), ∀ n : ℕ, u + (n : ℂ) = w →
        (∀ i : ℕ, i ≤ n → Metric.ball (u + (i : ℂ)) ρe ⊆ d.Dφ ∧
          ∀ z : ℂ, z ∈ d.Dφ → ‖z - (u + (i : ℂ))‖ ≤ ρe → ‖deriv d.φ z‖ ≤ Ce₀) ∧
        (∀ z : ℂ, z ∈ d.Dφ → ‖z - u‖ ≤ ρe → cc₀ / (M * M) ≤ ‖deriv d.φ z‖) := by
  -- `Tb` is positive because it dominates `1`.
  have hTbpos : 0 < Tb := lt_of_lt_of_le one_pos hTb1
  -- The `T₀`-parameterised walk bound, invoked at the radius `Tb` itself.
  obtain ⟨ρe, hρepos, hballw, M₀, hM₀pos, Ce₀, cc₀, hCe₀, hcc₀, hmain⟩ :=
    Work.Pert.deriv_phi_bounds_walk_at d hK'c hK' hTbpos hTb
  refine ⟨Tb, hTbpos, by linarith, hTb, ρe, hρepos, hballw, M₀, hM₀pos, Ce₀, cc₀,
    hCe₀, hcc₀, ?_⟩
  -- The strip `Dstrip M (Tb + 1)` of the conclusion is literally the strip of the inner statement.
  exact hmain

end

end Work.Pert.Ksub2
