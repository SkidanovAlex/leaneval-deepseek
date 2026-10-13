import Mathlib
import Submission.Work.WilE9.Sharp.hasFDerivAt_of_lineDiff

namespace Work.WilE9.Sharp

/-!
# Uniform line increment bound

If `f : ℝⁿ → ℝ` has, at every point `p` of an open set `U`, a directional derivative along each
coordinate direction `eᵢ` equal to `g i p` (in the little-o sense `hl`), and each `g i` is
continuous at a point `y ∈ U`, then the differentiability along the coordinate axes is *uniform*
in a neighbourhood of `y`: for every `ε > 0` there is `δ > 0` such that for all `z` with
`‖z - y‖ < δ`, all `i` and all `|a| < δ`,

`|f (z + a • eᵢ) - f z - a * (g i y)| ≤ ε * |a|`.

The naive bound `|f (z + a eᵢ) - f z - a g i z| ≤ ε|a|` (available at each `z` separately) plus
`|g i z - g i y| ≤ ε` is *not* enough, because the modulus of the first estimate depends on `z`.
Instead we subtract the *fixed* linear term `a * g i y` and use the one dimensional mean value
theorem on the segment `[z, z + a eᵢ]`: the derivative of `t ↦ f (z + t eᵢ) - t * g i y` is
`g i (z + t eᵢ) - g i y`, which is bounded by `ε` on the whole segment because `g i` is continuous
at `y`.  This is exactly the content of the colleague's lemma `LineDiffAux.lineDeriv_bound`; here
we only have to produce the two hypotheses it asks for, choosing a ball around `y` that lies
inside `U` and on which all the `g i` are within `ε` of `g i y`.
-/

theorem line_inc_uniform_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (g : Fin n → (Fin n → ℝ) → ℝ)
    (hl : ∀ i, ∀ p ∈ U, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ, 0 < |t| → |t| < δ →
          |f (p + t • Pi.single i (1 : ℝ)) - f p - t * g i p| ≤ ε * |t|)
    {y : Fin n → ℝ} (hy : y ∈ U) (hg : ∀ i, ContinuousAt (g i) y) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (z : Fin n → ℝ), ‖z - y‖ < δ → ∀ (i : Fin n) (a : ℝ), |a| < δ →
      |f (z + a • Pi.single i (1 : ℝ)) - f z - a * g i y| ≤ ε * |a| := by
  -- A ball around `y` contained in the open set `U`.
  obtain ⟨ρ, hρpos, hρU⟩ := Metric.isOpen_iff.mp hU y hy
  -- Continuity of the whole vector of coordinate derivatives at `y`.
  have hG : ContinuousAt (fun w : Fin n → ℝ => fun i => g i w) y := by
    rw [continuousAt_pi]
    exact hg
  rw [Metric.continuousAt_iff] at hG
  obtain ⟨δg, hδgpos, hδg⟩ := hG ε hε
  -- Work with the radius `min ρ δg / 2`: a step of length `< min ρ δg / 2` then stays closer
  -- than `min ρ δg` to `y`, hence inside `U` and inside the continuity ball of `g`.
  have hδpos : 0 < min ρ δg / 2 := by
    have : 0 < min ρ δg := lt_min hρpos hδgpos
    linarith
  refine ⟨min ρ δg / 2, hδpos, ?_⟩
  intro z hz i a ha
  have hmun : min ρ δg / 2 + min ρ δg / 2 = min ρ δg := by ring
  -- Every point of the segment `[z, z + a eᵢ]` stays within `min ρ δg` of `y`.
  have hstrict : ∀ s : ℝ, s ∈ Set.uIcc (0:ℝ) a →
      ‖z + s • Pi.single i (1:ℝ) - y‖ < min ρ δg := by
    intro s hs
    have hsabs : |s| ≤ |a| := LineDiffAux.abs_le_abs_of_mem_uIcc hs
    have hdist : ‖z + s • Pi.single i (1:ℝ) - y‖ ≤ ‖z - y‖ + |s| := by
      have he : z + s • Pi.single i (1:ℝ) - y = (z - y) + (s • Pi.single i (1:ℝ)) := by abel
      rw [he]
      calc ‖(z - y) + s • Pi.single i (1:ℝ)‖
          ≤ ‖z - y‖ + ‖s • Pi.single i (1:ℝ)‖ := norm_add_le _ _
        _ = ‖z - y‖ + |s| := by
              rw [norm_smul, Real.norm_eq_abs, LineDiffAux.norm_pi_single_one, mul_one]
    calc ‖z + s • Pi.single i (1:ℝ) - y‖ ≤ ‖z - y‖ + |s| := hdist
      _ < min ρ δg / 2 + min ρ δg / 2 := add_lt_add hz (lt_of_le_of_lt hsabs ha)
      _ = min ρ δg := hmun
  -- Assemble the two hypotheses of the one dimensional mean value estimate.
  exact LineDiffAux.lineDeriv_bound (i := i) (a := z) (y := y) (t := a) (ε := ε) hl
    (fun s hs => hρU (by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_lt_of_le (hstrict s hs) (min_le_left _ _)))
    (fun s hs => by
      have hw := hstrict s hs
      have hdist : dist (z + s • Pi.single i (1:ℝ)) y < δg := by
        rw [dist_eq_norm]
        exact lt_of_lt_of_le hw (min_le_right _ _)
      have hgd : dist (fun j => g j (z + s • Pi.single i (1:ℝ))) (fun j => g j y) < ε :=
        hδg hdist
      have hgd' : ‖(fun j => g j (z + s • Pi.single i (1:ℝ))) - (fun j => g j y)‖ < ε := by
        simpa only [dist_eq_norm] using hgd
      have h1 := norm_le_pi_norm
        ((fun j => g j (z + s • Pi.single i (1:ℝ))) - (fun j => g j y)) i
      have h1' : ‖g i (z + s • Pi.single i (1:ℝ)) - g i y‖
          ≤ ‖(fun j => g j (z + s • Pi.single i (1:ℝ))) - (fun j => g j y)‖ := by
        simpa only [Pi.sub_apply] using h1
      exact le_of_lt (lt_of_le_of_lt h1' hgd'))

end Work.WilE9.Sharp
