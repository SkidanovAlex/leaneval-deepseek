import Mathlib
import Submission.Work.Diff.GE.MovingFrame.multilinear_eventually_bounded
import Submission.Work.Diff.GE.MovingFrame.prod_piecewise_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.MovingFrame

open scoped BigOperators
open Filter

/-- If a family of five-fold multilinear forms converges pointwise along a filter `l`, and a family
of tuples `u s` converges along `l`, then the values converge: `Φ s (u s) → L u₀`.

WARNING (a false shortcut): for arity `5` one must NOT use `Φ s (u s) - Φ s u₀ = Φ s (u s - u₀)`.
Instead write `u s = (u s - u₀) + u₀` and use the multilinear expansion
`MultilinearMap.map_add_univ`: `Φ s (δ + u₀) = ∑ T, Φ s (T.piecewise δ u₀)`; the term `T = ∅` is
`Φ s u₀ → L u₀`, and each term with `T ≠ ∅` is bounded by `C * (M^4 * c)` where `C` is the eventual
operator-norm bound of `Φ` (`multilinear_eventually_bounded`), `M` bounds `‖u₀ i‖` and `c` bounds
`‖δ i‖` (`prod_piecewise_le`), so the sum of the `2^5 - 1` higher-order terms tends to `0`. -/
theorem tendsto_multilinear_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter ℝ} (Φ : ℝ → MultilinearMap ℝ (fun _ : Fin 5 => V) ℝ)
    (L : (Fin 5 → V) → ℝ) (u : ℝ → Fin 5 → V) (u₀ : Fin 5 → V)
    (hΦ : ∀ w : Fin 5 → V, Filter.Tendsto (fun s => Φ s w) l (nhds (L w)))
    (hu : Filter.Tendsto u l (nhds u₀)) :
    Filter.Tendsto (fun s => Φ s (u s)) l (nhds (L u₀)) := by
  -- Step 1 : the family `Φ s` is eventually bounded in operator norm.
  obtain ⟨C, hC⟩ := multilinear_eventually_bounded Φ L hΦ
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hCbdd : ∀ᶠ s in l, ∀ w : Fin 5 → V, ‖Φ s w‖ ≤ max C 0 * ∏ i, ‖w i‖ := by
    filter_upwards [hC] with s hs
    intro w
    have hnn : 0 ≤ ∏ i, ‖w i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
    rw [Real.norm_eq_abs]
    exact (hs w).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) hnn)
  -- Step 2 : `u s - u₀ → 0`.
  have hsub : Tendsto (fun s => u s - u₀) l (nhds 0) := by
    simpa using hu.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => u₀) l (nhds u₀))
  have hnorm : Tendsto (fun s => ‖u s - u₀‖) l (nhds 0) := by
    simpa using hsub.norm
  -- Step 3 : `u s` stays bounded.
  have hubdd : ∀ᶠ s in l, ‖u s‖ ≤ ‖u₀‖ + 1 := by
    have h : Tendsto (fun s => ‖u s‖) l (nhds ‖u₀‖) := hu.norm
    filter_upwards [Metric.tendsto_nhds.1 h 1 zero_lt_one] with s hs
    have hs' : |‖u s‖ - ‖u₀‖| < 1 := by simpa [Real.dist_eq] using hs
    linarith [(abs_lt.1 hs').2]
  set N : ℝ := ↑(Fintype.card (Fin 5)) with hN
  set K : ℝ := max C 0 * N * (‖u₀‖ + 1) ^ (Fintype.card (Fin 5) - 1) with hK
  -- Step 4 : `Φ s (u s) - Φ s u₀ → 0`, by the multilinear difference bound.
  have hdiff : Tendsto (fun s => Φ s (u s) - Φ s u₀) l (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (g := fun s : ℝ => K * ‖u s - u₀‖)
      (Eventually.of_forall fun s => norm_nonneg _) ?_ ?_
    · filter_upwards [hCbdd, hubdd] with s hs hu'
      rw [sub_zero, hK, hN]
      have h1 := (Φ s).norm_image_sub_le_of_bound hC0 hs (u s) u₀
      have hm : max ‖u s‖ ‖u₀‖ ≤ ‖u₀‖ + 1 :=
        max_le hu' (by linarith [norm_nonneg u₀])
      have hpow : (max ‖u s‖ ‖u₀‖) ^ (Fintype.card (Fin 5) - 1)
          ≤ (‖u₀‖ + 1) ^ (Fintype.card (Fin 5) - 1) :=
        pow_le_pow_left₀ (le_trans (norm_nonneg _) (le_max_left _ _)) hm _
      have hd : 0 ≤ ‖u s - u₀‖ := norm_nonneg _
      calc ‖Φ s (u s) - Φ s u₀‖
          ≤ max C 0 * ↑(Fintype.card (Fin 5)) *
              (max ‖u s‖ ‖u₀‖) ^ (Fintype.card (Fin 5) - 1) * ‖u s - u₀‖ := h1
        _ = (max C 0 * ↑(Fintype.card (Fin 5))) *
              ((max ‖u s‖ ‖u₀‖) ^ (Fintype.card (Fin 5) - 1) * ‖u s - u₀‖) := by ring
        _ ≤ (max C 0 * ↑(Fintype.card (Fin 5))) *
              ((‖u₀‖ + 1) ^ (Fintype.card (Fin 5) - 1) * ‖u s - u₀‖) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hpow hd)
                (mul_nonneg (le_max_right _ _) (Nat.cast_nonneg _))
        _ = (max C 0 * ↑(Fintype.card (Fin 5)) *
              (‖u₀‖ + 1) ^ (Fintype.card (Fin 5) - 1)) * ‖u s - u₀‖ := by ring
    · have hlim := hnorm.const_mul K
      simpa using hlim
  -- Step 5 : add back the limit term.
  have hsum := hdiff.add (hΦ u₀)
  have hfun : (fun s : ℝ => (Φ s (u s) - Φ s u₀) + Φ s u₀) = fun s => Φ s (u s) := by
    funext s; ring
  rw [hfun] at hsum
  simpa using hsum

end Work.Diff.GE.MovingFrame
