import Mathlib

open Filter
open scoped Topology

namespace Work.Param

/-- **A repelling fixed point of `z ↦ z² + c` attracts only itself.**

If `p` is a fixed point of `f z = z² + c` with repelling multiplier `‖2p‖ > 1`, then any orbit
converging to `p` must reach `p` in finitely many steps.

Indeed `‖f z - p‖ = ‖z - p‖ · ‖z + p‖` and for `z` close to `p` the second factor is `> 1`; so on a
small disc around `p` the map expands distances by a fixed factor `q > 1`.  If an orbit enters this
disc without hitting `p`, the distances `‖fⁿ x - p‖` are bounded below by a fixed positive number
while the orbit converges to `p` — a contradiction. -/
theorem repelling_eventual_eq {c p x : ℂ} (hfix : p ^ 2 + c = p) (hrep : 1 < ‖2 * p‖) (hlim : Filter.Tendsto (fun n : ℕ => (fun z : ℂ => z ^ 2 + c)^[n] x) Filter.atTop (nhds p)) : ∃ N : ℕ, (fun z : ℂ => z ^ 2 + c)^[N] x = p := by
  set f : ℂ → ℂ := fun z => z ^ 2 + c with hf
  have hc : c = p - p ^ 2 := by linear_combination hfix
  have hr : 0 < (‖2 * p‖ - 1) / 2 := by linarith
  have hq1 : 1 < (‖2 * p‖ + 1) / 2 := by linarith
  have hqr : (‖2 * p‖ + 1) / 2 = ‖2 * p‖ - (‖2 * p‖ - 1) / 2 := by ring
  -- Local expansion: on the disc of radius `(‖2p‖-1)/2` the map multiplies the distance to `p`
  -- by at least `q = (‖2p‖+1)/2 > 1`.
  have key : ∀ z : ℂ, ‖z - p‖ ≤ (‖2 * p‖ - 1) / 2 →
      (‖2 * p‖ + 1) / 2 * ‖z - p‖ ≤ ‖z ^ 2 + c - p‖ := by
    intro z hz
    have hsub : z ^ 2 + c - p = (z - p) * (z + p) := by rw [hc]; ring
    have hzp : (‖2 * p‖ + 1) / 2 ≤ ‖z + p‖ := by
      have h2p : 2 * p = (z + p) - (z - p) := by ring
      have htri : ‖2 * p‖ ≤ ‖z + p‖ + ‖z - p‖ := by
        calc ‖2 * p‖ = ‖(z + p) - (z - p)‖ := by rw [h2p]
          _ ≤ ‖z + p‖ + ‖z - p‖ := norm_sub_le _ _
      rw [hqr]
      linarith
    calc (‖2 * p‖ + 1) / 2 * ‖z - p‖ ≤ ‖z + p‖ * ‖z - p‖ :=
          mul_le_mul_of_nonneg_right hzp (norm_nonneg _)
      _ = ‖z ^ 2 + c - p‖ := by rw [hsub, norm_mul]; ring
  -- The orbit eventually enters the disc.
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) ((‖2 * p‖ - 1) / 2) hr
  have hNr : ∀ n ≥ N, ‖f^[n] x - p‖ < (‖2 * p‖ - 1) / 2 := by
    intro n hn; have := hN n hn; rwa [dist_eq_norm] at this
  by_cases hxp : f^[N] x = p
  · exact ⟨N, hxp⟩
  · -- Otherwise the orbit stays at distance ≥ `‖f^[N] x - p‖ > 0` from `p` forever.
    exfalso
    have hpos : 0 < ‖f^[N] x - p‖ := by
      rw [norm_pos_iff]; exact sub_ne_zero.mpr hxp
    obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp hlim) ‖f^[N] x - p‖ hpos
    have hA : ∀ n, N ≤ n → ‖f^[N] x - p‖ ≤ ‖f^[n] x - p‖ := by
      intro n hn
      refine Nat.le_induction (m := N)
        (P := fun n _ => ‖f^[N] x - p‖ ≤ ‖f^[n] x - p‖) ?base ?step n hn
      · rfl
      · intro k hk ih
        have hkr : ‖f^[k] x - p‖ ≤ (‖2 * p‖ - 1) / 2 := le_of_lt (hNr k hk)
        have hk2 : (‖2 * p‖ + 1) / 2 * ‖f^[k] x - p‖ ≤ ‖f^[k+1] x - p‖ := by
          have h := key (f^[k] x) hkr
          have hstep : f^[k+1] x = (f^[k] x)^2 + c := by
            simp only [Function.iterate_succ_apply', hf]
          rwa [hstep]
        exact le_trans ih
          (le_trans (le_mul_of_one_le_left (norm_nonneg _) (le_of_lt hq1)) hk2)
    have h1 := hA (max N M) (le_max_left _ _)
    have h2 : ‖f^[max N M] x - p‖ < ‖f^[N] x - p‖ := by
      have := hM (max N M) (le_max_right _ _)
      rwa [dist_eq_norm] at this
    linarith

end Work.Param
