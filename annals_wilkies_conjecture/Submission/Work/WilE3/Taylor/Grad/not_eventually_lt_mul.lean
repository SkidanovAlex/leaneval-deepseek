import Mathlib

namespace Work.WilE3.Taylor.Grad

/-- If `u → cu > 0` and `v → cv` as `t → 0⁺`, then `u t < t ^ d * v t` cannot hold
eventually on `(0, ∞)`: since `t ^ d → 0` and `v` is bounded near `0`, the right-hand side
tends to `0`, while `u` stays bounded away from `0` by `cu / 2`. -/
theorem not_eventually_lt_mul {u v : ℝ → ℝ} {d : ℕ} (hd : 0 < d) {cu cv : ℝ} (hcu : 0 < cu) (hu : Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds cu)) (hv : Filter.Tendsto v (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds cv)) (hineq : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), u t < t ^ d * v t) : False := by
  -- `t ↦ t ^ d` tends to `0 ^ d = 0` as `t → 0`; restrict to `(0, ∞)`.
  have hpow : Filter.Tendsto (fun t : ℝ => t ^ d) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := (continuousAt_pow (0 : ℝ) d).tendsto
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hd)] at h
    exact h.mono_left inf_le_left
  -- hence `t ↦ t ^ d * v t` tends to `0 * cv = 0`.
  have hprod : Filter.Tendsto (fun t : ℝ => t ^ d * v t) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := hpow.mul hv
    rwa [zero_mul] at h
  -- eventually `t ^ d * v t < cu / 2`
  have hlt : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ^ d * v t < cu / 2 :=
    Filter.Tendsto.eventually_lt_const (by linarith) hprod
  -- eventually `cu / 2 < u t`
  have hgt : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), cu / 2 < u t :=
    (tendsto_order.mp hu).1 (cu / 2) (by linarith)
  -- contradiction with the hypothesis `u t < t ^ d * v t`
  have hcontra : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), False := by
    filter_upwards [hineq, hlt, hgt] with t h1 h2 h3
    linarith
  exact hcontra.exists.elim (fun t ht => ht)

end Work.WilE3.Taylor.Grad
