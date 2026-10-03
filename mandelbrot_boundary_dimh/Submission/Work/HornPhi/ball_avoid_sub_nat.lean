import Mathlib

/-!
# A ball around `y` avoiding the discrete set `v - ℕ`

`{v - (k : ℂ) | k : ℕ}` is a discrete, closed subset of `ℂ`, so a point `y` outside it has
positive distance from it.  Concretely, the elements `v - k` with `k ≥ N` are eventually far
from `y` (`dist (v - k) y ≥ k - dist y v → ∞`), and the finitely many initial ones are each at
positive distance from `y` because `y ≠ v - k`.

This is the "pick `r > 0` with `ball y r ∩ (v - ℕ) = ∅`" step used to build local sections of the
Fatou coordinate `Φ` in `Work.HornPhi.horn_phi`.
-/

namespace Work.HornPhi

theorem ball_avoid_sub_nat {v y : ℂ} (h : ∀ k : ℕ, y ≠ v - (k : ℂ)) :
    ∃ r : ℝ, 0 < r ∧ ∀ k : ℕ, v - (k : ℂ) ∉ Metric.ball y r := by
  -- A uniform positive lower bound on `dist (v - k) y` for the finitely many `k < N`.
  have haux : ∀ N : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ k : ℕ, k < N → r ≤ dist (v - (k : ℂ)) y := by
    intro N
    induction N with
    | zero => exact ⟨1, one_pos, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ N ih =>
        obtain ⟨r, hr, hrk⟩ := ih
        have hd : 0 < dist (v - (N : ℂ)) y := by
          rw [dist_pos]; exact fun hcon => h N hcon.symm
        refine ⟨min r (dist (v - (N : ℂ)) y), lt_min hr hd, fun k hk => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
        · exact le_trans (min_le_left _ _) (hrk k hlt)
        · subst heq; exact min_le_right _ _
  -- Beyond `N`, the distance grows with `k`.
  obtain ⟨N, hN⟩ := exists_nat_gt (dist y v + 1)
  obtain ⟨r, hr, hrk⟩ := haux N
  refine ⟨min r 1, lt_min hr one_pos, fun k => ?_⟩
  rw [Metric.mem_ball, not_lt]
  rcases lt_or_ge k N with hk | hk
  · exact le_trans (min_le_left _ _) (hrk k hk)
  · have hk' : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkey : (k : ℝ) - dist y v ≤ ‖(y - v) + (k : ℂ)‖ := by
      have h1 := abs_norm_sub_norm_le (k : ℂ) (v - y)
      have h2 : ‖(k : ℂ)‖ = (k : ℝ) := norm_natCast k
      have h3 : ‖v - y‖ = dist y v := by rw [dist_eq_norm, norm_sub_rev]
      have h4 : (k : ℂ) - (v - y) = (y - v) + (k : ℂ) := by ring
      rw [h2, h3, h4] at h1
      exact (abs_le.mp h1).2
    have hd : 1 ≤ dist (v - (k : ℂ)) y := by
      rw [dist_eq_norm, show (v - (k : ℂ)) - y = -((y - v) + (k : ℂ)) by ring, norm_neg]
      linarith
    exact le_trans (min_le_right _ _) hd

end Work.HornPhi
