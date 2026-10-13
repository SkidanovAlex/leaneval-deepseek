import Mathlib
import Submission.Work.WilC4.ULPMDefs

namespace Work.WilVP

/-- **The free window puts `u` on the same side as `s`.**

If `B` avoids the window `[s/(2N), 2N·s]` and `u` lies within the middle half of the
multiplicative neighborhood of `s` (i.e. `|u - s| < s/2`, so `s/2 < u < 3s/2`), then `u` and `s`
are on the same side of every breakpoint of `B` at distance `> N`:

* a breakpoint `b < s/(2N)` satisfies `N·b < s/2 < u` and `N·b < s`;
* a breakpoint `b > 2N·s` satisfies `N·s < 2N·s < b` and `N·u < 3N·s/2 < 2N·s < b`. -/
lemma sameSide_of_free_window {N : ℕ} {B : Set ℝ} {s u : ℝ}
    (hN : 0 < N) (hs : 0 < s)
    (hfree : ∀ b ∈ B, ¬ (s / (2 * N) ≤ b ∧ b ≤ 2 * N * s))
    (hu : |u - s| < s / 2) : Work.WilC4.Route.SameSide N B u s := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hu_lo : s / 2 < u := by
    rw [abs_lt] at hu; linarith [hu.1]
  have hu_hi : u < 3 * s / 2 := by
    rw [abs_lt] at hu; linarith [hu.2]
  intro b hb
  rcases not_and_or.mp (hfree b hb) with h | h
  · left
    have hb' : b < s / (2 * (N:ℝ)) := not_le.mp h
    have hkey : (N:ℝ) * b < s / 2 := by
      have h1 := mul_lt_mul_of_pos_left hb' hNpos
      have heq : (N:ℝ) * (s / (2 * (N:ℝ))) = s / 2 := by field_simp
      rw [heq] at h1; exact h1
    exact ⟨by linarith, by linarith⟩
  · right
    have hb' : 2 * (N:ℝ) * s < b := not_le.mp h
    exact ⟨by nlinarith [hNpos, hs, hu_hi, hb'], by nlinarith [hNpos, hs, hb']⟩

end Work.WilVP
