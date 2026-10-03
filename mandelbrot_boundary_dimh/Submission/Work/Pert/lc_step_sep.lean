import Mathlib

namespace Work.Pert

theorem lc_step_sep {H : ℕ → ℝ} {n : ℕ}
    (hstep : ∀ j, j < n → H (j + 1) ≤ H j - 15 / 16) :
    ∀ j j' : ℕ, j ≤ j' → j' ≤ n → H j' ≤ H j - (15 / 16) * ((j' - j : ℕ) : ℝ) := by
  have key : ∀ d j, j + d ≤ n → H (j + d) ≤ H j - (15 / 16) * (d : ℝ) := by
    intro d
    induction d with
    | zero => intro j _; simp
    | succ d ih =>
      intro j hj
      have hjn : j < n := by omega
      have h1 : H (j + 1) ≤ H j - 15 / 16 := hstep j hjn
      have h2 : H ((j + 1) + d) ≤ H (j + 1) - (15 / 16) * (d : ℝ) := ih (j + 1) (by omega)
      rw [show j + (d + 1) = (j + 1) + d from by omega]
      push_cast
      linarith
  intro j j' hjj hj'n
  have h := key (j' - j) j (by omega)
  rwa [Nat.add_sub_of_le hjj] at h

end Work.Pert
