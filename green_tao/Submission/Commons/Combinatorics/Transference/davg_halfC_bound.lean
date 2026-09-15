import Mathlib
import Submission.Commons.Combinatorics.Transference.cube_lfc_half
import Submission.Commons.Combinatorics.Transference.davg_bound

namespace Commons.Combinatorics.Transference

theorem davg_halfC_bound {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) (ν F : ZMod p → ℝ)
    (hν : ∀ x, 0 ≤ ν x) {C : ℝ} (hC : 1 ≤ C) (hF : ∀ x, |F x| ≤ C * (ν x + 1))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hLFC : ∀ A : Finset (Fin d → Bool), A ⊆ Finset.univ.erase (0 : Fin d → Bool) →
      A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin d → ZMod p,
          ∏ ω ∈ A, ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) - 1| ≤ ε) :
    ∀ x, |davg d (fun y => F y / (2 * C)) x| ≤ (2 : ℝ) ^ (2 ^ d - 1) * (1 + ε) := by
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC
  have h2C : (0 : ℝ) < 2 * C := by linarith
  have hLFC' := cube_lfc_half ν hε hLFC
  have hF' : ∀ x, |F x / (2 * C)| ≤ (ν x + 1) / 2 + 1 := by
    intro x
    rw [abs_div, abs_of_pos h2C]
    calc |F x| / (2 * C) ≤ (C * (ν x + 1)) / (2 * C) :=
          div_le_div_of_nonneg_right (hF x) (le_of_lt h2C)
      _ = (ν x + 1) / 2 := by field_simp
      _ ≤ (ν x + 1) / 2 + 1 := le_add_of_nonneg_right zero_le_one
  intro x
  exact davg_bound hd (fun y => (ν y + 1) / 2) (fun y => F y / (2 * C)) hF' hε hLFC' x

end Commons.Combinatorics.Transference
