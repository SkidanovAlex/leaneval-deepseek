import Mathlib.Data.Nat.Prime.Defs
import Submission.Commons.Combinatorics.Transference.exists_shift_boundary_cover

namespace Commons.Combinatorics.Transference

theorem exists_boundary_family {p : ℕ} [Fact p.Prime] {K : ℕ} (G' : Fin K → ZMod p → ℝ)
    (ν : ZMod p → ℝ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1)
    (hν : ∀ x, 0 ≤ ν x) :
    ∃ (α : Fin K → ℝ) (T : Fin K → Finset (ZMod p)),
      (∀ j, 0 ≤ α j ∧ α j < ε) ∧
      (∀ (j : Fin K) (y : ZMod p),
        (∃ n : ℤ, |(G' j y - α j) / ε - n| ≤ η) → y ∈ T j) ∧
      ∑ j, ∑ y ∈ T j, (ν y + 1) ≤ (K : ℝ) * (3 * η * ∑ x, (ν x + 1)) := by
  classical
  have hν1 : ∀ x : ZMod p, 0 ≤ ν x + 1 := fun x => by linarith [hν x]
  have hforall : ∀ j : Fin K, ∃ (α : ℝ) (T : Finset (ZMod p)),
      0 ≤ α ∧ α < ε ∧
      (∀ y : ZMod p, (∃ n : ℤ, |(G' j y - α) / ε - n| ≤ η) → y ∈ T) ∧
      ∑ y ∈ T, (ν y + 1) ≤ 3 * η * ∑ x, (ν x + 1) := by
    intro j
    obtain ⟨α, hα0, hαε, T, hT, hsum⟩ :=
      exists_shift_boundary_cover (G' j) ν hε hη hη1 hν1
    exact ⟨α, T, hα0, hαε, hT, hsum⟩
  choose α T hα0 hαε hT hsum using hforall
  refine ⟨α, T, ?_, ?_, ?_⟩
  · intro j; exact ⟨hα0 j, hαε j⟩
  · intro j y hy; exact hT j y hy
  · calc ∑ j : Fin K, ∑ y ∈ T j, (ν y + 1)
        ≤ ∑ j : Fin K, (3 * η * ∑ x, (ν x + 1)) :=
          Finset.sum_le_sum (fun j _ => hsum j)
      _ = (K : ℝ) * (3 * η * ∑ x, (ν x + 1)) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

end Commons.Combinatorics.Transference