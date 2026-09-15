import Mathlib
import Submission.Commons.NumberTheory.Sieve.card_omega_pair

namespace Commons.NumberTheory.Sieve

theorem card_omega_pair_gen {p : ℕ} [Fact p.Prime] {t : ℕ} (ht : 2 ≤ t) {W : ZMod p} (L L' : Fin t → ZMod p) (hL : L ≠ 0) (hne : ∀ c : ZMod p, L' ≠ c • L) (b b' : ZMod p) : ((Finset.univ : Finset (Fin t → ZMod p)).filter (fun x => W * ((∑ j, L j * x j) + b) + 1 = 0 ∧ W * ((∑ j, L' j * x j) + b') + 1 = 0)).card ≤ if W = 0 then 0 else p ^ (t - 2) := by
  classical
  have hL' : L' ≠ 0 := by
    have h := hne 0
    rw [zero_smul] at h
    exact h
  by_cases hW : W = 0
  · rw [if_pos hW]
    have hcard : ((Finset.univ : Finset (Fin t → ZMod p)).filter
        (fun x => W * ((∑ j, L j * x j) + b) + 1 = 0 ∧
                  W * ((∑ j, L' j * x j) + b') + 1 = 0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hx1, _⟩ := hx.2
      rw [hW] at hx1
      simp only [zero_mul, zero_add] at hx1
      exact one_ne_zero hx1
    exact le_of_eq hcard
  · rw [if_neg hW]
    have hpred : ∀ x : Fin t → ZMod p,
        (W * ((∑ j, L j * x j) + b) + 1 = 0 ∧
         W * ((∑ j, L' j * x j) + b') + 1 = 0)
          ↔ ((∑ j, L j * x j) = -W⁻¹ - b ∧ (∑ j, L' j * x j) = -W⁻¹ - b') := by
      intro x
      rw [mul_add_one_eq_zero_iff hW, mul_add_one_eq_zero_iff hW]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [← h1]; ring, by rw [← h2]; ring⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [h1]; ring, by rw [h2]; ring⟩
    have hS_eq : ((Finset.univ : Finset (Fin t → ZMod p)).filter
        (fun x => W * ((∑ j, L j * x j) + b) + 1 = 0 ∧
                  W * ((∑ j, L' j * x j) + b') + 1 = 0))
        = (Finset.univ : Finset (Fin t → ZMod p)).filter
          (fun x => (∑ j, L j * x j) = -W⁻¹ - b ∧
                    (∑ j, L' j * x j) = -W⁻¹ - b') :=
      Finset.filter_congr (fun x _ => hpred x)
    rw [hS_eq]
    exact Commons.LinearAlgebra.ZMod.pair_affine_hyperplanes_card ht L L' hL hL' hne (-W⁻¹ - b) (-W⁻¹ - b')

end Commons.NumberTheory.Sieve
