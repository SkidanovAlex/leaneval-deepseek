import Mathlib
import Submission.Commons.LinearAlgebra.ZMod.affine_hyperplane_card
import Submission.Commons.LinearAlgebra.ZMod.pair_affine_hyperplanes_card

namespace Commons.NumberTheory.Sieve

/-- For `W ≠ 0`, the affine equation `W * s + 1 = 0` is equivalent to `s = -W⁻¹`. -/
lemma mul_add_one_eq_zero_iff {k : Type*} [Field k] {W s : k} (hW : W ≠ 0) :
    W * s + 1 = 0 ↔ s = -W⁻¹ := by
  have hWneg : W * (-W⁻¹) = -1 := by
    rw [mul_neg, mul_inv_cancel₀ hW]
  constructor
  · intro h
    have hs : W * s = -1 := add_eq_zero_iff_eq_neg.mp h
    rw [← hWneg] at hs
    exact mul_left_cancel₀ hW hs
  · intro h
    rw [h, hWneg]
    ring

theorem card_omega_pair {p : ℕ} [Fact p.Prime] {t : ℕ} (ht : 2 ≤ t) {W : ZMod p}
    (L L' : Fin t → ZMod p) (hL : L ≠ 0) (hne : ∀ c : ZMod p, L' ≠ c • L) :
    ((Finset.univ : Finset (Fin t → ZMod p)).filter
        (fun x => W * (∑ j, L j * x j) + 1 = 0 ∧ W * (∑ j, L' j * x j) + 1 = 0)).card
      ≤ if W = 0 then 0 else p ^ (t - 2) := by
  classical
  have hL' : L' ≠ 0 := by
    have h := hne 0
    rw [zero_smul] at h
    exact h
  by_cases hW : W = 0
  · rw [if_pos hW]
    have hcard : ((Finset.univ : Finset (Fin t → ZMod p)).filter
        (fun x => W * (∑ j, L j * x j) + 1 = 0 ∧ W * (∑ j, L' j * x j) + 1 = 0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hx1, hx2⟩ := hx.2
      rw [hW] at hx1
      simp only [zero_mul, zero_add] at hx1
      exact one_ne_zero hx1
    exact le_of_eq hcard
  · rw [if_neg hW]
    have hpred : ∀ x : Fin t → ZMod p,
        (W * (∑ j, L j * x j) + 1 = 0 ∧ W * (∑ j, L' j * x j) + 1 = 0)
          ↔ ((∑ j, L j * x j) = -W⁻¹ ∧ (∑ j, L' j * x j) = -W⁻¹) := by
      intro x
      rw [mul_add_one_eq_zero_iff hW, mul_add_one_eq_zero_iff hW]
    have hS_eq : ((Finset.univ : Finset (Fin t → ZMod p)).filter
        (fun x => W * (∑ j, L j * x j) + 1 = 0 ∧ W * (∑ j, L' j * x j) + 1 = 0))
        = (Finset.univ : Finset (Fin t → ZMod p)).filter
          (fun x => (∑ j, L j * x j) = -W⁻¹ ∧ (∑ j, L' j * x j) = -W⁻¹) := by
      exact Finset.filter_congr (fun x _ => hpred x)
    rw [hS_eq]
    exact Commons.LinearAlgebra.ZMod.pair_affine_hyperplanes_card ht L L' hL hL' hne (-W⁻¹) (-W⁻¹)

end Commons.NumberTheory.Sieve
