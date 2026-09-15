import Mathlib
import Submission.Commons.LinearAlgebra.ZMod.affine_hyperplane_card

namespace Commons.NumberTheory.Sieve

theorem card_omega_one_gen {p : ℕ} [Fact p.Prime] {t : ℕ} (ht : 1 ≤ t) {W : ZMod p} (hW : W ≠ 0) (L : Fin t → ZMod p) (hL : L ≠ 0) (b : ZMod p) : ((Finset.univ : Finset (Fin t → ZMod p)).filter (fun x => W * ((∑ j, L j * x j) + b) + 1 = 0)).card = p ^ (t - 1) := by
  classical
  have hpred : ∀ x : Fin t → ZMod p,
      (W * ((∑ j, L j * x j) + b) + 1 = 0) ↔ (∑ j, L j * x j = -W⁻¹ - b) := by
    intro x
    constructor
    · intro h
      have h1 : W * ((∑ j, L j * x j) + b) = -1 := (add_eq_zero_iff_eq_neg).mp h
      have h2 : (∑ j, L j * x j) + b = W⁻¹ * (-1) := (eq_inv_mul_iff_mul_eq₀ hW).mpr h1
      have h2' : (∑ j, L j * x j) + b = -W⁻¹ := by
        rw [h2]; ring
      exact (eq_sub_iff_add_eq).mpr h2'
    · intro h
      have hb : (∑ j, L j * x j) + b = -W⁻¹ := by rw [h]; ring
      rw [hb, mul_neg, mul_inv_cancel₀ hW]
      ring
  rw [Finset.filter_congr (fun x _ => hpred x)]
  exact Commons.LinearAlgebra.ZMod.affine_hyperplane_card ht L hL (-W⁻¹ - b)

end Commons.NumberTheory.Sieve
