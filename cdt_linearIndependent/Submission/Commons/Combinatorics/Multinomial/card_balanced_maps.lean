import Mathlib
import Submission.Commons.Combinatorics.Fintype.sum_piFinset_ite_card_eq_multinomial

namespace Commons.Combinatorics.Multinomial

open Finset

theorem card_balanced_maps (m d : ℕ) (hm : 0 < m) (hmd : m ∣ d) :
    (Finset.univ.filter (fun g : Fin d → Fin m =>
        ∀ x : Fin m, (Finset.univ.filter (fun c : Fin d => g c = x)).card = d / m)).card
      = Nat.multinomial Finset.univ (fun _ : Fin m => d / m) := by
  classical
  have hp : ∑ _ : Fin m, d / m = d := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simpa using Nat.mul_div_cancel' hmd
  have h := Commons.Combinatorics.Fintype.sum_piFinset_ite_card_eq_multinomial
    (α := Fin m) (R := ℕ) (p := fun _ : Fin m => d / m) (k := d)
    (by simpa using hp) (fun _ => (1 : ℕ))
  rw [Fintype.piFinset_univ] at h
  simp only [one_pow, Finset.prod_const_one, mul_one] at h
  rw [Finset.sum_boole] at h
  exact h

end Commons.Combinatorics.Multinomial
