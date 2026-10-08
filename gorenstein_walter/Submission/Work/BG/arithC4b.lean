import Mathlib
import Submission.Work.BG.ThmABCDefs

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem arithC4b : Work.GW2.C16.ArithC4bProp := by
  -- `2 * (2K)² * d = 8N` reduces to `K² * d = N`, so `K ∣ N`; coprimality then forces `K = 1`.
  intro N K d _hodd hcop h
  have h2 : ((2 * K : ℕ) : ℤ) = 2 * (K : ℤ) := by push_cast; ring
  rw [h2] at h
  have h3 : (K : ℤ) ^ 2 * d = (N : ℤ) := by nlinarith [h]
  have hdvd : (K : ℤ) ∣ (N : ℤ) := ⟨(K : ℤ) * d, by rw [← h3]; ring⟩
  have hdvd' : K ∣ N := by exact_mod_cast hdvd
  rw [Nat.Coprime] at hcop
  rw [Nat.gcd_eq_left hdvd'] at hcop
  exact hcop

end Work.BG
