import Mathlib
import Submission.Work.SG.SGsepDefs

namespace Work.SGsep

open Work.SG

/-- Minimality of the order of a vector modulo a lattice: if `IsOrdOf L u o` and `d` is a
positive divisor of `o` with `d • u ∈ L`, then `d = o`.  (Otherwise `o = d * m` with `m > 1`,
and taking a prime `p ∣ m` gives a proper divisor `o / p = d * (m / p)` with `(o/p) • u ∈ L`,
contradicting the minimality clause of `IsOrdOf`.) -/
theorem IsOrdOf_eq_of_dvd_smul_mem {L : AddSubgroup (Fin 3 → ℝ)} {u : Fin 3 → ℝ} {o d : ℕ}
    (h : Work.SG.IsOrdOf L u o) (hdvd : d ∣ o) (hdpos : 0 < d) (hs : (d : ℤ) • u ∈ L) : d = o := by
  by_contra hne
  obtain ⟨h1, h2, h3⟩ := h
  -- `d > 0` (recorded; it is what makes `o / d` an honest "complementary factor").
  have hd0 : 0 < d := hdpos
  set m := o / d
  have ho : d * m = o := Nat.mul_div_cancel' hdvd
  -- `m ≠ 1`, else `o = d`.
  have hmne : m ≠ 1 := by
    intro hmm
    rw [hmm, mul_one] at ho
    exact hne ho
  -- pick a prime `p ∣ m`; then `p ∣ o` and `o / p = d * (m / p)` is a proper divisor of `o`
  -- with `(o / p) • u ∈ L`, contradicting minimality.
  obtain ⟨p, hpp, hpm⟩ := Nat.exists_prime_and_dvd hmne
  have hpo : p ∣ o := by rw [← ho]; exact Dvd.dvd.mul_left hpm d
  have hdiv : o / p = d * (m / p) := by
    have hm : m = p * (m / p) := (Nat.mul_div_cancel' hpm).symm
    have h2' : d * m = p * (d * (m / p)) := by nth_rewrite 1 [hm]; ring
    rw [← ho, h2', Nat.mul_div_cancel_left (d * (m / p)) hpp.pos]
  have hmem : (((o / p : ℕ)) : ℤ) • u ∈ L := by
    rw [hdiv]
    have hcast : ((d * (m / p) : ℕ) : ℤ) = ((m / p : ℕ) : ℤ) * (d : ℤ) := by
      push_cast; ring
    rw [hcast, mul_zsmul]
    exact L.zsmul_mem hs _
  exact h3 p hpp hpo hmem

end Work.SGsep
