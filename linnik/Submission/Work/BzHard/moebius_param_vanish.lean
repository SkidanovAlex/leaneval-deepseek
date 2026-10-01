import Mathlib

set_option linter.unusedVariables false

namespace Work.BzHard

/-- If `gcd d e` and `(e / gcd d e) * (d / gcd d e)` are not coprime, then some prime
divides both `gcd d e` and one of `d / gcd d e`, `e / gcd d e`; hence that prime's square
divides `d` or `e`, so the corresponding Möbius value vanishes. -/
theorem moebius_param_vanish {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e)
    (h : ¬ Nat.Coprime (Nat.gcd d e) ((e / Nat.gcd d e) * (d / Nat.gcd d e))) :
    (ArithmeticFunction.moebius d : ℝ) = 0 ∨ (ArithmeticFunction.moebius e : ℝ) = 0 := by
  have hg_dvd_d : Nat.gcd d e ∣ d := Nat.gcd_dvd_left d e
  have hg_dvd_e : Nat.gcd d e ∣ e := Nat.gcd_dvd_right d e
  have hd_eq : Nat.gcd d e * (d / Nat.gcd d e) = d := Nat.mul_div_cancel' hg_dvd_d
  have he_eq : Nat.gcd d e * (e / Nat.gcd d e) = e := Nat.mul_div_cancel' hg_dvd_e
  have hgcd : Nat.gcd (Nat.gcd d e) ((e / Nat.gcd d e) * (d / Nat.gcd d e)) ≠ 1 := by
    intro hc
    exact h (Nat.coprime_iff_gcd_eq_one.mpr hc)
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hgcd
  have hp_g : p ∣ Nat.gcd d e := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have hp_prod : p ∣ (e / Nat.gcd d e) * (d / Nat.gcd d e) :=
    dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  rcases (Nat.Prime.dvd_mul hpp).mp hp_prod with hp_eg | hp_dg
  · right
    have hpp_dvd_e : p * p ∣ e := by
      have := mul_dvd_mul hp_g hp_eg
      rwa [he_eq] at this
    have hnsq : ¬ Squarefree e := by
      intro hsq
      exact (Nat.squarefree_iff_prime_squarefree.mp hsq) p hpp hpp_dvd_e
    have h0 : ArithmeticFunction.moebius e = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
    rw [h0]; norm_num
  · left
    have hpp_dvd_d : p * p ∣ d := by
      have := mul_dvd_mul hp_g hp_dg
      rwa [hd_eq] at this
    have hnsq : ¬ Squarefree d := by
      intro hsq
      exact (Nat.squarefree_iff_prime_squarefree.mp hsq) p hpp hpp_dvd_d
    have h0 : ArithmeticFunction.moebius d = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
    rw [h0]; norm_num

end Work.BzHard
