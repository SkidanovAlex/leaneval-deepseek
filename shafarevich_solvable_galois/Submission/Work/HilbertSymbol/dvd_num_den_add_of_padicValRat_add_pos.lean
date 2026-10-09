import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- Auxiliary: if `q + r` has positive `p`-adic valuation, then `p` divides the "naive numerator"
`q.num * r.den + q.den * r.num` of the sum (written as an integer). -/
private theorem dvd_add_num_den_of_padicValRat_add_pos {p : ℕ} [Fact p.Prime] {q r : ℚ}
    (h : 0 < padicValRat p (q + r)) :
    (p : ℤ) ∣ q.num * (r.den : ℤ) + r.num * (q.den : ℤ) := by
  have hsum : q + r = (((q.num * (r.den : ℤ) + (q.den : ℤ) * r.num : ℤ)) : ℚ) /
      ((((q.den : ℤ) * (r.den : ℤ)) : ℤ) : ℚ) := by
    rw [Rat.add_num_den, Rat.divInt_eq_div]
  have hsum' : q + r = Rat.divInt (q.num * (r.den : ℤ) + (q.den : ℤ) * r.num)
      ((q.den : ℤ) * (r.den : ℤ)) := Rat.add_num_den q r
  have hsum0 : q + r ≠ 0 := by
    intro h0
    rw [h0, padicValRat.zero] at h
    exact lt_irrefl 0 h
  have hN : q.num * (r.den : ℤ) + (q.den : ℤ) * r.num ≠ 0 :=
    Rat.mk_num_ne_zero_of_ne_zero hsum0 hsum'
  have hD : ((q.den : ℤ) * (r.den : ℤ)) ≠ 0 := by
    have h1 : (q.den : ℤ) ≠ 0 := by exact_mod_cast Rat.den_nz q
    have h2 : (r.den : ℤ) ≠ 0 := by exact_mod_cast Rat.den_nz r
    exact mul_ne_zero h1 h2
  have hDq : ((((q.den : ℤ) * (r.den : ℤ) : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast hD
  have hNq : (((q.num * (r.den : ℤ) + (q.den : ℤ) * r.num : ℤ)) : ℚ) ≠ 0 := by
    exact_mod_cast hN
  have hval : padicValRat p (q + r) =
      (padicValInt p (q.num * (r.den : ℤ) + (q.den : ℤ) * r.num) : ℤ) -
      (padicValInt p ((q.den : ℤ) * (r.den : ℤ)) : ℤ) := by
    rw [hsum, padicValRat.div hNq hDq, padicValRat.of_int, padicValRat.of_int]
  have hpos : 0 < (padicValInt p (q.num * (r.den : ℤ) + (q.den : ℤ) * r.num) : ℤ) -
      (padicValInt p ((q.den : ℤ) * (r.den : ℤ)) : ℤ) := by
    rw [← hval]; exact h
  have hnonneg : (0 : ℤ) ≤ (padicValInt p ((q.den : ℤ) * (r.den : ℤ)) : ℤ) := by
    exact_mod_cast Nat.zero_le _
  have hposN : (0 : ℤ) <
      (padicValInt p (q.num * (r.den : ℤ) + (q.den : ℤ) * r.num) : ℤ) := by
    linarith
  have hne : padicValInt p (q.num * (r.den : ℤ) + (q.den : ℤ) * r.num) ≠ 0 := by
    intro h0
    rw [h0] at hposN
    exact lt_irrefl 0 hposN
  have hdvd : (p : ℤ) ∣ q.num * (r.den : ℤ) + (q.den : ℤ) * r.num := by
    by_contra hnd
    exact hne (padicValInt.eq_zero_iff.mpr (Or.inr (Or.inr hnd)))
  convert hdvd using 1
  ring

theorem dvd_num_den_add_of_padicValRat_add_pos {p : ℕ} [Fact p.Prime] {c d : ℚˣ}
    (h : 0 < padicValRat p ((c : ℚ) + (d : ℚ))) :
    (p : ℤ) ∣ (c : ℚ).num * ((d : ℚ).den : ℤ) + (d : ℚ).num * ((c : ℚ).den : ℤ) :=
  dvd_add_num_den_of_padicValRat_add_pos h

end Work.HilbertSymbol
