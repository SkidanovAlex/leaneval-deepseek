import Mathlib

namespace Work.KMTPlan.A6.ConcAux

/-- The `p`-adic valuation of `∏_{j=0}^{d} j!` is at most `(d+1) · v_p(d!)`:
each factor `j!` divides `d!` for `j ≤ d`, so the whole product divides `(d!)^{d+1}`. -/
theorem padicValNat_prod_factorial_le (p d : ℕ) [Fact p.Prime] :
    padicValNat p (∏ j ∈ Finset.range (d + 1), j.factorial)
      ≤ (d + 1) * padicValNat p d.factorial := by
  have hdvd : (∏ j ∈ Finset.range (d + 1), j.factorial)
      ∣ (∏ j ∈ Finset.range (d + 1), d.factorial) :=
    Finset.prod_dvd_prod_of_dvd _ _
      (fun j hj => Nat.factorial_dvd_factorial (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  have hconst : (∏ j ∈ Finset.range (d + 1), d.factorial) = d.factorial ^ (d + 1) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [hconst] at hdvd
  have hne : d.factorial ^ (d + 1) ≠ 0 := pow_ne_zero _ d.factorial_ne_zero
  have hle : padicValNat p (∏ j ∈ Finset.range (d + 1), j.factorial)
      ≤ padicValNat p (d.factorial ^ (d + 1)) :=
    (padicValNat_dvd_iff_le hne).mp (pow_padicValNat_dvd.trans hdvd)
  rwa [padicValNat.pow] at hle

end Work.KMTPlan.A6.ConcAux
