import Mathlib
import Submission.Work.ThmG.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSIntegrate.Order

open Work.ThmG

/-- If `d` acts fixed-point-freely (fpf) on the odd part `Q₁ = OddPart Q` of `Q`, and `d`
centralises some non-trivial element `q ∈ Q`, then `Q` contains a `d`-centralised involution.

The point is that `q` cannot have odd order: an odd-order element of `Q` lies in `oddPart Q`,
where `d` is fpf.  Hence `q` has even order `n`, and `u = q ^ (n / 2)` is an involution of `Q`
commuting with `d` (conjugation is a homomorphism). -/
theorem exists_involution_of_centralizes_oddPart {G : Type*} [Group G] [Finite G]
    {Q : Subgroup G} {d q : G}
    (hfpf : ∀ x ∈ Work.ThmG.oddPart Q, d * x * d⁻¹ = x → x = 1)
    (hq : q ∈ Q) (hq1 : q ≠ 1) (hc : d * q * d⁻¹ = q) :
    ∃ u ∈ Q, orderOf u = 2 ∧ d * u * d⁻¹ = u := by
  -- `q` does not have odd order, else it would lie in `oddPart Q` where `d` is fpf.
  have hnotodd : ¬ Odd (orderOf q) := fun ho =>
    hq1 (hfpf q (Work.ThmG.mem_oddPart_of_odd Q hq ho) hc)
  have heven : Even (orderOf q) := Nat.not_odd_iff_even.mp hnotodd
  -- order of `q` is a positive natural number since `G` is finite
  have hpos : 0 < orderOf q := (isOfFinOrder_of_finite q).orderOf_pos
  have h2n : 2 * (orderOf q / 2) = orderOf q := Nat.two_mul_div_two_of_even heven
  have hdivne : orderOf q / 2 ≠ 0 := fun hh => by
    rw [hh, mul_zero] at h2n
    omega
  refine ⟨q ^ (orderOf q / 2), Q.pow_mem hq _, ?_, ?_⟩
  · -- the constructed element has order exactly `2`
    refine orderOf_eq_prime ?_ ?_
    · rw [← pow_mul, Nat.div_two_mul_two_of_even heven, pow_orderOf_eq_one]
    · -- `q ^ (n / 2) ≠ 1` since its `n`-th power is `1` but `n / 2 < n`
      intro h
      have hdvd : orderOf q ∣ orderOf q / 2 := orderOf_dvd_iff_pow_eq_one.mpr h
      have hle : orderOf q ≤ orderOf q / 2 := Nat.le_of_dvd (Nat.pos_of_ne_zero hdivne) hdvd
      have hlt : orderOf q / 2 < orderOf q := Nat.div_lt_self hpos (by norm_num)
      omega
  · -- and it is centralised by `d`
    rw [← conj_pow, hc]

end Work.BSIntegrate.Order
