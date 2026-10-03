import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_eq_gcd_mul
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_pow_eq_zero
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_eq_zero
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- For a prime `p`, `p ^ e ∣ x ^ n` holds exactly when `p ^ ⌈e / n⌉ ∣ x`, where
`⌈e / n⌉ = (e + n - 1) / n` is the ceiling of `e / n` in `ℕ`. -/
theorem pow_dvd_pow_iff (p e n x : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    p ^ e ∣ x ^ n ↔ p ^ ((e + n - 1) / n) ∣ x := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h
    by_cases hx : x = 0
    · rw [hx]; exact dvd_zero _
    · have hxn : x ^ n ≠ 0 := pow_ne_zero _ hx
      have h1 : e ≤ padicValNat p (x ^ n) := (padicValNat_dvd_iff_le hxn).mp h
      rw [padicValNat.pow] at h1
      have h2 : (e + n - 1) / n ≤ padicValNat p x :=
        (Nat.div_le_iff_le_mul_add_pred (b := n) (a := e + n - 1)
          (c := padicValNat p x) (by omega)).mpr (by omega)
      exact (padicValNat_dvd_iff_le hx).mpr h2
  · intro h
    obtain ⟨y, rfl⟩ := h
    have hle : e ≤ (e + n - 1) / n * n := by
      have h3 := (Nat.div_le_iff_le_mul_add_pred (b := n) (a := e + n - 1)
        (c := (e + n - 1) / n) (by omega)).mp le_rfl
      rw [Nat.mul_comm n ((e + n - 1) / n)] at h3
      omega
    rw [mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow p hle) _

/-- The square-part factor `∏_{q | p^e} q ^ (v_q(p^e) / 2)` of a prime power `p ^ e`
equals `p ^ (e / 2)`. -/
lemma primeFactors_pow_prod_factorization_div_two (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
    (Nat.primeFactors (p ^ e)).prod (fun q => q ^ ((p ^ e).factorization q / 2)) =
      p ^ (e / 2) := by
  have hfac : (p ^ e).factorization p = e := by
    rw [Nat.Prime.factorization_pow hp]
    exact Finsupp.single_eq_same
  rw [Nat.primeFactors_prime_pow (by omega : e ≠ 0) hp, Finset.prod_singleton, hfac]

/-- The number of elements of `ZMod (p ^ e)` whose fourth power vanishes is
`p ^ (e - ⌈e / 4⌉)`. -/
lemma ncard_pow_four_eq_zero_zmod_prime_pow (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
    ({y : ZMod (p ^ e) | y ^ 4 = 0}.ncard) = p ^ (e - (e + 3) / 4) := by
  haveI : NeZero (p ^ e) := ⟨(pow_pos hp.pos e).ne'⟩
  rw [ncard_zmod_eq_range (n := p ^ e) (ψ := fun y : ZMod (p ^ e) => y ^ 4 = 0)]
  have hfil : ((Finset.range (p ^ e)).filter (fun r : ℕ => ((r : ZMod (p ^ e)) ^ 4 = 0)))
      = ((Finset.range (p ^ e)).filter (fun r : ℕ => p ^ e ∣ r ^ 4)) := by
    apply Finset.filter_congr
    intro r _
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  rw [hfil]
  have hpow : ((Finset.range (p ^ e)).filter (fun r : ℕ => p ^ e ∣ r ^ 4))
      = ((Finset.range (p ^ e)).filter (fun r : ℕ => p ^ ((e + 3) / 4) ∣ r)) := by
    apply Finset.filter_congr
    intro r _
    have h := pow_dvd_pow_iff p e 4 r hp (by norm_num : 1 ≤ 4)
    rw [show (e + 4 - 1) / 4 = (e + 3) / 4 by omega] at h
    exact h
  rw [hpow, card_filter_range_dvd (p ^ e) (p ^ ((e + 3) / 4)) (pow_pos hp.pos _)
      (Nat.pow_dvd_pow p (by omega))]
  rw [Nat.pow_div (by omega : (e + 3) / 4 ≤ e) hp.pos]

end Commons.NumberTheory.FriedlanderIwaniec