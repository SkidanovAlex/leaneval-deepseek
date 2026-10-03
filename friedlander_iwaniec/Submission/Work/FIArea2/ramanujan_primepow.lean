import Mathlib
import Submission.Work.FIArea2.ramanujan_setup

namespace Work.FIArea2

open scoped BigOperators
open Finset

/-!
# The Ramanujan sum bound at a prime power

`Work.FIArea2.ram` is the classical Ramanujan sum
`R(h; b) = ∑_{1 ≤ η ≤ b, (η,b)=1} e(η h / b)`, and the target here is the classical bound
`‖R(h;p^k)‖ ≤ (p^k, h)` for `p` prime — the value of the Ramanujan sum at a **prime power**.

The route used is the elementary "all minus non-coprime" splitting of the sum defining `ram`,
together with the incomplete-geometric-sum evaluation `T_eq` from `ramanujan_setup`:

* the whole sum over `1 ≤ η ≤ p^(k+1)` is `T (p^(k+1)) h = p^(k+1)·[p^(k+1) ∣ h]`;
* the terms with `(η, p^(k+1)) > 1` are exactly the multiples of `p`, and reindexed by `η = p j`
  they sum to `T (p^k) h = p^k·[p^k ∣ h]`.

Hence `R(h; p^(k+1)) = p^(k+1)[p^(k+1) ∣ h] - p^k[p^k ∣ h]`, from which the stated bound is a
case check on the valuation of `h` at `p`, using `Nat.dvd_prime_pow` to identify
`(p^(k+1), h.natAbs)` as a power of `p`.
-/

/-- `p^(k+1)/p = p^k`. -/
private lemma ram_pp_pow_div (p k : ℕ) (hp : Nat.Prime p) : p ^ (k + 1) / p = p ^ k := by
  rw [pow_succ]
  exact Nat.mul_div_cancel _ hp.pos

/-- Divisibility of `b.natAbs` by `m : ℕ` is divisibility of `b : ℤ` by `m`. -/
private lemma ram_pp_int_nat_dvd (m : ℕ) (b : ℤ) : m ∣ b.natAbs ↔ (m : ℤ) ∣ b := by
  constructor
  · intro hh
    have : ((m : ℤ)).natAbs ∣ b.natAbs := by simpa using hh
    exact (Int.natAbs_dvd_natAbs (a := (m : ℤ)) (b := b)).mp this
  · intro hh
    have : ((m : ℤ)).natAbs ∣ b.natAbs := (Int.natAbs_dvd_natAbs (a := (m : ℤ)) (b := b)).mpr hh
    simpa using this

/-- **Splitting the Ramanujan sum at a prime power.** The terms coprime to `p^(k+1)` are `ram`,
the others are the multiples of `p` and reindex to `T (p^k) h`, so
`ram (p^(k+1)) h = T (p^(k+1)) h - T (p^k) h`. -/
private lemma ram_pp_decomp (p k : ℕ) (hp : Nat.Prime p) (h : ℤ) :
    ram (p ^ (k + 1)) h = T (p ^ (k + 1)) h - T (p ^ k) h := by
  have hsplit := sum_filter_add_sum_filter_not (s := Icc 1 (p^(k+1)))
      (p := fun η => Nat.Coprime η (p^(k+1)))
      (f := fun η => E (((h * (η:ℤ) : ℤ) : ℝ) / ((p^(k+1) : ℕ) : ℝ)))
  have hfull : (∑ η ∈ Icc 1 (p^(k+1)),
      E (((h * (η:ℤ) : ℤ) : ℝ) / ((p^(k+1) : ℕ) : ℝ))) = T (p^(k+1)) h := by
    unfold T; rfl
  have hnotcop : (∑ η ∈ (Icc 1 (p^(k+1))).filter (fun η => ¬ Nat.Coprime η (p^(k+1))),
        E (((h * (η:ℤ) : ℤ) : ℝ) / ((p^(k+1) : ℕ) : ℝ))) = T (p^k) h := by
    rw [show (Icc 1 (p^(k+1))).filter (fun η => ¬ Nat.Coprime η (p^(k+1)))
        = (Icc 1 (p^(k+1))).filter (fun η => p ∣ η) from by
      apply filter_congr; intro η _
      rw [Nat.coprime_pow_right_iff (n := k+1) (Nat.succ_pos k), Nat.coprime_comm,
          hp.coprime_iff_not_dvd]
      tauto]
    rw [sum_Icc_filter_dvd (p^(k+1)) p ⟨p^k, by rw [pow_succ']⟩
          (fun η => E (((h * (η:ℤ) : ℤ) : ℝ) / ((p^(k+1) : ℕ) : ℝ)))]
    rw [ram_pp_pow_div p k hp]
    unfold T
    apply sum_congr rfl
    intro j hj
    congr 1
    have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    push_cast
    rw [pow_succ]
    field_simp
  calc ram (p^(k+1)) h
      = ∑ η ∈ (Icc 1 (p^(k+1))).filter (fun η => Nat.Coprime η (p^(k+1))),
          E (((h * (η:ℤ) : ℤ) : ℝ) / ((p^(k+1) : ℕ) : ℝ)) := rfl
    _ = (∑ η ∈ Icc 1 (p^(k+1)), E (((h * (η:ℤ) : ℤ) : ℝ) / ((p^(k+1) : ℕ) : ℝ)))
          - (∑ η ∈ (Icc 1 (p^(k+1))).filter (fun η => ¬ Nat.Coprime η (p^(k+1))),
              E (((h * (η:ℤ) : ℤ) : ℝ) / ((p^(k+1) : ℕ) : ℝ))) := by
          rw [← hsplit]; ring
    _ = T (p^(k+1)) h - T (p^k) h := by rw [hfull, hnotcop]

/-- If `p^(k+1) ∣ h` then `(p^(k+1), h) = p^(k+1)`. -/
private lemma ram_pp_gcd_top (p k : ℕ) (h : ℤ) (hA : ((p ^ (k + 1) : ℕ) : ℤ) ∣ h) :
    Nat.gcd (p ^ (k + 1)) h.natAbs = p ^ (k + 1) :=
  Nat.gcd_eq_left ((ram_pp_int_nat_dvd (p ^ (k + 1)) h).mpr hA)

/-- If `p^k ∣ h` but `p^(k+1) ∤ h` then `(p^(k+1), h) = p^k`: the gcd divides `p^(k+1)`, hence
is a power of `p`, is divisible by `p^k`, and is not `p^(k+1)`. -/
private lemma ram_pp_gcd_mid (p k : ℕ) (hp : Nat.Prime p) (h : ℤ)
    (hB : ((p ^ k : ℕ) : ℤ) ∣ h) (hA : ¬ ((p ^ (k + 1) : ℕ) : ℤ) ∣ h) :
    Nat.gcd (p ^ (k + 1)) h.natAbs = p ^ k := by
  have hB' : p^k ∣ h.natAbs := (ram_pp_int_nat_dvd (p^k) h).mpr hB
  have hA' : ¬ (p^(k+1) ∣ h.natAbs) := fun hh => hA ((ram_pp_int_nat_dvd (p^(k+1)) h).mp hh)
  have hdvd : p^k ∣ Nat.gcd (p^(k+1)) h.natAbs :=
    Nat.dvd_gcd (pow_dvd_pow p (Nat.le_succ k)) hB'
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left _ _)
  have hkj : k ≤ j := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (hj ▸ hdvd)
  have hjk : j = k := by
    have : j ≤ k := by
      rcases Nat.lt_or_ge j (k+1) with hlt | hge
      · omega
      · exfalso
        have hj' : j = k+1 := by omega
        have hh : Nat.gcd (p^(k+1)) h.natAbs ∣ h.natAbs := Nat.gcd_dvd_right _ _
        rw [hj, hj'] at hh
        exact hA' hh
    omega
  rw [hj, hjk]

theorem ramanujan_primepow (p k : ℕ) (hp : Nat.Prime p) (h : ℤ) :
    ‖ram (p ^ k) h‖ ≤ (Nat.gcd (p ^ k) h.natAbs : ℝ) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, pow_zero]
    have h1 : ram 1 h = 1 := by
      unfold ram
      rw [Finset.Icc_self]
      norm_num [E_int]
    rw [h1]
    simp
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hramval : ram (p^(k'+1)) h =
        (if ((p^(k'+1) : ℕ) : ℤ) ∣ h then ((p^(k'+1) : ℕ) : ℂ) else 0)
        - (if ((p^k' : ℕ) : ℤ) ∣ h then ((p^k' : ℕ) : ℂ) else 0) := by
      rw [ram_pp_decomp p k' hp h, T_eq (p^(k'+1)) (Nat.one_le_pow _ p hp.pos) h,
          T_eq (p^k') (Nat.one_le_pow _ p hp.pos) h]
    by_cases hA : ((p^(k'+1) : ℕ) : ℤ) ∣ h
    · have hAnat : p^(k'+1) ∣ h.natAbs := (ram_pp_int_nat_dvd (p^(k'+1)) h).mpr hA
      have hB : ((p^k' : ℕ) : ℤ) ∣ h :=
        (ram_pp_int_nat_dvd (p^k') h).mp (dvd_trans (pow_dvd_pow p (Nat.le_succ k')) hAnat)
      rw [hramval, if_pos hA, if_pos hB, ram_pp_gcd_top p k' h hA]
      rw [← Nat.cast_sub (Nat.pow_le_pow_right hp.pos (Nat.le_succ k')), Complex.norm_natCast]
      exact_mod_cast Nat.sub_le _ _
    · by_cases hB : ((p^k' : ℕ) : ℤ) ∣ h
      · rw [hramval, if_neg hA, if_pos hB, ram_pp_gcd_mid p k' hp h hB hA]
        simp
      · rw [hramval, if_neg hA, if_neg hB]
        simp

end Work.FIArea2
