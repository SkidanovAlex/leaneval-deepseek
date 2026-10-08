import Mathlib
import Submission.Work.BSLit.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSLit.ArithmeticNineTwoSeven` — Huppert–Blackburn IX (2-7)

`f ^ a = 2 ^ b + 1` with `f` odd and `2 ≤ f` forces `a = 1` or `f ^ a = 9`.
-/

set_option autoImplicit false

namespace Work.BSLit

/-- An odd divisor of a power of two equals `1`. -/
lemma odd_dvd_two_pow {m b : ℕ} (h : m ∣ 2 ^ b) (hm : Odd m) : m = 1 := by
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  rcases k with _ | k
  · simp
  · exact absurd ⟨2 ^ k, by rw [pow_succ]; ring⟩ (Nat.not_even_iff_odd.mpr hm)

/-- **Huppert–Blackburn IX (2-7)** (`Work.ThmF.ArithmeticNineTwoSeven`): if `f ^ a = 2 ^ b + 1` with `f` odd and `2 ≤ f`, then `a = 1` or `f ^ a = 9`. This is the elementary arithmetic input of Peterfalvi II Ch. V §3, steps (6) and (8). Route: for `a ≥ 2`, `f ^ a - 1 = 2 ^ b`; if `a = 2m` is even then `(f^m - 1)(f^m + 1) = 2 ^ b` are powers of `2` differing by `2`, hence `2` and `4`, so `f^m = 3` and `a = 2`; if `a` is odd and `≥ 3` then `(f - 1)(f^(a-1) + ⋯ + 1) = 2 ^ b` with the second factor odd and `> 1`. -/
theorem ArithmeticNineTwoSeven : Work.ThmF.ArithmeticNineTwoSeven := by
  intro f a b hfodd hf2 hapos heq
  by_cases ha1 : a = 1
  · exact Or.inl ha1
  · right
    have ha2 : 2 ≤ a := by omega
    have hf3 : 3 ≤ f := by rcases hfodd with ⟨k, hk⟩; omega
    have hf1 : 1 ≤ f := by omega
    have hsub : f ^ a - 1 = 2 ^ b := by rw [heq, Nat.add_sub_cancel]
    have hgeom : (∑ i ∈ Finset.range a, f ^ i) * (f - 1) = 2 ^ b :=
      (geom_sum_mul_of_one_le (x := f) hf1 a).trans hsub
    by_cases haodd : Odd a
    · -- `a` odd and `≥ 2`: the geometric factor is an odd divisor `> 1` of `2 ^ b`.
      exfalso
      have hSodd : Odd (∑ i ∈ Finset.range a, f ^ i) := by
        rw [Finset.odd_sum_iff_odd_card_odd,
          Finset.filter_true_of_mem (fun x _ => hfodd.pow), Finset.card_range]
        exact haodd
      have hSdvd : (∑ i ∈ Finset.range a, f ^ i) ∣ 2 ^ b := ⟨f - 1, hgeom.symm⟩
      have hSeq : (∑ i ∈ Finset.range a, f ^ i) = 1 := odd_dvd_two_pow hSdvd hSodd
      have hmem : a - 1 ∈ Finset.range a := Finset.mem_range.mpr (by omega)
      have hle : f ^ (a - 1) ≤ ∑ i ∈ Finset.range a, f ^ i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le _) hmem
      have hbig : 3 ≤ f ^ (a - 1) := by
        calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
          _ ≤ 3 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ f ^ (a - 1) := Nat.pow_le_pow_left hf3 (a - 1)
      omega
    · -- `a` even: `a = 2 * m`, and `(f^m - 1) (f^m + 1) = 2 ^ b`, so both are powers of two
      -- differing by `2`, hence `2` and `4`.
      have haeven : Even a := Nat.not_odd_iff_even.mp haodd
      obtain ⟨m, rfl⟩ := haeven
      have hm1 : 1 ≤ m := by omega
      have hfm3 : 3 ≤ f ^ m := by
        calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
          _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
          _ ≤ f ^ m := Nat.pow_le_pow_left hf3 m
      have hfmeq : (f ^ m) ^ 2 = 2 ^ b + 1 := by
        rw [pow_two, ← pow_add]; exact heq
      have hprod : (f ^ m - 1) * (f ^ m + 1) = 2 ^ b := by
        have h1 : (f ^ m - 1) * (f ^ m + 1) = (f ^ m) ^ 2 - 1 := by
          rw [mul_comm, ← Nat.sq_sub_sq (f ^ m) 1]
        rw [h1, hfmeq, Nat.add_sub_cancel]
      obtain ⟨c, hc, hceq⟩ :=
        (Nat.dvd_prime_pow Nat.prime_two).1 (⟨f ^ m + 1, hprod.symm⟩ : (f ^ m - 1) ∣ 2 ^ b)
      obtain ⟨d, hd, hdeq⟩ :=
        (Nat.dvd_prime_pow Nat.prime_two).1
          (⟨f ^ m - 1, by rw [mul_comm]; exact hprod.symm⟩ : (f ^ m + 1) ∣ 2 ^ b)
      have hge2 : 2 ≤ 2 ^ c := by rw [← hceq]; omega
      have hlt : 2 ^ c < 2 ^ d := by rw [← hceq, ← hdeq]; omega
      have hcd : c < d := (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp hlt
      have hcle : c ≤ d := le_of_lt hcd
      have hdiff : 2 ^ d - 2 ^ c = 2 := by rw [← hdeq, ← hceq]; omega
      have hp : 2 ^ c ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hcle
      have h1 : 2 ^ d = 2 ^ c * 2 ^ (d - c) := by
        rw [← pow_add, Nat.add_sub_of_le hcle]
      have h2 : 2 ^ d = 2 ^ c + 2 := by omega
      have hge : 2 ≤ 2 ^ (d - c) := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (d - c) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2c : 2 ^ c ≤ 2 := by
        have h3 : 2 ^ c + 2 ^ c ≤ 2 ^ c + 2 := by
          calc 2 ^ c + 2 ^ c = 2 ^ c * 2 := by ring
            _ ≤ 2 ^ c * 2 ^ (d - c) := Nat.mul_le_mul_left _ hge
            _ = 2 ^ d := h1.symm
            _ = 2 ^ c + 2 := h2
        exact (add_le_add_iff_left (2 ^ c)).mp h3
      have h2c_eq : 2 ^ c = 2 := le_antisymm h2c hge2
      have hfm1 : f ^ m - 1 = 2 := by rw [hceq, h2c_eq]
      have hfm_eq3 : f ^ m = 3 := by omega
      rw [pow_add, hfm_eq3]
      norm_num

end Work.BSLit
