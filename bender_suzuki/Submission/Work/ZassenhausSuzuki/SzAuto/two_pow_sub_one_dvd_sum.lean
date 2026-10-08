import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.SzAuto.two_pow_sub_one_dvd_sum`

For `0 < s < n`, the number `2 ^ n - 1` divides
`∑_{i < (n / gcd(n,s)) * (2 ^ gcd(n,s) - 1)} 2 ^ (s * i)`.

Writing `d = gcd(n,s)`, `q = n / d`, `t = s / d` (so `n = d * q`, `s = d * t`, and
`q` and `t` are coprime by construction) and `x = 2 ^ d`, the claim becomes

  `(x ^ q - 1) ∣ ∑_{i < q * (x - 1)} x ^ (t * i)`.

This is `geom_dvd`.  Its proof works modulo `x ^ q - 1`, where the class `a = x` satisfies
`a ^ q = 1` and `x ^ q ≡ 1`.  Splitting `range (q * (x - 1))` into `x - 1` consecutive blocks of
length `q` and using that `a ^ q = 1`, every block reduces to `∑_{k < q} a ^ (t * k)`.  Since
`q` and `t` are coprime, `k ↦ t * k % q` permutes `range q`, so `∑_{k < q} a ^ (t*k) = ∑_{r<q} a^r`;
finally `(x - 1) * ∑_{r < q} x ^ r = x ^ q - 1 ≡ 0`.
-/

namespace Work.ZassenhausSuzuki.SzAuto

/-- Block decomposition of a sum over `range (m * n)`: group the indices into `m` consecutive
blocks of length `n`.  The index `j * n + k` for `j < m`, `k < n` runs over `range (m * n)`
exactly once. -/
theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m n : ℕ) :
    ∑ i ∈ Finset.range (m * n), f i
      = ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range n, f (j * n + k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- For `0 < q` and `q.Coprime t`, multiplication by `t` permutes the residues modulo `q`; hence
summing a function over the indices `t * k % q` equals summing it over `range q`. -/
theorem sum_range_mul_mod_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) {q t : ℕ}
    (hq : 0 < q) (h : q.Coprime t) :
    ∑ k ∈ Finset.range q, f (t * k % q) = ∑ r ∈ Finset.range q, f r := by
  -- `k ↦ t * k % q` is injective on `range q`.
  have key : ∀ a b, a < q → b < q → t * a % q = t * b % q → a ≤ b → a = b := by
    intro a b _ hb hab hle
    have hmod : t * a ≡ t * b [MOD q] := hab
    have hdvd : q ∣ t * b - t * a :=
      (Nat.modEq_iff_dvd' (Nat.mul_le_mul_left t hle)).mp hmod
    have hdvd2 : q ∣ t * (b - a) := by rwa [← Nat.mul_sub_left_distrib] at hdvd
    have hdvd3 : q ∣ b - a := Nat.Coprime.dvd_of_dvd_mul_left h hdvd2
    have hlt : b - a < q := lt_of_le_of_lt (Nat.sub_le b a) hb
    have h0 : (b - a) % q = 0 := Nat.mod_eq_zero_of_dvd hdvd3
    rw [Nat.mod_eq_of_lt hlt] at h0
    exact le_antisymm hle (Nat.le_of_sub_eq_zero h0)
  have hinj : Set.InjOn (fun k => t * k % q) (↑(Finset.range q)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    rcases le_total a b with hle | hle
    · exact key a b ha hb hab hle
    · exact (key b a hb ha hab.symm hle).symm
  -- hence its image is all of `range q`
  have himg : (Finset.range q).image (fun k => t * k % q) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨k, _, rfl⟩ := hx
      exact Nat.mod_lt _ hq
    · rw [Finset.card_image_of_injOn hinj]
  rw [← Finset.sum_image hinj, himg]

/-- Reduction of the exponent modulo `q`, taken modulo `x ^ q - 1`. -/
theorem pow_modEq_mod (x q a : ℕ) (hx : 1 ≤ x) :
    x ^ a ≡ x ^ (a % q) [MOD (x ^ q - 1)] := by
  have hxq : x ^ q ≡ 1 [MOD x ^ q - 1] :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow q x (by omega))).mpr (dvd_refl _) |>.symm
  have hpow : (x ^ q) ^ (a / q) ≡ 1 [MOD (x ^ q - 1)] := by
    simpa using hxq.pow (a / q)
  have heq : x ^ a = x ^ (a % q) * (x ^ q) ^ (a / q) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    exact (Nat.mod_add_div a q).symm
  rw [heq]
  simpa using Nat.ModEq.mul (Nat.ModEq.refl (x ^ (a % q))) hpow

/-- Core combinatorial divisibility: for `0 < q`, `q.Coprime t` and `1 ≤ x`, the number
`x ^ q - 1` divides `∑_{i < q * (x - 1)} x ^ (t * i)`. -/
theorem geom_dvd (x q t : ℕ) (hq : 0 < q) (h : q.Coprime t) (hx : 1 ≤ x) :
    (x ^ q - 1) ∣ ∑ i ∈ Finset.range (q * (x - 1)), x ^ (t * i) := by
  rw [← Nat.modEq_zero_iff_dvd]
  have hxq : x ^ q ≡ 1 [MOD x ^ q - 1] :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow q x (by omega))).mpr (dvd_refl _) |>.symm
  -- split `range (q * (x - 1))` into `x - 1` blocks of length `q`
  have hblock : ∑ i ∈ Finset.range (q * (x - 1)), x ^ (t * i)
      = ∑ j ∈ Finset.range (x - 1), ∑ k ∈ Finset.range q, x ^ (t * (j * q + k)) := by
    rw [mul_comm q (x - 1)]
    exact sum_range_mul_eq (fun i => x ^ (t * i)) (x - 1) q
  -- inside a block, `x ^ (t * (j*q + k)) ≡ x ^ (t * k)` since `x ^ q ≡ 1`
  have hstep1 : (∑ j ∈ Finset.range (x - 1), ∑ k ∈ Finset.range q, x ^ (t * (j * q + k)))
      ≡ (∑ j ∈ Finset.range (x - 1), ∑ k ∈ Finset.range q, x ^ (t * k)) [MOD x ^ q - 1] := by
    apply Nat.ModEq.sum
    intro j _
    apply Nat.ModEq.sum
    intro k _
    have hsplit : x ^ (t * (j * q + k)) = x ^ (t * j * q) * x ^ (t * k) := by
      rw [show t * (j * q + k) = t * j * q + t * k by ring, pow_add]
    rw [hsplit]
    have hxj : x ^ (t * j * q) ≡ 1 [MOD x ^ q - 1] := by
      have hpow : x ^ (t * j * q) = (x ^ q) ^ (t * j) := by
        rw [show t * j * q = q * (t * j) by ring, pow_mul]
      rw [hpow]
      simpa using hxq.pow (t * j)
    simpa using Nat.ModEq.mul hxj (Nat.ModEq.refl (x ^ (t * k)))
  have hstep2 : (∑ j ∈ Finset.range (x - 1), ∑ k ∈ Finset.range q, x ^ (t * k))
      = (x - 1) * ∑ k ∈ Finset.range q, x ^ (t * k) := by
    rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_range]
  -- permutation of the residues mod `q`
  have hstep3 : (x - 1) * (∑ k ∈ Finset.range q, x ^ (t * k))
      ≡ (x - 1) * (∑ r ∈ Finset.range q, x ^ r) [MOD x ^ q - 1] := by
    apply Nat.ModEq.mul (Nat.ModEq.refl (x - 1))
    calc ∑ k ∈ Finset.range q, x ^ (t * k)
        ≡ ∑ k ∈ Finset.range q, x ^ (t * k % q) [MOD x ^ q - 1] := by
          apply Nat.ModEq.sum; intro k _
          exact pow_modEq_mod x q (t * k) hx
      _ = ∑ r ∈ Finset.range q, x ^ r := sum_range_mul_mod_eq (fun i => x ^ i) hq h
  have hstep4 : (x - 1) * (∑ r ∈ Finset.range q, x ^ r) = x ^ q - 1 := by
    have h1 := geom_sum_mul_add (x - 1) q
    rw [Nat.sub_add_cancel hx] at h1
    have h2 : (∑ i ∈ Finset.range q, x ^ i) * (x - 1) = x ^ q - 1 := by omega
    rw [← h2, mul_comm]
  rw [hblock]
  refine hstep1.trans ?_
  rw [hstep2]
  refine hstep3.trans ?_
  rw [hstep4]
  exact Nat.modEq_zero_iff_dvd.mpr (dvd_refl (x ^ q - 1))

theorem two_pow_sub_one_dvd_sum (n s : ℕ) (hs : 0 < s) (hsn : s < n) :
    (2 ^ n - 1) ∣ Finset.sum (Finset.range ((n / n.gcd s) * (2 ^ (n.gcd s) - 1)))
      (fun i => 2 ^ (s * i)) := by
  set d := n.gcd s with hd
  set q := n / d with hq
  set t := s / d with ht
  have hdvdn : d ∣ n := by rw [hd]; exact Nat.gcd_dvd_left n s
  have hdvds : d ∣ s := by rw [hd]; exact Nat.gcd_dvd_right n s
  have hnd : d * q = n := by rw [hq]; exact Nat.mul_div_cancel' hdvdn
  have hst : d * t = s := by rw [ht]; exact Nat.mul_div_cancel' hdvds
  have hdpos : 0 < d := by rw [hd]; exact Nat.gcd_pos_of_pos_right n hs
  have hcop : q.Coprime t := by
    rw [hq, ht, hd]; exact Nat.coprime_div_gcd_div_gcd hdpos
  have hqpos : 0 < q := by
    rw [hq]; exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvdn) hdpos
  have hmain : ((2 ^ d) ^ q - 1) ∣ ∑ i ∈ Finset.range (q * (2 ^ d - 1)), (2 ^ d) ^ (t * i) :=
    geom_dvd (2 ^ d) q t hqpos hcop (Nat.one_le_pow d 2 (by norm_num))
  have hD : (2 ^ d) ^ q - 1 = 2 ^ n - 1 := by rw [← pow_mul, hnd]
  have hterm : ∀ i, (2 ^ d) ^ (t * i) = 2 ^ (s * i) := by
    intro i; rw [← pow_mul, ← mul_assoc, hst]
  have hsum : ∑ i ∈ Finset.range (q * (2 ^ d - 1)), (2 ^ d) ^ (t * i)
      = Finset.sum (Finset.range (q * (2 ^ d - 1))) (fun i => 2 ^ (s * i)) :=
    Finset.sum_congr rfl (fun i _ => hterm i)
  rw [hD, hsum] at hmain
  exact hmain

end Work.ZassenhausSuzuki.SzAuto
