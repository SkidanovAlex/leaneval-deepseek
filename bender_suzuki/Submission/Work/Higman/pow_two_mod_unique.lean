import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Higman

/-!
# The arithmetic core of Higman's Lemma 8

Higman (*Suzuki 2-groups*, Illinois J. Math. **7** (1963), p. 87) proves his Lemma 8 by quoting
his §4 Lemma 6: `L₃` is not `ξ`-isomorphic to `L₂`.  In the Suzuki situation the required
contradiction can be extracted explicitly (see `Submission/Work/Higman/higman_lemma8_plan.md`):
the monomials `x ^ (2 ^ p) * y ^ (2 ^ q)` occurring in an `ξ`-equivariant biadditive map
`L₁ × L₂ → L₃` (with `ξ` acting on `L₁` as `μ ·` and on `L₂`, `L₃` as `λ ·`, `λ = μ ^ t`,
`t = 2 ^ i + 2 ^ j`) must satisfy `2 ^ p + t * 2 ^ q ≡ t [MOD 2 ^ n - 1]`, and at most one pair
`(p,q)` does.  That is `pow_two_mod_unique` below, whose proof is elementary: it only uses that a
sum of two powers of two determines the multiset of exponents (`two_pow_sum_eq`).
-/

/-- The product of a power of two and an odd number determines both factors. -/
theorem mul_eq_mul_of_pow_two {a c u v : ℕ} (h : 2 ^ a * u = 2 ^ c * v) (hu : ¬ 2 ∣ u)
    (hv : ¬ 2 ∣ v) : a = c ∧ u = v := by
  rcases Nat.lt_trichotomy a c with hac | h' | hca
  · exfalso
    have hc : 2 ^ c = 2 ^ a * 2 ^ (c - a) := by
      rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hac)]
    rw [hc, mul_assoc] at h
    have h2 : u = 2 ^ (c - a) * v := Nat.mul_left_cancel (pow_pos (by norm_num : 0 < 2) a) h
    exact hu (by rw [h2]; exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) v)
  · subst h'
    exact ⟨rfl, Nat.mul_left_cancel (pow_pos (by norm_num : 0 < 2) a) h⟩
  · exfalso
    have hc : 2 ^ a = 2 ^ c * 2 ^ (a - c) := by
      rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hca)]
    rw [hc, mul_assoc] at h
    have h2 : 2 ^ (a - c) * u = v := Nat.mul_left_cancel (pow_pos (by norm_num : 0 < 2) c) h
    exact hv (by rw [← h2]; exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) u)

/-- `1 + 2 ^ k` is odd for `k ≥ 1`. -/
theorem not_two_dvd_one_add_two_pow {k : ℕ} (hk : 1 ≤ k) : ¬ 2 ∣ 1 + 2 ^ k := by
  intro hd
  have h2k : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have h1 : 2 ∣ 1 + 2 ^ k - 2 ^ k := Nat.dvd_sub hd h2k
  have h2 : 1 + 2 ^ k - 2 ^ k = 1 := by omega
  rw [h2] at h1
  omega

/-- **Sums of two powers of two.**  `2 ^ a + 2 ^ b = 2 ^ c + 2 ^ e` determines the multiset of
exponents. -/
theorem two_pow_sum_eq {a b c e : ℕ} (h : 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ e) :
    (a = c ∧ b = e) ∨ (a = e ∧ b = c) := by
  have hord : ∀ a b c e : ℕ, a ≤ b → c ≤ e → 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ e → a = c ∧ b = e := by
    intro a b c e hab hce h
    have hX : 2 ^ a + 2 ^ b = 2 ^ a * (1 + 2 ^ (b - a)) := by
      rw [mul_add, mul_one, ← pow_add, Nat.add_sub_cancel' hab]
    have hY : 2 ^ c + 2 ^ e = 2 ^ c * (1 + 2 ^ (e - c)) := by
      rw [mul_add, mul_one, ← pow_add, Nat.add_sub_cancel' hce]
    rw [hX, hY] at h
    rcases Nat.eq_or_lt_of_le hab with hba | hba
    · rcases Nat.eq_or_lt_of_le hce with hec | hec
      · subst hba
        subst hec
        have h' : 2 ^ (a + 1) * 1 = 2 ^ (c + 1) * 1 := by
          simpa [Nat.sub_self, pow_succ, mul_comm, mul_left_comm, mul_assoc] using h
        obtain ⟨h1, -⟩ := mul_eq_mul_of_pow_two h' (by norm_num) (by norm_num)
        exact ⟨by omega, by omega⟩
      · exfalso
        subst hba
        have hodd : ¬ 2 ∣ 1 + 2 ^ (e - c) := not_two_dvd_one_add_two_pow (by omega)
        have h' : 2 ^ (a + 1) * 1 = 2 ^ c * (1 + 2 ^ (e - c)) := by
          simpa [Nat.sub_self, pow_succ, mul_comm, mul_left_comm, mul_assoc] using h
        obtain ⟨-, h2⟩ := mul_eq_mul_of_pow_two h' (by norm_num) hodd
        have hpos : 0 < 2 ^ (e - c) := pow_pos (by norm_num) _
        omega
    · rcases Nat.eq_or_lt_of_le hce with hec | hec
      · exfalso
        subst hec
        have hodd : ¬ 2 ∣ 1 + 2 ^ (b - a) := not_two_dvd_one_add_two_pow (by omega)
        have h' : 2 ^ a * (1 + 2 ^ (b - a)) = 2 ^ (c + 1) * 1 := by
          simpa [Nat.sub_self, pow_succ, mul_comm, mul_left_comm, mul_assoc] using h
        obtain ⟨-, h2⟩ := mul_eq_mul_of_pow_two h' hodd (by norm_num)
        have hpos : 0 < 2 ^ (b - a) := pow_pos (by norm_num) _
        omega
      · have hodd1 : ¬ 2 ∣ 1 + 2 ^ (b - a) := not_two_dvd_one_add_two_pow (by omega)
        have hodd2 : ¬ 2 ∣ 1 + 2 ^ (e - c) := not_two_dvd_one_add_two_pow (by omega)
        obtain ⟨h1, h2⟩ := mul_eq_mul_of_pow_two h hodd1 hodd2
        have hpoweq : 2 ^ (b - a) = 2 ^ (e - c) := by omega
        have h3 : b - a = e - c := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpoweq
        exact ⟨h1, by omega⟩
  rcases le_total a b with hab | hab
  · rcases le_total c e with hce | hce
    · exact Or.inl (hord a b c e hab hce h)
    · obtain ⟨h1, h2⟩ := hord e c a b hce hab (by rw [add_comm (2 ^ e) (2 ^ c)]; exact h.symm)
      exact Or.inr ⟨h1.symm, h2.symm⟩
  · rcases le_total c e with hce | hce
    · obtain ⟨h1, h2⟩ := hord b a c e hab hce (by rw [add_comm]; exact h)
      exact Or.inr ⟨h2, h1⟩
    · obtain ⟨h1, h2⟩ := hord b a e c hab hce
        (by rw [add_comm (2 ^ b) (2 ^ a), add_comm (2 ^ e) (2 ^ c)]; exact h)
      exact Or.inl ⟨h2, h1⟩

/-- Two numbers in `[2, 2 ^ n]` congruent modulo `2 ^ n - 1` are equal. -/
theorem eq_of_modEq_of_le_two_pow {n A B : ℕ} (hA : 2 ≤ A) (hA' : A ≤ 2 ^ n)
    (hB : 2 ≤ B) (hB' : B ≤ 2 ^ n) (hAB : A ≡ B [MOD 2 ^ n - 1]) : A = B := by
  rcases le_total A B with hle | hle
  · have hdvd : 2 ^ n - 1 ∣ B - A := (Nat.modEq_iff_dvd' hle).mp hAB
    have hlt : B - A < 2 ^ n - 1 := by omega
    have hz := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  · have hdvd : 2 ^ n - 1 ∣ A - B := (Nat.modEq_iff_dvd' hle).mp hAB.symm
    have hlt : A - B < 2 ^ n - 1 := by omega
    have hz := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega

/-- Two sums of two powers of two with exponents `< n` that are congruent mod `2 ^ n - 1` have the
same multiset of exponents. -/
theorem two_pow_sum_modEq {n a b c e : ℕ} (ha : a < n) (hb : b < n) (hc : c < n)
    (he : e < n) (h : 2 ^ a + 2 ^ b ≡ 2 ^ c + 2 ^ e [MOD 2 ^ n - 1]) :
    (a = c ∧ b = e) ∨ (a = e ∧ b = c) := by
  have bound : ∀ x y : ℕ, x < n → y < n → 2 ^ x + 2 ^ y ≤ 2 ^ n := by
    intro x y hx hy
    have h1 : 2 ^ x ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ y ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ^ x + 2 ^ y ≤ 2 ^ (n - 1) + 2 ^ (n - 1) := Nat.add_le_add h1 h2
      _ = 2 ^ n := by
          rw [← two_mul, ← pow_succ']
          congr 1
          omega
  have two_le : ∀ x y : ℕ, 2 ≤ 2 ^ x + 2 ^ y := by
    intro x y
    have h1 : 1 ≤ 2 ^ x := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 1 ≤ 2 ^ y := Nat.one_le_pow _ _ (by norm_num)
    omega
  exact two_pow_sum_eq (eq_of_modEq_of_le_two_pow (two_le a b) (bound a b ha hb)
    (two_le c e) (bound c e hc he) h)

/-- **Arithmetic core of Higman 1963, Lemma 8.**  Let `2 ≤ n`, `N = 2 ^ n - 1` and
`t = 2 ^ i + 2 ^ j` with `i < j < n`.  Then `2 ^ p ≡ t * (2 ^ q - 1) [MOD N]` has at most one
solution `(p, q)` with `p, q < n`.

Proof.  Multiplying `2 ^ p ≡ t (2 ^ q - 1)` by `2 ^ q' - 1` and `2 ^ p' ≡ t (2 ^ q' - 1)` by
`2 ^ q - 1` and comparing gives `2 ^ p (2 ^ q' - 1) ≡ 2 ^ p' (2 ^ q - 1)`, i.e.
`2 ^ (p + q') + 2 ^ p' ≡ 2 ^ (p' + q) + 2 ^ p [MOD N]`.  Reducing exponents mod `n` and reading off
the multiset of exponents (`two_pow_sum_modEq`) gives either `p = p'` and `q = q'`, or
`q = q' = 0`; the latter is impossible since then `2 ^ p ≡ 0 [MOD N]` while `N = 2 ^ n - 1` is an
odd number `≥ 3`. -/
theorem pow_two_mod_unique (n i j p q p' q' : ℕ) (h2 : 2 ≤ n) (hij : i < j) (hjn : j < n)
    (hp : p < n) (hq : q < n) (hp' : p' < n) (hq' : q' < n)
    (h1 : 2 ^ p ≡ (2 ^ i + 2 ^ j) * (2 ^ q - 1) [MOD 2 ^ n - 1])
    (h2' : 2 ^ p' ≡ (2 ^ i + 2 ^ j) * (2 ^ q' - 1) [MOD 2 ^ n - 1]) :
    p = p' ∧ q = q' := by
  set N := 2 ^ n - 1 with hNdef
  set t := 2 ^ i + 2 ^ j with htdef
  have hn : 1 ≤ n := by omega
  have hN3 : 3 ≤ N := by
    have h : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    omega
  -- (1) reduction of exponents modulo `n`
  have hpowN : (2 : ℕ) ^ n % N = 1 := by
    have hN1 : 2 ^ n = N + 1 := by omega
    rw [hN1, Nat.add_comm, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  have hmod : ∀ x : ℕ, 2 ^ x ≡ 2 ^ (x % n) [MOD N] := by
    intro x
    have hx : (x / n) * n + x % n = x := by
      rw [mul_comm]; exact Nat.div_add_mod x n
    have hN1' : (2 : ℕ) ^ n ≡ 1 [MOD N] := by
      rw [Nat.ModEq, hpowN, Nat.mod_eq_of_lt (by omega : 1 < N)]
    calc 2 ^ x = 2 ^ ((x / n) * n + x % n) := by rw [hx]
      _ = (2 ^ n) ^ (x / n) * 2 ^ (x % n) := by rw [pow_add, mul_comm (x / n) n, ← pow_mul]
      _ ≡ 1 ^ (x / n) * 2 ^ (x % n) [MOD N] := Nat.ModEq.mul (hN1'.pow _) (Nat.ModEq.refl _)
      _ = 2 ^ (x % n) := by simp
  -- (2) multiply the two congruences and eliminate `t`
  have hmul1 : 2 ^ p * (2 ^ q' - 1) ≡ t * (2 ^ q - 1) * (2 ^ q' - 1) [MOD N] :=
    h1.mul (Nat.ModEq.refl _)
  have hmul2 : 2 ^ p' * (2 ^ q - 1) ≡ t * (2 ^ q' - 1) * (2 ^ q - 1) [MOD N] :=
    h2'.mul (Nat.ModEq.refl _)
  have hswap : t * (2 ^ q - 1) * (2 ^ q' - 1) = t * (2 ^ q' - 1) * (2 ^ q - 1) := by ring
  rw [hswap] at hmul1
  have hkey : 2 ^ p * (2 ^ q' - 1) ≡ 2 ^ p' * (2 ^ q - 1) [MOD N] := hmul1.trans hmul2.symm
  have e1 : 2 ^ p * (2 ^ q' - 1) = 2 ^ (p + q') - 2 ^ p := by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_add]
  have e2 : 2 ^ p' * (2 ^ q - 1) = 2 ^ (p' + q) - 2 ^ p' := by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_add]
  rw [e1, e2] at hkey
  have hkey2 : 2 ^ (p + q') - 2 ^ p + (2 ^ p + 2 ^ p') ≡
      2 ^ (p' + q) - 2 ^ p' + (2 ^ p + 2 ^ p') [MOD N] :=
    hkey.add (Nat.ModEq.refl _)
  have s1 : 2 ^ (p + q') - 2 ^ p + (2 ^ p + 2 ^ p') = 2 ^ (p + q') + 2 ^ p' := by
    have hle : 2 ^ p ≤ 2 ^ (p + q') := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have s2 : 2 ^ (p' + q) - 2 ^ p' + (2 ^ p + 2 ^ p') = 2 ^ (p' + q) + 2 ^ p := by
    have hle : 2 ^ p' ≤ 2 ^ (p' + q) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [s1, s2] at hkey2
  -- (3) reduce the exponents mod `n` and read off the multiset
  have hred : 2 ^ ((p + q') % n) + 2 ^ p' ≡ 2 ^ ((p' + q) % n) + 2 ^ p [MOD N] := by
    have a1 := (hmod (p + q')).add (Nat.ModEq.refl (2 ^ p'))
    have a2 := (hmod (p' + q)).add (Nat.ModEq.refl (2 ^ p))
    exact a1.symm.trans (hkey2.trans a2)
  rcases two_pow_sum_modEq (Nat.mod_lt _ (by omega)) hp' (Nat.mod_lt _ (by omega)) hp hred with
    ⟨ha1, hp'e⟩ | ⟨ha1, hp'e⟩
  · -- (p + q') % n = (p' + q) % n and p' = p
    subst hp'e
    refine ⟨rfl, ?_⟩
    have hs : (p' + q') % n = (p' + q) % n := ha1
    have hm : p' + q' ≡ p' + q [MOD n] := hs
    have hqq : q' ≡ q [MOD n] := Nat.ModEq.add_left_cancel (Nat.ModEq.refl p') hm
    exact (hqq.eq_of_lt_of_lt hq' hq).symm
  · -- (p + q') % n = p and p' = (p' + q) % n : this forces q = 0
    exfalso
    have hq0 : q = 0 := by
      have h1' : p' + q ≡ p' + 0 [MOD n] := by
        show (p' + q) % n = (p' + 0) % n
        rw [Nat.add_zero, ← hp'e]
        exact (Nat.mod_eq_of_lt hp').symm
      have hqq : q ≡ 0 [MOD n] := Nat.ModEq.add_left_cancel (Nat.ModEq.refl p') h1'
      exact hqq.eq_of_lt_of_lt hq (by omega)
    subst hq0
    -- now `2 ^ p ≡ t * 0 ≡ 0 [MOD N]`, which is impossible
    have hzero : 2 ^ p ≡ 0 [MOD N] := by
      have h := h1
      rw [pow_zero, Nat.sub_self, mul_zero] at h
      exact h
    have hdvd : N ∣ 2 ^ p := Nat.dvd_of_mod_eq_zero (by rw [hzero, Nat.zero_mod])
    have hodd : Odd N := by
      have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hn]
      have hpos : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
      exact ⟨2 ^ (n - 1) - 1, by rw [hNdef]; omega⟩
    have hcop : N.Coprime (2 ^ p) := (Nat.coprime_two_right.mpr hodd).pow_right p
    have hdvd1 : N ∣ 1 := hcop.dvd_of_dvd_mul_left (by simpa using hdvd)
    have hle1 : N ≤ 1 := Nat.le_of_dvd (by norm_num : 0 < 1) hdvd1
    omega

end Work.Higman
