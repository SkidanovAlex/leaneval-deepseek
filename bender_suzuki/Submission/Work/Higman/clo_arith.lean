import Mathlib
import Submission.Work.Higman.pow_two_mod_unique

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Arithmetic lemmas for the monomial analysis of Higman's Lemma 8

Two elementary consequences of `Work.Higman.pow_two_mod_unique` needed by the final step of
Higman's Lemma 8: "two distinct powers of two are never congruent to `1`" (this excludes the
Frobenius-conjugacy of the eigenvalue parameters) and the sign-variant of the uniqueness
statement (equivariance of the bracket pairing naturally produces
`2 ^ p + t * 2 ^ q ≡ t`, whereas `pow_two_mod_unique` is stated with the opposite sign).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

/-- `N = 2 ^ n - 1` is odd (`n ≥ 1`). -/
private theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  refine ⟨2 ^ (n - 1) - 1, ?_⟩
  have h1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  have h2 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
  rw [h1, Nat.mul_sub_left_distrib, mul_one]
  omega

/-- `2 ^ n ≡ 1` modulo `2 ^ n - 1` (`n ≥ 1`). -/
private theorem two_pow_modEq_one {n : ℕ} (hn : 1 ≤ n) : (2 : ℕ) ^ n ≡ 1 [MOD 2 ^ n - 1] := by
  have hkey : ((2 ^ n - 1) + 1) % (2 ^ n - 1) = 1 % (2 ^ n - 1) := by
    rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
  have hN1 : 2 ^ n = (2 ^ n - 1) + 1 := by
    have : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    omega
  rw [Nat.ModEq]
  nth_rw 1 [hN1]
  exact hkey

/-- `2 ^ a + 2 ^ b` with `a ≠ b`, both `< n`, is never congruent to `1` modulo `2 ^ n - 1`. -/
theorem two_pow_sum_mod_ne_one {n a b : ℕ} (h2 : 2 ≤ n) (ha : a < n) (hb : b < n)
    (hab : a ≠ b) : ¬ (2 ^ a + 2 ^ b ≡ 1 [MOD 2 ^ n - 1]) := by
  intro h
  set N := 2 ^ n - 1 with hN
  have hN3 : 3 ≤ N := by
    have h4 : 4 ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hmod : (2 ^ a + 2 ^ b) % N = 1 := by
    have h' : (2 ^ a + 2 ^ b) % N = 1 % N := h
    rw [h', Nat.mod_eq_of_lt (by omega)]
  have hpow : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
    rw [← two_mul, ← pow_succ']
    congr 1
    omega
  have hle : 2 ^ a + 2 ^ b ≤ 2 ^ n := by
    have h1 : 2 ^ a ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2' : 2 ^ b ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hge : 3 ≤ 2 ^ a + 2 ^ b := by
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · have hapos : 0 < a := by
        rcases Nat.eq_zero_or_pos a with ha0 | hpos
        · exact absurd (ha0.trans hb0.symm) hab
        · exact hpos
      have h1 : 2 ≤ 2 ^ a := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hapos
      have h2' : 1 ≤ 2 ^ b := Nat.one_le_pow _ _ (by norm_num)
      omega
    · have h1 : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by norm_num)
      have h2' : 2 ≤ 2 ^ b := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hbpos
      omega
  have h2n1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hN1 : N + 1 = 2 ^ n := by rw [hN, Nat.sub_add_cancel h2n1]
  have hcases : 2 ^ a + 2 ^ b = 1 ∨ 2 ^ a + 2 ^ b = 2 ^ n := by
    rcases lt_or_ge (2 ^ a + 2 ^ b) (N + 1) with hlt | hge'
    · have hleN : 2 ^ a + 2 ^ b ≤ N := Nat.lt_succ_iff.mp hlt
      rcases lt_or_eq_of_le hleN with hlt' | heq'
      · rw [Nat.mod_eq_of_lt hlt'] at hmod
        exact Or.inl hmod
      · have hzero : (2 ^ a + 2 ^ b) % N = 0 := by rw [heq', Nat.mod_self]
        exact absurd (hzero.symm.trans hmod) (by norm_num)
    · right
      rw [hN1] at hge'
      omega
  rcases hcases with h1 | h1
  · omega
  · have ha' : 2 ^ a ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb' : 2 ^ b ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hEqa : 2 ^ a = 2 ^ (n - 1) := by
      have hthis : 2 ^ a + 2 ^ b ≤ 2 ^ a + 2 ^ (n - 1) := add_le_add le_rfl hb'
      rw [h1, ← hpow] at hthis
      exact le_antisymm ha' (Nat.add_le_add_iff_right.mp hthis)
    have hEqb : 2 ^ b = 2 ^ (n - 1) := by
      have hthis : 2 ^ a + 2 ^ b ≤ 2 ^ (n - 1) + 2 ^ b := add_le_add ha' le_rfl
      rw [h1, ← hpow] at hthis
      exact le_antisymm hb' (Nat.add_le_add_iff_left.mp hthis)
    exact hab ((Nat.pow_right_injective (by norm_num) hEqa).trans
      (Nat.pow_right_injective (by norm_num) hEqb).symm)

/-- `2 ^ k ≡ 2 ^ (k % n)` modulo `2 ^ n - 1` (`n ≥ 1`). -/
private theorem pow_modEq_mod {n k : ℕ} (hn : 1 ≤ n) :
    2 ^ k ≡ 2 ^ (k % n) [MOD 2 ^ n - 1] := by
  have h2n : (2 : ℕ) ^ n ≡ 1 [MOD 2 ^ n - 1] := two_pow_modEq_one hn
  have hx : k = (k / n) * n + k % n := by
    rw [mul_comm]
    exact (Nat.div_add_mod k n).symm
  calc 2 ^ k = 2 ^ ((k / n) * n + k % n) := congrArg (fun t => 2 ^ t) hx
    _ = (2 ^ n) ^ (k / n) * 2 ^ (k % n) := by
        rw [pow_add, mul_comm (k / n) n, ← pow_mul]
    _ ≡ 1 ^ (k / n) * 2 ^ (k % n) [MOD 2 ^ n - 1] :=
        Nat.ModEq.mul (h2n.pow _) (Nat.ModEq.refl _)
    _ = 2 ^ (k % n) := by simp

/-- If `2 ^ p + t * 2 ^ q ≡ t (mod 2 ^ n - 1)` with `q = 0` then `2 ^ p ≡ 0`, which is
impossible since `2 ^ n - 1` is odd and `≥ 3`. -/
private theorem not_congr_of_q_zero {n p t : ℕ} (h2 : 2 ≤ n)
    (h : 2 ^ p + t * 2 ^ 0 ≡ t [MOD 2 ^ n - 1]) : False := by
  set N := 2 ^ n - 1 with hN
  have hN3 : 3 ≤ N := by
    have h4 : 4 ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hNodd : Odd N := odd_two_pow_sub_one (by omega)
  have hcop : N.Coprime (2 ^ p) := (Nat.coprime_two_right.mpr hNodd).pow_right p
  have hzero : 2 ^ p ≡ 0 [MOD N] := by
    have h' : 2 ^ p + t ≡ 0 + t [MOD N] := by simpa using h
    exact Nat.ModEq.add_right_cancel' t h'
  have hdvd : N ∣ 2 ^ p :=
    Nat.dvd_of_mod_eq_zero (show 2 ^ p % N = 0 by simpa [Nat.ModEq] using hzero)
  have hdvd1 : N ∣ 1 := hcop.dvd_of_dvd_mul_left (by simpa using hdvd)
  have := Nat.le_of_dvd (by norm_num) hdvd1
  omega

/-- **Arithmetic core of the final step of Higman's Lemma 8 (Suzuki form).**  For `2 ≤ n`,
`i < j < n`, `t = 2 ^ i + 2 ^ j`, the congruence `2 ^ p + t * 2 ^ q ≡ t [MOD 2 ^ n - 1]` has at
most one solution `(p, q)` with `p, q < n`. -/
theorem pow_two_mod_unique_plus (n i j p q p' q' : ℕ) (h2 : 2 ≤ n) (hij : i < j) (hjn : j < n)
    (hp : p < n) (hq : q < n) (hp' : p' < n) (hq' : q' < n)
    (h1 : 2 ^ p + (2 ^ i + 2 ^ j) * 2 ^ q ≡ 2 ^ i + 2 ^ j [MOD 2 ^ n - 1])
    (h2' : 2 ^ p' + (2 ^ i + 2 ^ j) * 2 ^ q' ≡ 2 ^ i + 2 ^ j [MOD 2 ^ n - 1]) :
    p = p' ∧ q = q' := by
  set N := 2 ^ n - 1 with hN
  set t := 2 ^ i + 2 ^ j with ht
  have hn : 1 ≤ n := by omega
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0] at h1
    exact not_congr_of_q_zero h2 h1
  have hq0' : q' ≠ 0 := by
    intro h0
    rw [h0] at h2'
    exact not_congr_of_q_zero h2 h2'
  -- the substitution `(r, s) ↦ ((r + n - s) % n, n - s)`
  have key : ∀ r s : ℕ, r < n → s < n → s ≠ 0 → 2 ^ r + t * 2 ^ s ≡ t [MOD N] →
      2 ^ ((r + n - s) % n) ≡ t * (2 ^ (n - s) - 1) [MOD N] := by
    intro r s hr hs hs0 h
    have hmul : (2 ^ r + t * 2 ^ s) * 2 ^ (n - s) ≡ t * 2 ^ (n - s) [MOD N] :=
      h.mul (Nat.ModEq.refl _)
    have hexp : (2 ^ r + t * 2 ^ s) * 2 ^ (n - s) = 2 ^ (r + (n - s)) + t * 2 ^ n := by
      have h1 : 2 ^ r * 2 ^ (n - s) = 2 ^ (r + (n - s)) := (pow_add 2 r (n - s)).symm
      have h2 : t * 2 ^ s * 2 ^ (n - s) = t * 2 ^ n := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_of_le (by omega)]
      rw [add_mul, h1, h2]
    rw [hexp] at hmul
    have h2n : (2 : ℕ) ^ n ≡ 1 [MOD N] := two_pow_modEq_one hn
    have ht1 : t * 2 ^ n ≡ t * 1 [MOD N] := Nat.ModEq.mul (Nat.ModEq.refl t) h2n
    rw [mul_one] at ht1
    have h2'' : 2 ^ (r + (n - s)) + t ≡ t * 2 ^ (n - s) [MOD N] :=
      ((Nat.ModEq.refl (2 ^ (r + (n - s)))).add ht1).symm.trans hmul
    have hsplit : t * 2 ^ (n - s) = t * (2 ^ (n - s) - 1) + t := by
      have h2' : 1 ≤ 2 ^ (n - s) := Nat.one_le_pow _ _ (by norm_num)
      calc t * 2 ^ (n - s) = t * ((2 ^ (n - s) - 1) + 1) := by
            rw [Nat.sub_add_cancel h2']
        _ = t * (2 ^ (n - s) - 1) + t * 1 := by rw [mul_add]
        _ = t * (2 ^ (n - s) - 1) + t := by rw [mul_one]
    rw [hsplit] at h2''
    have h3 : 2 ^ (r + (n - s)) ≡ t * (2 ^ (n - s) - 1) [MOD N] :=
      Nat.ModEq.add_right_cancel' t h2''
    have h4 : 2 ^ (r + (n - s)) ≡ 2 ^ ((r + n - s) % n) [MOD N] := by
      have he : r + (n - s) = r + n - s := by omega
      rw [he]
      exact pow_modEq_mod hn
    exact h4.symm.trans h3
  have hsubq : (n - q) % n = n - q := Nat.mod_eq_of_lt (by omega)
  have hsubq' : (n - q') % n = n - q' := Nat.mod_eq_of_lt (by omega)
  have h1' : 2 ^ ((p + n - q) % n) ≡ t * (2 ^ ((n - q) % n) - 1) [MOD N] := by
    rw [hsubq]
    exact key p q hp hq hq0 h1
  have h2'' : 2 ^ ((p' + n - q') % n) ≡ t * (2 ^ ((n - q') % n) - 1) [MOD N] := by
    rw [hsubq']
    exact key p' q' hp' hq' hq0' h2'
  have hfin := pow_two_mod_unique n i j ((p + n - q) % n) ((n - q) % n) ((p' + n - q') % n)
    ((n - q') % n) h2 hij hjn (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h1' h2''
  obtain ⟨hpq, hqq⟩ := hfin
  have hq_eq : q = q' := by
    rw [hsubq, hsubq'] at hqq
    omega
  have hp_eq : p = p' := by
    have hB : (p + n - q) % n = (p' + n - q') % n := hpq
    rw [← hq_eq] at hB
    have e1 : p + n - q = p + (n - q) := by omega
    have e2 : p' + n - q = p' + (n - q) := by omega
    rw [e1, e2] at hB
    have hD : p ≡ p' [MOD n] := Nat.ModEq.add_right_cancel' (n - q) hB
    exact Nat.ModEq.eq_of_lt_of_lt hD hp hp'
  exact ⟨hp_eq, hq_eq⟩

end Work.Higman
