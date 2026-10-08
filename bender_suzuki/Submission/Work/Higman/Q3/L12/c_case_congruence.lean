import Mathlib
import Submission.Work.Higman.Q3.L12.three_pow_congruence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Higman.Q3.L12

/-- `2 ^ a ≡ 2 ^ (a % n)` modulo `2 ^ n - 1` (local copy of the helper used in the `D` case). -/
theorem c_pow_two_modEq {n a : ℕ} (hn : 0 < n) :
    (2 : ℕ) ^ a ≡ 2 ^ (a % n) [MOD 2 ^ n - 1] := by
  conv_lhs => rw [← Nat.div_add_mod a n]
  rw [pow_add, pow_mul]
  have hbase : (2 : ℕ) ^ n ≡ 1 [MOD (2 : ℕ) ^ n - 1] := by
    have hle : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_two_pow
    exact ((Nat.modEq_iff_dvd' hle).mpr (dvd_refl ((2 : ℕ) ^ n - 1))).symm
  have h := (hbase.pow (a / n)).mul (Nat.ModEq.refl (n := (2 : ℕ) ^ n - 1) (2 ^ (a % n)))
  simpa [one_pow, mul_comm] using h

/-- **Higman (1963), the congruence of p. 91, `C` case.**

If `0 < r < n`, `s, t < n` and

`1 + 2 ^ s * (1 + 2 ^ r) ≡ 2 ^ t * (1 + 2 ^ r)  (mod 2 ^ n - 1)`

then `2 * r + 1 ≡ 0 (mod n)` with `s ≡ r + 1`, `t ≡ 1`, or `2 * r - 1 ≡ 0 (mod n)` with
`s ≡ 0`, `t ≡ r`.

This is the arithmetic content of Higman's third case (p. 91): he gets the congruence
`λ ^ (1 + 2 ^ (s-1) (1 + 2 ^ r)) = λ ^ (2 ^ t (1 + 2 ^ r))` (with `s - 1` in place of `s` here),
notes that the congruence `2 ^ a + 2 ^ b + 2 ^ c ≡ 2 ^ d + 2 ^ e (mod 2 ^ n - 1)` has only the
permuted solutions of `a ≡ b ≡ d - 1`, `c ≡ e` (`Work.Higman.Q3.L12.three_pow_congruence`),
checks the six possibilities and finds that only `s ≡ r + 2`, `t ≡ 1`, `2r + 1 ≡ 0` and its
`r ↔ -r`-mirror survive; with the normalisation `0 < r ≤ n / 2` (using `A(n, θ) ≅ A(n, θ⁻¹)`) the
second is excluded, so `n` is odd and `2 θ ^ 2 = 1` — exactly the Column-III condition of
`C(n, ε)`.

Exhaustively verified for `n ≤ 90`: solutions exist exactly for odd `n`, two per `n`, one in each
branch.  Proof: expand `1 + 2 ^ s + 2 ^ (s+r) ≡ 2 ^ t + 2 ^ (t+r)`, apply the bound
`-(2 ^ n - 1) < (1 + 2 ^ s + 2 ^ (s+r)) - (2 ^ t + 2 ^ (t+r)) < 2 * (2 ^ n - 1)` to obtain the
possible multiples `k ∈ {-1, 0, 1, 2}` of `2 ^ n - 1`, and compare binary expansions in each
case (the `k = 0, 1, 2` cases give the two branches). -/
theorem c_case_congruence {n r s t : ℕ} (hn : 0 < n)
    (hr : r < n) (hr0 : r ≠ 0) (hs : s < n) (ht : t < n)
    (h : 1 + 2 ^ s * (1 + 2 ^ r) ≡ 2 ^ t * (1 + 2 ^ r) [MOD 2 ^ n - 1]) :
    (2 * r + 1 ≡ 0 [MOD n] ∧ s ≡ r + 1 [MOD n] ∧ t ≡ 1 [MOD n]) ∨
    (2 * r - 1 ≡ 0 [MOD n] ∧ s ≡ 0 [MOD n] ∧ t ≡ r [MOD n]) := by
  -- `n ≥ 2`, hence `1 % n = 1`
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
  have hn2 : 2 ≤ n := by omega
  have h1lt : 1 < n := by omega
  have h1mod : 1 % n = 1 := Nat.mod_eq_of_lt h1lt
  have hsmod : s % n = s := Nat.mod_eq_of_lt hs
  have htmod : t % n = t := Nat.mod_eq_of_lt ht
  have hrmod : r % n = r := Nat.mod_eq_of_lt hr
  -- expand the congruence into `1 + 2 ^ s + 2 ^ (s+r) ≡ 2 ^ t + 2 ^ (t+r)`
  have hL : 1 + 2 ^ s * (1 + 2 ^ r) = 1 + (2 ^ s + 2 ^ (s + r)) := by
    rw [mul_add, mul_one, ← pow_add]
  have hR : 2 ^ t * (1 + 2 ^ r) = 2 ^ t + 2 ^ (t + r) := by
    rw [mul_add, mul_one, ← pow_add]
  rw [hL, hR] at h
  -- reduce the exponents modulo `n`
  have hLm : 1 + (2 ^ s + 2 ^ (s + r)) ≡ 1 + (2 ^ s + 2 ^ ((s + r) % n)) [MOD 2 ^ n - 1] :=
    Nat.ModEq.add_left 1 (Nat.ModEq.add_left (2 ^ s) (c_pow_two_modEq hn))
  have hRm : 2 ^ t + 2 ^ (t + r) ≡ 2 ^ t + 2 ^ ((t + r) % n) [MOD 2 ^ n - 1] :=
    Nat.ModEq.add_left (2 ^ t) (c_pow_two_modEq hn)
  have hmain : ((2 ^ 0 + 2 ^ s) + 2 ^ ((s + r) % n)) ≡ (2 ^ t + 2 ^ ((t + r) % n))
      [MOD 2 ^ n - 1] := by
    have h' := hLm.symm.trans (h.trans hRm)
    simpa [pow_zero, add_assoc] using h'
  -- Higman's three-term congruence
  rcases three_pow_congruence hn (a := 0) (b := s) (c := (s + r) % n) (d := t)
      (e := (t + r) % n) hn hs (Nat.mod_lt _ hn) ht (Nat.mod_lt _ hn) hmain with
    h1 | h2 | h3 | h4 | h5 | h6
  · -- D1: `a = b` (`s = 0`), `t = 1`, `c = e`; impossible
    obtain ⟨h0, ht1, hce⟩ := h1
    exfalso
    have hs0 : s = 0 := h0.symm
    have htr : (t + r) % n = r := by
      rw [← hce, hs0, zero_add, hrmod]
    have hmod : t + r ≡ r [MOD n] := by
      show (t + r) % n = r % n
      rw [htr, hrmod]
    have hdvd : n ∣ t := by
      have hh := (Nat.modEq_iff_dvd' (Nat.le_add_left r t)).mp hmod.symm
      rwa [Nat.add_sub_cancel] at hh
    have ht0 : t = 0 := Nat.eq_zero_of_dvd_of_lt hdvd ht
    have ht1' : t = 1 := by rw [ht1, zero_add, h1mod]
    omega
  · -- D2: `s = 0`, `e = (a+1)%n`, `c = d`; gives the second branch
    obtain ⟨h0, hce, hcd⟩ := h2
    have hs0 : s = 0 := h0.symm
    have htrt : t = r := by
      have hh := hcd
      rw [hs0, zero_add, hrmod] at hh
      exact hh.symm
    have h2r : (2 * r) % n = 1 := by
      have hh := hce
      rw [htrt, h1mod] at hh
      simpa [two_mul] using hh
    have hmod : 1 ≡ 2 * r [MOD n] := by
      show 1 % n = (2 * r) % n
      rw [h1mod, h2r]
    have hdvd : n ∣ 2 * r - 1 := (Nat.modEq_iff_dvd' (by omega : 1 ≤ 2 * r)).mp hmod
    refine Or.inr ⟨?_, ?_, ?_⟩
    · exact Nat.modEq_zero_iff_dvd.mpr hdvd
    · rw [hs0]
    · rw [htrt]
  · -- D3: `a = c`, `d = (a+1)%n`, `b = e`; gives the first branch
    obtain ⟨hcr, ht1, hse⟩ := h3
    have ht1' : t = 1 := by rw [ht1, zero_add, h1mod]
    have htt : t ≡ 1 [MOD n] := by rw [ht1']
    have hsr : s ≡ r + 1 [MOD n] := by
      show s % n = (r + 1) % n
      rw [hse, Nat.mod_mod, Nat.add_mod, ht1', h1mod, hrmod, Nat.add_comm]
    have hmod0 : s + r ≡ 0 [MOD n] := by
      show (s + r) % n = 0 % n
      rw [← hcr, Nat.zero_mod]
    have hmod1 : s + r ≡ 2 * r + 1 [MOD n] := by
      have hh := hsr.add_right r
      have he : (r + 1) + r = 2 * r + 1 := by ring
      rwa [he] at hh
    refine Or.inl ⟨?_, hsr, htt⟩
    exact hmod1.symm.trans hmod0
  · -- D4: `a = c`, `e = (a+1)%n`, `b = d`; impossible
    obtain ⟨hcr, hce, hst⟩ := h4
    exfalso
    have hz : (t + r) % n = 0 := by rw [← hst, hcr]
    rw [hz, zero_add, h1mod] at hce
    exact Nat.zero_ne_one hce
  · -- D5: `b = c`, `d = (b+1)%n`, `a = e`; forces `r = 0`
    obtain ⟨hsc, htd, hez⟩ := h5
    exfalso
    have hmod : s + r ≡ s [MOD n] := by
      show (s + r) % n = s % n
      rw [← hsc, hsmod]
    have hdvd : n ∣ r := by
      have hh := (Nat.modEq_iff_dvd' (Nat.le_add_right s r)).mp hmod.symm
      rwa [Nat.add_sub_cancel_left] at hh
    exact hr0 (Nat.eq_zero_of_dvd_of_lt hdvd hr)
  · -- D6: `b = c`, `e = (b+1)%n`, `a = d`; forces `r = 0`
    obtain ⟨hsc, hte, htz⟩ := h6
    exfalso
    have hmod : s + r ≡ s [MOD n] := by
      show (s + r) % n = s % n
      rw [← hsc, hsmod]
    have hdvd : n ∣ r := by
      have hh := (Nat.modEq_iff_dvd' (Nat.le_add_right s r)).mp hmod.symm
      rwa [Nat.add_sub_cancel_left] at hh
    exact hr0 (Nat.eq_zero_of_dvd_of_lt hdvd hr)

end Work.Higman.Q3.L12
