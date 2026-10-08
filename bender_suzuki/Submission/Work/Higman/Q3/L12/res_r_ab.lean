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

/-- `2 ^ a ≡ 2 ^ (a % n)` modulo `2 ^ n - 1` (local copy, so that this file does not need to
import the heavier `d_case_congruence` chain). -/
theorem res_r_ab_pow_two_modEq {n a : ℕ} (hn : 0 < n) :
    (2 : ℕ) ^ a ≡ 2 ^ (a % n) [MOD 2 ^ n - 1] := by
  conv_lhs => rw [← Nat.div_add_mod a n]
  rw [pow_add, pow_mul]
  have hbase : (2 : ℕ) ^ n ≡ 1 [MOD (2 : ℕ) ^ n - 1] := by
    have hle : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_two_pow
    exact ((Nat.modEq_iff_dvd' hle).mpr (dvd_refl ((2 : ℕ) ^ n - 1))).symm
  have h := (hbase.pow (a / n)).mul (Nat.ModEq.refl (n := (2 : ℕ) ^ n - 1) (2 ^ (a % n)))
  simpa [one_pow, mul_comm] using h

/-- **The `r`/`ab` resonance congruence of Higman's Lemma 12.**

With `2 ≤ n`, `0 < r < n`, `k, l < n`, the congruence

`2 ^ k * 2 + 2 ^ l * (1 + 2 ^ r) ≡ 2 * (1 + 2 ^ r)  (mod 2 ^ n - 1)`

forces

`k ≡ n - 1`, `2 * r + 1 ≡ 0`, `l ≡ r + 1  (mod n)`   or
`k ≡ r - 1`, `2 * r - 1 ≡ 0`, `l ≡ n + 1 - r  (mod n)`.

Proof: rewrite as `2 ^ (k+1) + 2 ^ l + 2 ^ (l+r) ≡ 2 ^ 1 + 2 ^ (r+1)`, reduce every exponent
modulo `n`, and apply Higman's three-versus-two-powers congruence
(`Work.Higman.Q3.L12.three_pow_congruence`).  Of its six alternatives four are contradictory
(they force `n ∣ 1` or `n ∣ r`), and the remaining two are exactly the two claimed branches.
Exhaustively verified for `n ≤ 44`. -/
theorem res_r_ab {n r k l : ℕ} (hn : 2 ≤ n) (hr : r < n) (hr0 : r ≠ 0) (hr1 : 1 ≤ r)
    (hk : k < n) (hl : l < n)
    (h : 2 ^ k * 2 + 2 ^ l * (1 + 2 ^ r) ≡ 2 * (1 + 2 ^ r) [MOD 2 ^ n - 1]) :
    (k ≡ n - 1 [MOD n] ∧ 2 * r + 1 ≡ 0 [MOD n] ∧ l ≡ r + 1 [MOD n]) ∨
    (k ≡ r - 1 [MOD n] ∧ 2 * r - 1 ≡ 0 [MOD n] ∧ l ≡ n + 1 - r [MOD n]) := by
  have hnpos : 0 < n := by omega
  have hlt : 1 < n := by omega
  -- rewrite the hypothesis into the shape `2 ^ (k+1) + 2 ^ l + 2 ^ (l+r) ≡ 2 + 2 ^ (r+1)`
  have e1 : 2 ^ k * 2 = 2 ^ (k + 1) := (pow_succ 2 k).symm
  have e2 : 2 ^ l * (1 + 2 ^ r) = 2 ^ l + 2 ^ (l + r) := by
    rw [mul_add, mul_one, ← pow_add]
  have e3 : 2 * (1 + 2 ^ r) = 2 + 2 ^ (r + 1) := by
    have hh : 2 * 2 ^ r = 2 ^ (r + 1) := by rw [mul_comm]; exact (pow_succ 2 r).symm
    rw [mul_add, mul_one, hh]
  rw [e1, e2, e3, ← add_assoc] at h
  -- reduce every exponent modulo `n`
  have hp1 : (2:ℕ) ^ (k + 1) ≡ 2 ^ ((k + 1) % n) [MOD 2 ^ n - 1] :=
    res_r_ab_pow_two_modEq hnpos
  have hplr : (2:ℕ) ^ (l + r) ≡ 2 ^ ((l + r) % n) [MOD 2 ^ n - 1] :=
    res_r_ab_pow_two_modEq hnpos
  have hpr1 : (2:ℕ) ^ (r + 1) ≡ 2 ^ ((r + 1) % n) [MOD 2 ^ n - 1] :=
    res_r_ab_pow_two_modEq hnpos
  have hL : 2 ^ (k+1) + 2 ^ l + 2 ^ (l+r)
      ≡ 2 ^ ((k+1)%n) + 2 ^ l + 2 ^ ((l+r)%n) [MOD 2 ^ n - 1] :=
    (hp1.add (Nat.ModEq.refl (n := 2 ^ n - 1) (2 ^ l))).add hplr
  have hR : 2 + 2 ^ (r+1) ≡ 2 ^ 1 + 2 ^ ((r+1)%n) [MOD 2 ^ n - 1] :=
    ((show (2:ℕ) ≡ 2 ^ 1 [MOD 2 ^ n - 1] by rw [pow_one])).add hpr1
  have hmain : 2 ^ ((k+1)%n) + 2 ^ l + 2 ^ ((l+r)%n)
      ≡ 2 ^ 1 + 2 ^ ((r+1)%n) [MOD 2 ^ n - 1] :=
    hL.symm.trans (h.trans hR)
  -- Higman's three-versus-two-powers congruence
  rcases three_pow_congruence hnpos (a := (k+1) % n) (b := l) (c := (l+r) % n)
      (d := 1) (e := (r+1) % n)
      (Nat.mod_lt _ hnpos) hl (Nat.mod_lt _ hnpos) hlt (Nat.mod_lt _ hnpos) hmain with
    h1 | h2 | h3 | h4 | h5 | h6
  · -- `a = b`, `d = (a+1)%n`, `c = e`: impossible
    exfalso
    obtain ⟨hab, hd1, hce⟩ := h1
    have ha0 : (k+1) % n = 0 := by
      have hmod : (1:ℕ) ≡ ((k+1)%n + 1) [MOD n] := by
        show 1 % n = ((k+1)%n + 1) % n
        rw [Nat.mod_eq_of_lt hlt]
        exact hd1
      have h3' : n ∣ ((k+1)%n + 1) - 1 :=
        (Nat.modEq_iff_dvd' (by omega : 1 ≤ (k+1)%n + 1)).mp hmod
      have h4 : n ∣ (k+1) % n := by simpa [Nat.add_sub_cancel] using h3'
      exact Nat.eq_zero_of_dvd_of_lt h4 (Nat.mod_lt _ hnpos)
    have hl0 : l = 0 := by rw [← hab, ha0]
    have hce' : (r+1) % n = r := by
      have hh := hce
      rw [hl0, zero_add, Nat.mod_eq_of_lt hr] at hh
      exact hh.symm
    have hdvd1 : n ∣ 1 := by
      have hmod : (r + 1) ≡ r [MOD n] := by
        show (r + 1) % n = r % n
        rw [Nat.mod_eq_of_lt hr]
        exact hce'
      have hh := (Nat.modEq_iff_dvd' (by omega : r ≤ r + 1)).mp hmod.symm
      simpa [Nat.add_sub_cancel_left] using hh
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd1) (by omega)
  · -- `a = b`, `e = (a+1)%n`, `c = d`: the second branch
    obtain ⟨hab, he2, hcd⟩ := h2
    have he2' : (r + 1) % n = (l + 1) % n := by rw [he2, hab]
    have hl_eq : l = r := by
      have hmod : l + 1 ≡ r + 1 [MOD n] := he2'.symm
      exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' 1 hmod) hl hr
    have h2r : (2 * r) % n = 1 := by
      rw [hl_eq] at hcd
      simpa [two_mul] using hcd
    have hmod2r : 2 * r ≡ 1 [MOD n] := by
      show (2 * r) % n = 1 % n
      rw [Nat.mod_eq_of_lt hlt]
      exact h2r
    have hdvd : n ∣ 2 * r - 1 :=
      (Nat.modEq_iff_dvd' (by omega : 1 ≤ 2 * r)).mp hmod2r.symm
    have hN1 : (1:ℕ) ≡ n + 1 [MOD n] := by
      show 1 % n = (n+1) % n
      rw [Nat.add_mod, Nat.mod_self, Nat.mod_eq_of_lt hlt, Nat.zero_add,
        Nat.mod_eq_of_lt hlt]
    have hrr : r + r ≡ n + 1 [MOD n] := by
      have hh : 2 * r ≡ n + 1 [MOD n] := hmod2r.trans hN1
      simpa [two_mul] using hh
    have hr_goal : r ≡ n + 1 - r [MOD n] := by
      have hsub : r + (n + 1 - r) = n + 1 := by omega
      have hA : r + r ≡ r + (n + 1 - r) [MOD n] := by rw [hsub]; exact hrr
      exact Nat.ModEq.add_left_cancel' r hA
    have hk1 : k + 1 = r := by
      have hk1mod : (k + 1) % n = r := by rw [hab, hl_eq]
      rcases Nat.lt_or_ge (k + 1) n with hcase | hcase
      · rwa [Nat.mod_eq_of_lt hcase] at hk1mod
      · have hkn : k + 1 = n := by omega
        rw [hkn, Nat.mod_self] at hk1mod
        omega
    have hk' : k = r - 1 := by omega
    refine Or.inr ⟨?_, ?_, ?_⟩
    · rw [hk']
    · exact Nat.modEq_zero_iff_dvd.mpr hdvd
    · rw [hl_eq]; exact hr_goal
  · -- `a = c`, `d = (a+1)%n`, `b = e`: the first branch
    obtain ⟨hac, hd3, hbe⟩ := h3
    have ha0 : (k+1) % n = 0 := by
      have hmod : (1:ℕ) ≡ ((k+1)%n + 1) [MOD n] := by
        show 1 % n = ((k+1)%n + 1) % n
        rw [Nat.mod_eq_of_lt hlt]
        exact hd3
      have h3' : n ∣ ((k+1)%n + 1) - 1 :=
        (Nat.modEq_iff_dvd' (by omega : 1 ≤ (k+1)%n + 1)).mp hmod
      have h4 : n ∣ (k+1) % n := by simpa [Nat.add_sub_cancel] using h3'
      exact Nat.eq_zero_of_dvd_of_lt h4 (Nat.mod_lt _ hnpos)
    have hk1dvd : n ∣ k + 1 := Nat.dvd_of_mod_eq_zero ha0
    have hk1 : k + 1 = n := le_antisymm (by omega) (Nat.le_of_dvd (by omega) hk1dvd)
    have hk' : k = n - 1 := by omega
    have hle : l ≡ r + 1 [MOD n] := by
      show l % n = (r + 1) % n
      rw [Nat.mod_eq_of_lt hl]
      exact hbe
    have hl0 : l + r ≡ 0 [MOD n] := by
      show (l + r) % n = 0 % n
      rw [← hac, ha0, Nat.zero_mod]
    have hsum : 2 * r + 1 ≡ 0 [MOD n] := by
      have hh : (r + 1) + r ≡ 0 [MOD n] := (hle.add_right r).symm.trans hl0
      have h' : (r + 1) + r = 2 * r + 1 := by ring
      rwa [h'] at hh
    exact Or.inl ⟨by rw [hk'], hsum, hle⟩
  · -- `a = c`, `e = (a+1)%n`, `b = d`: impossible
    exfalso
    obtain ⟨hac, he4, hbd⟩ := h4
    have hkr : (k+1) % n = (r+1) % n := by rw [hac, hbd, Nat.add_comm]
    have hkey : (r+1) % n = ((r+1) % n + 1) % n := he4.trans (by rw [hkr])
    have hdvd1 : n ∣ 1 := by
      have hmod : (r+1) % n + 1 ≡ (r+1) % n [MOD n] := by
        show ((r+1) % n + 1) % n = ((r+1) % n) % n
        rw [← hkey, Nat.mod_mod]
      have hh :=
        (Nat.modEq_iff_dvd' (by omega : (r+1) % n ≤ (r+1) % n + 1)).mp hmod.symm
      simpa [Nat.add_sub_cancel_left] using hh
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd1) (by omega)
  · -- `b = c`, `d = (b+1)%n`, `a = e`: forces `r = 0`
    exfalso
    obtain ⟨hbc, hd5, hae⟩ := h5
    have hmod : l + r ≡ l [MOD n] := by
      show (l + r) % n = l % n
      rw [← hbc, Nat.mod_eq_of_lt hl]
    have hdvd : n ∣ r := by
      have hh := (Nat.modEq_iff_dvd' (by omega : l ≤ l + r)).mp hmod.symm
      simpa [Nat.add_sub_cancel_left] using hh
    exact hr0 (Nat.eq_zero_of_dvd_of_lt hdvd hr)
  · -- `b = c`, `e = (b+1)%n`, `a = d`: forces `r = 0`
    exfalso
    obtain ⟨hbc, he6, had⟩ := h6
    have hmod : l + r ≡ l [MOD n] := by
      show (l + r) % n = l % n
      rw [← hbc, Nat.mod_eq_of_lt hl]
    have hdvd : n ∣ r := by
      have hh := (Nat.modEq_iff_dvd' (by omega : l ≤ l + r)).mp hmod.symm
      simpa [Nat.add_sub_cancel_left] using hh
    exact hr0 (Nat.eq_zero_of_dvd_of_lt hdvd hr)

end Work.Higman.Q3.L12
