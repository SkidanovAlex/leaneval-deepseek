import Mathlib

/-!
# Elementary support for `Commons.Data.Int.oneAddInvPowEq`

Multiplicative independence of `1 + 1/m` and `1 + 1/n` for distinct integers
`m, n ∉ {-1, 0}` with `10^6 * |m - n| < |n|`.

## Strategy

Write `X = 1 + 1/m = |m+1| / |m|` and `Y = 1 + 1/n = |n+1| / |n|` as reduced
fractions whose numerator and denominator are consecutive positive integers
(`A = B + 1 ∨ B = A + 1`).  A power relation `X^r Y^s = 1` with `r, s ≠ 0`
forces, by unique factorization (via `Nat.factorization`), either `X = Y`
(which gives `m = n`) or `X * Y = 1` (which gives `m + n + 1 = 0`); both are
excluded by `m ≠ n` and by the gap hypothesis.
-/

namespace Commons.Data.Int

/-! ## Pure natural-number lemmas -/

/-- `u^k = v^k + 1` with `v ≥ 1` forces `k = 1`. -/
lemma oneAddInvPowEq_pow_sub_eq_one (u v k : ℕ) (hv : 0 < v) (h : u ^ k = v ^ k + 1) :
    k = 1 := by
  by_cases hk : k = 1
  · exact hk
  have hk0 : k ≠ 0 := by
    intro hk0
    subst hk0
    norm_num at h
  have hk2 : 2 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have huv : v < u := by
    have hgt : v ^ k < u ^ k := by rw [h]; omega
    by_contra hnot
    have hle : u ≤ v := by omega
    have : u ^ k ≤ v ^ k := Nat.pow_le_pow_left hle k
    omega
  have hu1 : v + 1 ≤ u := by omega
  have hmid : v ^ k + 2 ≤ (v + 1) ^ k := by
    have hpow1 : v ^ (k - 1) ≤ (v + 1) ^ (k - 1) :=
      Nat.pow_le_pow_left (by omega : v ≤ v + 1) (k - 1)
    have hmul : v ^ k ≤ v * (v + 1) ^ (k - 1) := by
      calc v ^ k = v ^ ((k - 1) + 1) := by rw [Nat.sub_add_cancel hk1]
        _ = v * v ^ (k - 1) := by rw [pow_succ']
        _ ≤ v * (v + 1) ^ (k - 1) := Nat.mul_le_mul_left v hpow1
    have hdec : (v + 1) ^ k = v * (v + 1) ^ (k - 1) + (v + 1) ^ (k - 1) := by
      calc (v + 1) ^ k = (v + 1) ^ ((k - 1) + 1) := by rw [Nat.sub_add_cancel hk1]
        _ = (v + 1) * (v + 1) ^ (k - 1) := by rw [pow_succ']
        _ = v * (v + 1) ^ (k - 1) + (v + 1) ^ (k - 1) := by ring
    have hsmall : 2 ≤ (v + 1) ^ (k - 1) := by
      have he1 : (v + 1) ^ 1 ≤ (v + 1) ^ (k - 1) :=
        Nat.pow_le_pow_right (by omega : 0 < v + 1) (by omega : 1 ≤ k - 1)
      have hval : (v + 1) ^ 1 = v + 1 := by simp
      omega
    omega
  have hb : (v + 1) ^ k ≤ u ^ k := Nat.pow_le_pow_left hu1 k
  omega

/-- Consecutive natural numbers are coprime. -/
lemma oneAddInvPowEq_coprime_consecutive {A B : ℕ} (h : A = B + 1 ∨ B = A + 1) :
    Nat.Coprime A B := by
  rcases h with h | h
  · rw [h]
    exact ((Nat.coprime_self_add_right (m := B) (n := 1)).mpr (Nat.coprime_one_right B)).symm
  · rw [h]
    exact (Nat.coprime_self_add_right (m := A) (n := 1)).mpr (Nat.coprime_one_right A)

/-- Common power base: from `A^r = C^s` with coprime `r, s`, both `A` and `C`
are powers of one common natural. -/
lemma oneAddInvPowEq_commonBase {A C r s : ℕ} (hA : A ≠ 0) (hC : C ≠ 0) (_hr : r ≠ 0)
    (hs : s ≠ 0) (hcop : Nat.Coprime r s) (h : A ^ r = C ^ s) :
    ∃ w : ℕ, A = w ^ s ∧ C = w ^ r := by
  have hfac : ∀ p : ℕ, r * A.factorization p = s * C.factorization p := by
    intro p
    have hfac := congrArg (fun n : ℕ => n.factorization p) h
    simpa [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] using hfac
  have hdvd : ∀ p : ℕ, s ∣ A.factorization p := by
    intro p
    have h1 : s ∣ r * A.factorization p := by
      rw [hfac p]
      exact dvd_mul_right s (C.factorization p)
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop.symm h1
  let f : ℕ →₀ ℕ := Finsupp.onFinset A.factorization.support (fun p => A.factorization p / s) (by
      intro p hp
      have hz : A.factorization p ≠ 0 := by
        intro hz0
        simp [hz0] at hp
      exact Finsupp.mem_support_iff.mpr hz)
  have hfprime : ∀ p ∈ f.support, Nat.Prime p := by
    intro p hp
    have hfp : f p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hz : A.factorization p ≠ 0 := by
      intro hz0
      simp [f, hz0] at hfp
    by_contra hnp
    have : A.factorization p = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      exact Or.inl hnp
    exact hz this
  let w : ℕ := f.prod fun p k => p ^ k
  have hwf : w.factorization = f := by
    dsimp [w]
    exact Nat.prod_pow_factorization_eq_self hfprime
  have hfs : ∀ p : ℕ, A.factorization p = s * f p := by
    intro p
    dsimp [f]
    exact (Nat.mul_div_cancel' (hdvd p)).symm
  have hwpos : 1 ≤ w := by
    dsimp [w]
    apply Finset.one_le_prod'
    intro p hp
    have hp2 : 2 ≤ p := Nat.Prime.two_le (hfprime p hp)
    exact Nat.one_le_pow (f p) p (by omega)
  have hAeq : A = w ^ s := by
    apply Nat.eq_of_factorization_eq hA
    · exact pow_ne_zero s (by omega : w ≠ 0)
    · intro p
      calc
        A.factorization p = s * f p := hfs p
        _ = s * w.factorization p := by rw [hwf]
        _ = (w ^ s).factorization p := by
          rw [Nat.factorization_pow]
          simp [Finsupp.smul_apply, smul_eq_mul]
  have hfr : ∀ p : ℕ, C.factorization p = r * f p := by
    intro p
    have h1 := hfac p
    have h2 : s * (r * f p) = s * C.factorization p := by
      calc s * (r * f p) = r * (s * f p) := by ring
        _ = r * A.factorization p := by rw [hfs p]
        _ = s * C.factorization p := h1
    exact (Nat.mul_left_cancel (Nat.pos_of_ne_zero hs) h2).symm
  have hCeq : C = w ^ r := by
    apply Nat.eq_of_factorization_eq hC
    · exact pow_ne_zero r (by omega : w ≠ 0)
    · intro p
      calc
        C.factorization p = r * f p := hfr p
        _ = r * w.factorization p := by rw [hwf]
        _ = (w ^ r).factorization p := by
          rw [Nat.factorization_pow]
          simp [Finsupp.smul_apply, smul_eq_mul]
  exact ⟨w, hAeq, hCeq⟩

/-- If two consecutive pairs `{A,B}`, `{C,D}` satisfy `A^r = C^s` and
`B^r = D^s` with `r, s ≥ 1`, then `A = C` and `B = D`. -/
lemma oneAddInvPowEq_pairPow {A B C D r s : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hD : D ≠ 0) (hAB : A = B + 1 ∨ B = A + 1) (hCD : C = D + 1 ∨ D = C + 1)
    (hr : r ≠ 0) (hs : s ≠ 0) (h1 : A ^ r = C ^ s) (h2 : B ^ r = D ^ s) :
    A = C ∧ B = D := by
  let g := Nat.gcd r s
  let r' := r / g
  let s' := s / g
  have hgpos : 0 < g := by
    by_contra hg0
    have : g = 0 := by omega
    exact hr (Nat.gcd_eq_zero_iff.mp this).1
  have hcop' : Nat.Coprime r' s' := by
    dsimp [r', s', g]
    exact Nat.coprime_div_gcd_div_gcd hgpos
  have hrr : r = g * r' := by
    dsimp [g, r']
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left r s)).symm
  have hss : s = g * s' := by
    dsimp [g, s']
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right r s)).symm
  have hr' : r' ≠ 0 := by
    intro h0
    have : r = g * 0 := by simpa [h0] using hrr
    exact hr (by simpa using this)
  have hs' : s' ≠ 0 := by
    intro h0
    have : s = g * 0 := by simpa [h0] using hss
    exact hs (by simpa using this)
  have hroot1 : (A ^ r') ^ g = (C ^ s') ^ g := by
    calc (A ^ r') ^ g = A ^ (r' * g) := by rw [pow_mul]
      _ = A ^ (g * r') := by rw [mul_comm]
      _ = A ^ r := by rw [hrr]
      _ = C ^ s := h1
      _ = C ^ (g * s') := by rw [← hss]
      _ = C ^ (s' * g) := by rw [mul_comm]
      _ = (C ^ s') ^ g := by rw [pow_mul]
  have hroot2 : (B ^ r') ^ g = (D ^ s') ^ g := by
    calc (B ^ r') ^ g = B ^ (r' * g) := by rw [pow_mul]
      _ = B ^ (g * r') := by rw [mul_comm]
      _ = B ^ r := by rw [hrr]
      _ = D ^ s := h2
      _ = D ^ (g * s') := by rw [← hss]
      _ = D ^ (s' * g) := by rw [mul_comm]
      _ = (D ^ s') ^ g := by rw [pow_mul]
  have h1' : A ^ r' = C ^ s' := (Nat.pow_left_injective (by omega : g ≠ 0)) hroot1
  have h2' : B ^ r' = D ^ s' := (Nat.pow_left_injective (by omega : g ≠ 0)) hroot2
  rcases oneAddInvPowEq_commonBase hA hC hr' hs' hcop' h1' with ⟨u, huA, huC⟩
  rcases oneAddInvPowEq_commonBase hB hD hr' hs' hcop' h2' with ⟨v, hvB, hvD⟩
  have hu0 : u ≠ 0 := by
    intro hz
    have : A = 0 := by rw [huA, hz, zero_pow hs']
    exact hA this
  have hv0 : v ≠ 0 := by
    intro hz
    have : B = 0 := by rw [hvB, hz, zero_pow hs']
    exact hB this
  have hs'1 : s' = 1 := by
    rcases hAB with hAB1 | hAB2
    · have hne : u ^ s' = v ^ s' + 1 := by
        calc u ^ s' = A := huA.symm
          _ = B + 1 := hAB1
          _ = v ^ s' + 1 := by rw [hvB]
      exact oneAddInvPowEq_pow_sub_eq_one u v s' (Nat.pos_of_ne_zero hv0) hne
    · have hne : v ^ s' = u ^ s' + 1 := by
        calc v ^ s' = B := hvB.symm
          _ = A + 1 := hAB2
          _ = u ^ s' + 1 := by rw [huA]
      exact oneAddInvPowEq_pow_sub_eq_one v u s' (Nat.pos_of_ne_zero hu0) hne
  have hr'1 : r' = 1 := by
    rcases hCD with hCD1 | hCD2
    · have hne : u ^ r' = v ^ r' + 1 := by
        calc u ^ r' = C := huC.symm
          _ = D + 1 := hCD1
          _ = v ^ r' + 1 := by rw [hvD]
      exact oneAddInvPowEq_pow_sub_eq_one u v r' (Nat.pos_of_ne_zero hv0) hne
    · have hne : v ^ r' = u ^ r' + 1 := by
        calc v ^ r' = D := hvD.symm
          _ = C + 1 := hCD2
          _ = u ^ r' + 1 := by rw [huC]
      exact oneAddInvPowEq_pow_sub_eq_one v u r' (Nat.pos_of_ne_zero hu0) hne
  have hAC : A = C := by
    calc A = u ^ s' := huA
      _ = u := by rw [hs'1, pow_one]
      _ = u ^ r' := by rw [hr'1, pow_one]
      _ = C := huC.symm
  have hBD : B = D := by
    calc B = v ^ s' := hvB
      _ = v := by rw [hs'1, pow_one]
      _ = v ^ r' := by rw [hr'1, pow_one]
      _ = D := hvD.symm
  exact ⟨hAC, hBD⟩


/-! ## Rational fraction lemmas -/

/-- `(a / b : ℚ) ^ n = (a^n : ℚ) / (b^n : ℚ)`. -/
lemma oneAddInvPowEq_fracPow (A B P : ℕ) :
    ((A : ℚ) / (B : ℚ)) ^ P = (A ^ P : ℚ) / (B ^ P : ℚ) := by
  exact div_pow (A : ℚ) (B : ℚ) P

/-- `X^P * Y^Q = 1` (positive exponents) forces `X * Y = 1` when `X = A/B`,
`Y = C/D` with consecutive numerator/denominator pairs. -/
lemma oneAddInvPowEq_prod {A B C D P Q : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hD : D ≠ 0) (hAB : A = B + 1 ∨ B = A + 1) (hCD : C = D + 1 ∨ D = C + 1)
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : ((A : ℚ) / (B : ℚ)) ^ P * ((C : ℚ) / (D : ℚ)) ^ Q = 1) :
    ((A : ℚ) / (B : ℚ)) * ((C : ℚ) / (D : ℚ)) = 1 := by
  have hnum : A ^ P * C ^ Q = B ^ P * D ^ Q := by
    have hq : ((A : ℚ) / (B : ℚ)) ^ P * ((C : ℚ) / (D : ℚ)) ^ Q =
        (((A ^ P * C ^ Q : ℕ) : ℚ)) / (((B ^ P * D ^ Q : ℕ) : ℚ)) := by
      rw [oneAddInvPowEq_fracPow, oneAddInvPowEq_fracPow]
      norm_num [div_mul_div_comm]
    have hq1 : (((A ^ P * C ^ Q : ℕ) : ℚ)) / (((B ^ P * D ^ Q : ℕ) : ℚ)) = 1 := by
      rw [← hq]
      exact h
    have hden : ((B ^ P * D ^ Q : ℕ) : ℚ) ≠ 0 := by positivity
    have heq : ((A ^ P * C ^ Q : ℕ) : ℚ) = ((B ^ P * D ^ Q : ℕ) : ℚ) :=
      (div_eq_one_iff_eq hden).mp hq1
    exact_mod_cast heq
  have hAd : A ^ P = D ^ Q := by
    apply Nat.dvd_antisymm
    · have hcop : Nat.Coprime (A ^ P) (B ^ P) :=
        (oneAddInvPowEq_coprime_consecutive hAB).pow P P
      have hdv : A ^ P ∣ B ^ P * D ^ Q := by
        rw [← hnum]
        exact ⟨C ^ Q, rfl⟩
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdv
    · have hcop : Nat.Coprime (D ^ Q) (C ^ Q) :=
        (oneAddInvPowEq_coprime_consecutive hCD).symm.pow Q Q
      have hdv0 : D ^ Q ∣ B ^ P * D ^ Q := ⟨B ^ P, by ring⟩
      have hdv : D ^ Q ∣ C ^ Q * A ^ P := by
        have h2 : D ^ Q ∣ A ^ P * C ^ Q := by
          rw [hnum]
          exact hdv0
        simpa [mul_comm] using h2
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdv
  have hBc : B ^ P = C ^ Q := by
    apply Nat.dvd_antisymm
    · have hcop : Nat.Coprime (B ^ P) (A ^ P) :=
        (oneAddInvPowEq_coprime_consecutive hAB).symm.pow P P
      have hdv : B ^ P ∣ A ^ P * C ^ Q := by
        rw [hnum]
        exact ⟨D ^ Q, rfl⟩
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdv
    · have hcop : Nat.Coprime (C ^ Q) (D ^ Q) :=
        (oneAddInvPowEq_coprime_consecutive hCD).pow Q Q
      have hdv0 : C ^ Q ∣ A ^ P * C ^ Q := ⟨A ^ P, by ring⟩
      have hdv : C ^ Q ∣ D ^ Q * B ^ P := by
        have h2 : C ^ Q ∣ B ^ P * D ^ Q := by
          rw [← hnum]
          exact hdv0
        simpa [mul_comm] using h2
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdv
  have hDC : D = C + 1 ∨ C = D + 1 := by
    rcases hCD with hCD1 | hCD2
    · exact Or.inr hCD1
    · exact Or.inl hCD2
  rcases oneAddInvPowEq_pairPow hA hB hD hC hAB hDC hP hQ hAd hBc with ⟨hAD, hBC⟩
  have hAz : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  have hBz : (B : ℚ) ≠ 0 := by exact_mod_cast hB
  have hCz : (C : ℚ) ≠ 0 := by exact_mod_cast hC
  have hDz : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  rw [hAD, hBC]
  field_simp [hBz, hDz]

/-- `X^P = Y^Q` (positive exponents) forces `X = Y` when `X = A/B`, `Y = C/D`
with consecutive numerator/denominator pairs. -/
lemma oneAddInvPowEq_div {A B C D P Q : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hD : D ≠ 0) (hAB : A = B + 1 ∨ B = A + 1) (hCD : C = D + 1 ∨ D = C + 1)
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : ((A : ℚ) / (B : ℚ)) ^ P = ((C : ℚ) / (D : ℚ)) ^ Q) :
    ((A : ℚ) / (B : ℚ)) = ((C : ℚ) / (D : ℚ)) := by
  have hden1 : (B : ℚ) ^ P ≠ 0 := by positivity
  have hden2 : (D : ℚ) ^ Q ≠ 0 := by positivity
  have hnum : A ^ P * D ^ Q = B ^ P * C ^ Q := by
    have h1 : (A : ℚ) ^ P / (B : ℚ) ^ P = (C : ℚ) ^ Q / (D : ℚ) ^ Q := by
      simpa [div_pow] using h
    have hc : (A : ℚ) ^ P * (D : ℚ) ^ Q = (C : ℚ) ^ Q * (B : ℚ) ^ P :=
      (div_eq_div_iff hden1 hden2).mp h1
    norm_cast at hc
    have hnum' : A ^ P * D ^ Q = C ^ Q * B ^ P := by exact_mod_cast hc
    simpa [mul_comm] using hnum'
  have hAC : A ^ P = C ^ Q := by
    apply Nat.dvd_antisymm
    · have hcop : Nat.Coprime (A ^ P) (B ^ P) :=
        (oneAddInvPowEq_coprime_consecutive hAB).pow P P
      have hdv : A ^ P ∣ B ^ P * C ^ Q := by
        rw [← hnum]
        exact ⟨D ^ Q, rfl⟩
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdv
    · have hcop : Nat.Coprime (C ^ Q) (D ^ Q) :=
        (oneAddInvPowEq_coprime_consecutive hCD).pow Q Q
      have hdv0 : C ^ Q ∣ B ^ P * C ^ Q := ⟨B ^ P, by ring⟩
      have hdv : C ^ Q ∣ D ^ Q * A ^ P := by
        have h2 : C ^ Q ∣ A ^ P * D ^ Q := by
          rw [hnum]
          exact hdv0
        simpa [mul_comm] using h2
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdv
  have hBD : B ^ P = D ^ Q := by
    have hcancel : A ^ P * D ^ Q = A ^ P * B ^ P := by
      calc A ^ P * D ^ Q = B ^ P * C ^ Q := hnum
        _ = B ^ P * A ^ P := by rw [hAC]
        _ = A ^ P * B ^ P := by ring
    have hAz : A ^ P ≠ 0 := pow_ne_zero P hA
    exact (Nat.mul_left_cancel (Nat.pos_of_ne_zero hAz) hcancel).symm
  have hAz2 : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  have hBz : (B : ℚ) ≠ 0 := by exact_mod_cast hB
  have hCz : (C : ℚ) ≠ 0 := by exact_mod_cast hC
  have hDz : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  rcases oneAddInvPowEq_pairPow hA hB hC hD hAB hCD hP hQ hAC hBD with ⟨hAC2, hBD2⟩
  rw [hAC2, hBD2]

/-! ## Integer exponent lemmas -/

/-- A positive power of a reduced consecutive fraction cannot equal one. -/
lemma oneAddInvPowEq_pow_ne_one {C D P : ℕ} (hD : D ≠ 0) (hP : P ≠ 0) (hCDn : C ≠ D)
    (h : ((C : ℚ) / (D : ℚ)) ^ P = 1) : False := by
  have hden : (D : ℚ) ^ P ≠ 0 := pow_ne_zero P (by exact_mod_cast hD)
  have hq : (C : ℚ) ^ P / (D : ℚ) ^ P = 1 := by
    simpa [div_pow] using h
  have hceq : (C : ℚ) ^ P = (D : ℚ) ^ P := (div_eq_one_iff_eq hden).mp hq
  norm_cast at hceq
  have hCDP : C ^ P = D ^ P := by exact_mod_cast hceq
  exact hCDn ((Nat.pow_left_injective hP) hCDP)

/-- `(C/D : ℚ) ^ e = 1` with `C ≠ D` (consecutive) forces `e = 0`. -/
lemma oneAddInvPowEq_zpow_eq_one {C D : ℕ} (hD : D ≠ 0) (hCD : C = D + 1 ∨ D = C + 1)
    (e : ℤ) (h : ((C : ℚ) / (D : ℚ)) ^ e = 1) : e = 0 := by
  by_contra he0
  have hCDn : C ≠ D := by rcases hCD with h | h <;> omega
  have hP : e.natAbs ≠ 0 := by
    intro h0
    exact he0 (Int.natAbs_eq_zero.mp h0)
  rcases lt_or_gt_of_ne he0 with he_neg | he_pos
  · have hz : e = -↑e.natAbs := Int.eq_neg_natAbs_of_nonpos (le_of_lt he_neg)
    rw [hz] at h
    rw [zpow_neg, zpow_natCast] at h
    exact oneAddInvPowEq_pow_ne_one hD hP hCDn (inv_eq_one.mp h)
  · have hz : (e.natAbs : ℤ) = e := Int.natAbs_of_nonneg (le_of_lt he_pos)
    rw [← hz] at h
    rw [zpow_natCast] at h
    exact oneAddInvPowEq_pow_ne_one hD hP hCDn h

/-- With `X = A/B`, `Y = C/D` (consecutive pairs) and both exponents nonzero,
`X^r Y^s = 1` forces `X = Y` or `X * Y = 1`. -/
lemma oneAddInvPowEq_core {A B C D : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hD : D ≠ 0) (hAB : A = B + 1 ∨ B = A + 1) (hCD : C = D + 1 ∨ D = C + 1)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (h : ((A : ℚ) / (B : ℚ)) ^ r * ((C : ℚ) / (D : ℚ)) ^ s = 1) :
    ((A : ℚ) / (B : ℚ)) = ((C : ℚ) / (D : ℚ)) ∨
      ((A : ℚ) / (B : ℚ)) * ((C : ℚ) / (D : ℚ)) = 1 := by
  let X : ℚ := (A : ℚ) / (B : ℚ)
  let Y : ℚ := (C : ℚ) / (D : ℚ)
  have hX : X ≠ 0 := by
    dsimp [X]
    exact div_ne_zero (by exact_mod_cast hA) (by exact_mod_cast hB)
  have hY : Y ≠ 0 := by
    dsimp [Y]
    exact div_ne_zero (by exact_mod_cast hC) (by exact_mod_cast hD)
  have hrp_or_n : 0 < r ∨ r < 0 := by omega
  rcases hrp_or_n with hr_pos | hr_neg
  · -- 0 < r
    have hsp_or_n : 0 < s ∨ s < 0 := by omega
    rcases hsp_or_n with hs_pos | hs_neg
    · -- r > 0, s > 0
      have hzr : (r.natAbs : ℤ) = r := Int.natAbs_of_nonneg (le_of_lt hr_pos)
      have hzs : (s.natAbs : ℤ) = s := Int.natAbs_of_nonneg (le_of_lt hs_pos)
      rw [← hzr, ← hzs] at h
      rw [zpow_natCast, zpow_natCast] at h
      have hP : r.natAbs ≠ 0 := by
        intro h0
        exact hr (Int.natAbs_eq_zero.mp h0)
      have hQ : s.natAbs ≠ 0 := by
        intro h0
        exact hs (Int.natAbs_eq_zero.mp h0)
      exact Or.inr (oneAddInvPowEq_prod hA hB hC hD hAB hCD hP hQ h)
    · -- r > 0, s < 0
      have hzr : (r.natAbs : ℤ) = r := Int.natAbs_of_nonneg (le_of_lt hr_pos)
      have hzs : s = -↑s.natAbs := Int.eq_neg_natAbs_of_nonpos (le_of_lt hs_neg)
      rw [← hzr, hzs] at h
      rw [zpow_natCast, zpow_neg, zpow_natCast] at h
      have hP : r.natAbs ≠ 0 := by
        intro h0
        exact hr (Int.natAbs_eq_zero.mp h0)
      have hQ : s.natAbs ≠ 0 := by
        intro h0
        exact hs (Int.natAbs_eq_zero.mp h0)
      have hy' : Y ^ s.natAbs ≠ 0 := pow_ne_zero s.natAbs hY
      have h2 : X ^ r.natAbs * (Y ^ s.natAbs)⁻¹ = 1 := by simpa [X, Y] using h
      have hpq : X ^ r.natAbs = Y ^ s.natAbs := by
        have h3 : (X ^ r.natAbs * (Y ^ s.natAbs)⁻¹) * Y ^ s.natAbs = 1 * Y ^ s.natAbs :=
          congrArg (fun z : ℚ => z * Y ^ s.natAbs) h2
        simpa [mul_assoc, inv_mul_cancel₀ hy', mul_one] using h3
      exact Or.inl (oneAddInvPowEq_div hA hB hC hD hAB hCD hP hQ (by simpa [X, Y] using hpq))
  · -- r < 0
    have hsp_or_n : 0 < s ∨ s < 0 := by omega
    rcases hsp_or_n with hs_pos | hs_neg
    · -- r < 0, s > 0
      have hzr : r = -↑r.natAbs := Int.eq_neg_natAbs_of_nonpos (le_of_lt hr_neg)
      have hzs : (s.natAbs : ℤ) = s := Int.natAbs_of_nonneg (le_of_lt hs_pos)
      rw [hzr, ← hzs] at h
      rw [zpow_neg, zpow_natCast, zpow_natCast] at h
      have hP : r.natAbs ≠ 0 := by
        intro h0
        exact hr (Int.natAbs_eq_zero.mp h0)
      have hQ : s.natAbs ≠ 0 := by
        intro h0
        exact hs (Int.natAbs_eq_zero.mp h0)
      have hx' : X ^ r.natAbs ≠ 0 := pow_ne_zero r.natAbs hX
      have h2 : (X ^ r.natAbs)⁻¹ * Y ^ s.natAbs = 1 := by simpa [X, Y] using h
      have hpq : Y ^ s.natAbs = X ^ r.natAbs := by
        have h3 : X ^ r.natAbs * ((X ^ r.natAbs)⁻¹ * Y ^ s.natAbs) = X ^ r.natAbs * 1 :=
          congrArg (fun z : ℚ => X ^ r.natAbs * z) h2
        simpa [← mul_assoc, mul_inv_cancel₀ hx', mul_one] using h3
      exact Or.inl ((oneAddInvPowEq_div hC hD hA hB hCD hAB hQ hP
        (by simpa [Y, X] using hpq)).symm)
    · -- r < 0, s < 0
      have hzr : r = -↑r.natAbs := Int.eq_neg_natAbs_of_nonpos (le_of_lt hr_neg)
      have hzs : s = -↑s.natAbs := Int.eq_neg_natAbs_of_nonpos (le_of_lt hs_neg)
      rw [hzr, hzs] at h
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast] at h
      have hP : r.natAbs ≠ 0 := by
        intro h0
        exact hr (Int.natAbs_eq_zero.mp h0)
      have hQ : s.natAbs ≠ 0 := by
        intro h0
        exact hs (Int.natAbs_eq_zero.mp h0)
      have hpq : X ^ r.natAbs * Y ^ s.natAbs = 1 := by
        have h2 : (X ^ r.natAbs)⁻¹ * (Y ^ s.natAbs)⁻¹ = 1 := by simpa [X, Y] using h
        have hinv : (X ^ r.natAbs * Y ^ s.natAbs)⁻¹ = 1 := by
          calc
            (X ^ r.natAbs * Y ^ s.natAbs)⁻¹ = (Y ^ s.natAbs)⁻¹ * (X ^ r.natAbs)⁻¹ := by
              rw [mul_inv_rev]
            _ = (X ^ r.natAbs)⁻¹ * (Y ^ s.natAbs)⁻¹ := by ring
            _ = 1 := h2
        exact inv_eq_one.mp hinv
      exact Or.inr (oneAddInvPowEq_prod hA hB hC hD hAB hCD hP hQ (by simpa [X, Y] using hpq))


/-! ## Integer/absolute-value helpers for the main proof -/

/-- Consecutive integers have consecutive absolute values. -/
lemma oneAddInvPowEq_natAbs_succ (z : ℤ) :
    (z + 1).natAbs = z.natAbs + 1 ∨ z.natAbs = (z + 1).natAbs + 1 := by
  by_cases hz : 0 ≤ z
  · left
    have h1 : (((z + 1).natAbs : ℕ) : ℤ) = z + 1 := Int.natAbs_of_nonneg (by omega)
    have h2 : ((z.natAbs : ℕ) : ℤ) = z := Int.natAbs_of_nonneg hz
    have h3 : (((z + 1).natAbs : ℕ) : ℤ) = ((z.natAbs : ℕ) : ℤ) + 1 := by omega
    exact_mod_cast h3
  · right
    have h1 : (((z + 1).natAbs : ℕ) : ℤ) = -(z + 1) := by
      have hh : z + 1 = -(((z + 1).natAbs : ℤ)) := Int.eq_neg_natAbs_of_nonpos (by omega)
      linarith
    have h2 : ((z.natAbs : ℕ) : ℤ) = -z := by
      have hh : z = -((z.natAbs : ℤ)) := Int.eq_neg_natAbs_of_nonpos (by omega)
      linarith
    have h3 : ((z.natAbs : ℕ) : ℤ) = (((z + 1).natAbs : ℕ) : ℤ) + 1 := by omega
    exact_mod_cast h3

/-- `1 + 1/m` written with the absolute values of `m + 1` and `m`. -/
lemma oneAddInvPowEq_frac_abs (m : ℤ) (hm : m ≠ -1) (hm0 : m ≠ 0) :
    (1 + (1 : ℚ) / m) = (((m + 1).natAbs : ℕ) : ℚ) / ((m.natAbs : ℕ) : ℚ) := by
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hbase : (1 + (1 : ℚ) / m) = ((m + 1 : ℤ) : ℚ) / (m : ℚ) := by
    field_simp [hmq]
    simp
  have hcases : (1 ≤ m) ∨ (m ≤ -2) := by omega
  rcases hcases with hmpos | hmneg
  · have hA : (((m + 1).natAbs : ℕ) : ℚ) = ((m + 1 : ℤ) : ℚ) := by
      have hAz : (((m + 1).natAbs : ℕ) : ℤ) = m + 1 := Int.natAbs_of_nonneg (by omega)
      exact congrArg (fun x : ℤ => (x : ℚ)) hAz
    have hB : ((m.natAbs : ℕ) : ℚ) = (m : ℚ) := by
      have hBz : ((m.natAbs : ℕ) : ℤ) = m := Int.natAbs_of_nonneg (by omega)
      exact congrArg (fun x : ℤ => (x : ℚ)) hBz
    calc
      (1 + (1 : ℚ) / m) = ((m + 1 : ℤ) : ℚ) / (m : ℚ) := hbase
      _ = (((m + 1).natAbs : ℕ) : ℚ) / ((m.natAbs : ℕ) : ℚ) := by rw [← hA, ← hB]
  · have hA : (((m + 1).natAbs : ℕ) : ℚ) = -((m + 1 : ℤ) : ℚ) := by
      have hAz : (((m + 1).natAbs : ℕ) : ℤ) = -(m + 1) := by
        have hh : m + 1 = -(((m + 1).natAbs : ℤ)) := Int.eq_neg_natAbs_of_nonpos (by omega)
        linarith
      have hAc := congrArg (fun x : ℤ => (x : ℚ)) hAz
      simpa using hAc
    have hB : ((m.natAbs : ℕ) : ℚ) = -(m : ℚ) := by
      have hBz : ((m.natAbs : ℕ) : ℤ) = -m := by
        have hh : m = -((m.natAbs : ℤ)) := Int.eq_neg_natAbs_of_nonpos (by omega)
        linarith
      have hBc := congrArg (fun x : ℤ => (x : ℚ)) hBz
      simpa using hBc
    have hnum : ((m + 1 : ℤ) : ℚ) = -(((m + 1).natAbs : ℕ) : ℚ) := by linarith
    have hden : (m : ℚ) = -((m.natAbs : ℕ) : ℚ) := by linarith
    calc
      (1 + (1 : ℚ) / m) = ((m + 1 : ℤ) : ℚ) / (m : ℚ) := hbase
      _ = (((m + 1).natAbs : ℕ) : ℚ) / ((m.natAbs : ℕ) : ℚ) := by
        rw [hnum, hden]
        field_simp

/-- `|x| ≤ |2x - 1|` for all integers `x`. -/
lemma oneAddInvPowEq_abs_le (x : ℤ) : |x| ≤ |2 * x - 1| := by
  by_cases hx : 1 ≤ x
  · have h1 : 0 ≤ x := by omega
    have h2 : 0 ≤ 2 * x - 1 := by omega
    rw [abs_of_nonneg h1, abs_of_nonneg h2]
    omega
  · have h1 : x ≤ 0 := by omega
    have h2 : 2 * x - 1 ≤ 0 := by omega
    rw [abs_of_nonpos h1, abs_of_nonpos h2]
    omega

/-- `2m + 1` never vanishes, so its absolute value is at least one. -/
lemma oneAddInvPowEq_abs_ge_one (m : ℤ) : 1 ≤ |2 * m + 1| := by
  have hnz : 2 * m + 1 ≠ 0 := by
    intro h
    have h2 : 2 * m = -1 := by omega
    have hd : (2 : ℤ) ∣ 2 * m := dvd_mul_right 2 m
    rw [h2] at hd
    norm_num at hd
  have hnz2 : |2 * m + 1| ≠ 0 := by
    intro hz
    exact hnz (abs_eq_zero.mp hz)
  have hpos : 0 ≤ |2 * m + 1| := abs_nonneg (2 * m + 1)
  omega


/-! ## Main lemma -/

/-- If `(1 + 1/m)^b (1 + 1/n)^c = 1` with `m, n ∉ {-1, 0}`, `m ≠ n` and
`10^6 * |m - n| < |n|`, then `b = 0` and `c = 0`. -/
lemma oneAddInvPowEq (m n b c : ℤ) (hm : m ≠ -1) (hm0 : m ≠ 0) (hn : n ≠ -1)
    (hn0 : n ≠ 0) (hne : m ≠ n) (hgap : 10 ^ 6 * |m - n| < |n|)
    (hpow : ((1 + (1 : ℚ) / m) ^ b) * ((1 + (1 : ℚ) / n) ^ c) = 1) :
    b = 0 ∧ c = 0 := by
  let A : ℕ := (m + 1).natAbs
  let B : ℕ := m.natAbs
  let C : ℕ := (n + 1).natAbs
  let D : ℕ := n.natAbs
  let X : ℚ := 1 + (1 : ℚ) / m
  let Y : ℚ := 1 + (1 : ℚ) / n
  have hpowX : X ^ b * Y ^ c = 1 := by
    simpa [X, Y] using hpow
  have hX : X = (A : ℚ) / (B : ℚ) := by
    simpa [X, A, B] using (oneAddInvPowEq_frac_abs m hm hm0)
  have hY : Y = (C : ℚ) / (D : ℚ) := by
    simpa [Y, C, D] using (oneAddInvPowEq_frac_abs n hn hn0)
  have hA : A ≠ 0 := by
    intro hz
    dsimp [A] at hz
    have hz' : m + 1 = 0 := Int.natAbs_eq_zero.mp hz
    exact hm (by omega)
  have hB : B ≠ 0 := by
    intro hz
    dsimp [B] at hz
    exact hm0 (Int.natAbs_eq_zero.mp hz)
  have hC : C ≠ 0 := by
    intro hz
    dsimp [C] at hz
    have hz' : n + 1 = 0 := Int.natAbs_eq_zero.mp hz
    exact hn (by omega)
  have hD : D ≠ 0 := by
    intro hz
    dsimp [D] at hz
    exact hn0 (Int.natAbs_eq_zero.mp hz)
  have hAB : A = B + 1 ∨ B = A + 1 := by
    dsimp [A, B]
    exact oneAddInvPowEq_natAbs_succ m
  have hCD : C = D + 1 ∨ D = C + 1 := by
    dsimp [C, D]
    exact oneAddInvPowEq_natAbs_succ n
  by_cases hb : b = 0
  · by_cases hc : c = 0
    · exact ⟨hb, hc⟩
    · exfalso
      have hYc0 : Y ^ c = 1 := by simpa [hb] using hpowX
      have hYc : ((C : ℚ) / (D : ℚ)) ^ c = 1 := by simpa [Y, hY] using hYc0
      have hc0 : c = 0 := oneAddInvPowEq_zpow_eq_one hD hCD c hYc
      exact hc hc0
  · by_cases hc : c = 0
    · exfalso
      have hXb0 : X ^ b = 1 := by simpa [hc] using hpowX
      have hXb : ((A : ℚ) / (B : ℚ)) ^ b = 1 := by simpa [X, hX] using hXb0
      have hb0 : b = 0 := oneAddInvPowEq_zpow_eq_one hB hAB b hXb
      exact hb hb0
    · exfalso
      have hcore_in : ((A : ℚ) / (B : ℚ)) ^ b * ((C : ℚ) / (D : ℚ)) ^ c = 1 := by
        simpa [X, Y, hX, hY] using hpowX
      have hd := oneAddInvPowEq_core hA hB hC hD hAB hCD b c hb hc hcore_in
      rcases hd with hd1 | hd2
      · have hXY : X = Y := by simpa [X, Y, hX, hY] using hd1
        have hmn : m = n := by
          have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
          have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
          dsimp [X, Y] at hXY
          field_simp [hmq, hnq] at hXY
          have hz : (m + 1) * n = m * (n + 1) := by exact_mod_cast hXY
          nlinarith
        exact hne hmn
      · have hXY1 : X * Y = 1 := by simpa [X, Y, hX, hY] using hd2
        have hmn0 : m + n + 1 = 0 := by
          have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
          have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
          dsimp [X, Y] at hXY1
          field_simp [hmq, hnq] at hXY1
          have hz : (m + 1) * (n + 1) = m * n := by exact_mod_cast hXY1
          nlinarith
        have hn : n = -(m + 1) := by omega
        have hgap0 : 10 ^ 6 * |m - n| < |m + 1| := by
          rw [hn] at hgap ⊢
          rw [abs_neg] at hgap
          exact hgap
        have hmm : m - (-(m + 1)) = 2 * m + 1 := by ring
        have h1 : 10 ^ 6 * |2 * m + 1| < |m + 1| := by
          rw [hn] at hgap0
          rw [hmm] at hgap0
          exact hgap0
        have hle : |m + 1| ≤ |2 * m + 1| := by
          have hx : |m + 1| ≤ |2 * (m + 1) - 1| := oneAddInvPowEq_abs_le (m + 1)
          have harg : 2 * (m + 1) - 1 = 2 * m + 1 := by ring
          rw [harg] at hx
          exact hx
        have hgt : 1 ≤ |2 * m + 1| := oneAddInvPowEq_abs_ge_one m
        omega

end Commons.Data.Int
