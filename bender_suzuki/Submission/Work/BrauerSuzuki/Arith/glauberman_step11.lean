import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Arith

private lemma odd_ne_zero {n : ℤ} (h : Odd n) : n ≠ 0 := by rintro rfl; simp at h

-- ===== core =====
private lemma odd_of_not_two_dvd (w : ℤ) (hw : ¬ 2 ∣ w) : Odd w := by
  rw [← even_iff_two_dvd] at hw
  exact Int.not_even_iff_odd.mp hw

private lemma odd_cast {n : ℤ} (h : Odd n) : (n : ZMod 2) = 1 := by
  obtain ⟨m, rfl⟩ := h; push_cast; rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]

private lemma pm1_cast {n : ℤ} (h : n = 1 ∨ n = -1) : (n : ZMod 2) = 1 := by
  rcases h with h | h
  · rw [h]; decide
  · rw [h]; decide

private lemma pm1_cast4 {n : ℤ} (h : n = 1 ∨ n = -1) :
    (n : ZMod 4) = 1 ∨ (n : ZMod 4) = -1 := by
  rcases h with h | h
  · rw [h]; simp
  · rw [h]; simp

private lemma term_cast2 (ε w a b : ℤ) (hε : ε = 1 ∨ ε = -1) (ha : Odd a) (hb : Odd b) :
    ((ε * w^2 * a * b : ℤ) : ZMod 2) = (w : ZMod 2) := by
  have hs : ∀ c : ZMod 2, c^2 = c := by decide
  push_cast
  rw [pm1_cast hε, odd_cast ha, odd_cast hb, hs]
  ring

private lemma zmod2_extract : ∀ f : Fin 3 → ZMod 2, f 0 + f 1 + f 2 = 0 → (∃ i, f i ≠ 0) →
    ∃ a, f a = 0 ∧ ∀ b, b ≠ a → f b ≠ 0 := by decide

private lemma sum_cast2 (ε x w : Fin 3 → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hx : ∀ i, Odd (x i)) :
    (((ε 0 * w 0^2 * x 1 * x 2 + ε 1 * w 1^2 * x 0 * x 2 + ε 2 * w 2^2 * x 0 * x 1 : ℤ)) : ZMod 2)
      = (w 0 : ZMod 2) + (w 1 : ZMod 2) + (w 2 : ZMod 2) := by
  rw [Int.cast_add, Int.cast_add]
  rw [term_cast2 _ _ _ _ (hε 0) (hx 1) (hx 2), term_cast2 _ _ _ _ (hε 1) (hx 0) (hx 2),
      term_cast2 _ _ _ _ (hε 2) (hx 0) (hx 1)]

private lemma odd_sq_zmod4 (w : ℤ) (hw : Odd w) : (w : ZMod 4)^2 = 1 := by
  obtain ⟨t, rfl⟩ := hw
  push_cast
  ring_nf
  simp [show (4 : ZMod 4) = 0 by decide]

private lemma term_cast4_even (ε w a b : ℤ) (hw : 2 ∣ w) :
    ((ε * w^2 * a * b : ℤ) : ZMod 4) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨t, rfl⟩ := hw
  exact ⟨ε * t^2 * a * b, by ring⟩

private lemma term_cast4_odd (ε w a b : ℤ) (hw : ¬ 2 ∣ w) :
    ((ε * w^2 * a * b : ℤ) : ZMod 4) = (ε : ZMod 4) * (a : ZMod 4) * (b : ZMod 4) := by
  have hwodd := odd_of_not_two_dvd w hw
  obtain ⟨t, rfl⟩ := hwodd
  push_cast
  ring_nf
  simp [show (4 : ZMod 4) = 0 by decide]

private lemma zmod4_key (e0 e1 e2 x0 x1 x2 : ZMod 4)
    (he0 : e0 = 1 ∨ e0 = -1) (he1 : e1 = 1 ∨ e1 = -1) (he2 : e2 = 1 ∨ e2 = -1)
    (hx0sq : x0 * x0 = 1)
    (hmod : e1 * x0 * x2 + e2 * x0 * x1 = 0)
    (h5 : 1 + e0 * x0 + e1 * x1 + e2 * x2 = 0) :
    x0 + e0 = 0 := by
  have hmod' : x0 * (e1 * x2 + e2 * x1) = 0 := by linear_combination hmod
  have he12 : e1 * e2 * (e1 * x2 + e2 * x1) = e1 * x1 + e2 * x2 := by
    rcases he1 with h|h <;> rcases he2 with h'|h' <;> rw [h, h'] <;> ring
  have hA : x0 * (e1 * x1 + e2 * x2) = 0 := by
    rw [← he12]
    rw [show x0 * (e1 * e2 * (e1 * x2 + e2 * x1))
          = e1 * e2 * (x0 * (e1 * x2 + e2 * x1)) by ring]
    rw [hmod', mul_zero]
  have hB : e1 * x1 + e2 * x2 = -(1 + e0 * x0) := by linear_combination h5
  have hC : x0 * (1 + e0 * x0) = 0 := by
    have := hA; rw [hB] at this; linear_combination -this
  have hD : 1 + e0 * x0 = 0 := by
    have hh : x0 * (x0 * (1 + e0 * x0)) = 0 := by rw [hC, mul_zero]
    rw [← mul_assoc, hx0sq, one_mul] at hh
    exact hh
  calc x0 + e0 = e0 * (1 + e0 * x0) := by
        rcases he0 with h|h <;> rw [h] <;> ring
    _ = 0 := by rw [hD, mul_zero]

theorem glauberman_step11_core (ε x w : Fin 3 → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hx : ∀ i, Odd (x i))
    (hodd : ∃ i, ¬ (2 : ℤ) ∣ w i)
    (h5b1 : 1 + ∑ i, ε i * x i = 0)
    (hW : ε 0 * w 0 ^ 2 * x 1 * x 2 + ε 1 * w 1 ^ 2 * x 0 * x 2
            + ε 2 * w 2 ^ 2 * x 0 * x 1 = 0) :
    ∃ i, (2 : ℤ) ∣ w i ∧ (4 : ℤ) ∣ (x i + ε i) := by
  have hmod2 : (w 0 : ZMod 2) + (w 1 : ZMod 2) + (w 2 : ZMod 2) = 0 := by
    have hcast : (((ε 0 * w 0^2 * x 1 * x 2 + ε 1 * w 1^2 * x 0 * x 2
        + ε 2 * w 2^2 * x 0 * x 1 : ℤ)) : ZMod 2) = 0 := by rw [hW]; simp
    rwa [sum_cast2 ε x w hε hx] at hcast
  have hne : ∃ i, (w i : ZMod 2) ≠ 0 := by
    obtain ⟨i, hi⟩ := hodd
    exact ⟨i, fun h => hi ((ZMod.intCast_zmod_eq_zero_iff_dvd (w i) 2).mp h)⟩
  obtain ⟨a, ha0, hane⟩ := zmod2_extract (fun i => (w i : ZMod 2)) hmod2 hne
  have hdvd_a : (2 : ℤ) ∣ w a := (ZMod.intCast_zmod_eq_zero_iff_dvd (w a) 2).mp ha0
  have hndvd : ∀ b, b ≠ a → ¬ (2 : ℤ) ∣ w b := by
    intro b hb h
    exact hane b hb ((ZMod.intCast_zmod_eq_zero_iff_dvd (w b) 2).mpr h)
  have h5b1' : 1 + ε 0 * x 0 + ε 1 * x 1 + ε 2 * x 2 = 0 := by
    have h := h5b1; rw [Fin.sum_univ_three] at h; linarith
  refine ⟨a, hdvd_a, ?_⟩
  fin_cases a
  · have h1 : ¬ (2 : ℤ) ∣ w 1 := hndvd 1 (by decide)
    have h2 : ¬ (2 : ℤ) ∣ w 2 := hndvd 2 (by decide)
    have h4z : (((ε 0 * w 0^2 * x 1 * x 2 + ε 1 * w 1^2 * x 0 * x 2
        + ε 2 * w 2^2 * x 0 * x 1 : ℤ)) : ZMod 4) = 0 := by rw [hW]; simp
    rw [Int.cast_add, Int.cast_add] at h4z
    rw [term_cast4_even (ε 0) (w 0) (x 1) (x 2) hdvd_a,
        term_cast4_odd (ε 1) (w 1) (x 0) (x 2) h1,
        term_cast4_odd (ε 2) (w 2) (x 0) (x 1) h2] at h4z
    simp only [zero_add] at h4z
    change (4 : ℤ) ∣ x 0 + ε 0
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (x 0 + ε 0) 4).mp ?_
    have h5c : ((1 + ε 0 * x 0 + ε 1 * x 1 + ε 2 * x 2 : ℤ) : ZMod 4) = 0 := by
      rw [h5b1']; simp
    push_cast at h5c
    have key := zmod4_key (ε 0 : ZMod 4) (ε 1 : ZMod 4) (ε 2 : ZMod 4)
        (x 0 : ZMod 4) (x 1 : ZMod 4) (x 2 : ZMod 4)
        (pm1_cast4 (hε 0)) (pm1_cast4 (hε 1)) (pm1_cast4 (hε 2))
        (by rw [← pow_two]; exact odd_sq_zmod4 (x 0) (hx 0))
        (by linear_combination h4z) (by linear_combination h5c)
    push_cast
    exact key
  · have h0 : ¬ (2 : ℤ) ∣ w 0 := hndvd 0 (by decide)
    have h2 : ¬ (2 : ℤ) ∣ w 2 := hndvd 2 (by decide)
    have h4z : (((ε 0 * w 0^2 * x 1 * x 2 + ε 1 * w 1^2 * x 0 * x 2
        + ε 2 * w 2^2 * x 0 * x 1 : ℤ)) : ZMod 4) = 0 := by rw [hW]; simp
    rw [Int.cast_add, Int.cast_add] at h4z
    rw [term_cast4_odd (ε 0) (w 0) (x 1) (x 2) h0,
        term_cast4_even (ε 1) (w 1) (x 0) (x 2) hdvd_a,
        term_cast4_odd (ε 2) (w 2) (x 0) (x 1) h2] at h4z
    simp only [add_zero] at h4z
    change (4 : ℤ) ∣ x 1 + ε 1
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (x 1 + ε 1) 4).mp ?_
    have h5c : ((1 + ε 0 * x 0 + ε 1 * x 1 + ε 2 * x 2 : ℤ) : ZMod 4) = 0 := by
      rw [h5b1']; simp
    push_cast at h5c
    have key := zmod4_key (ε 1 : ZMod 4) (ε 0 : ZMod 4) (ε 2 : ZMod 4)
        (x 1 : ZMod 4) (x 0 : ZMod 4) (x 2 : ZMod 4)
        (pm1_cast4 (hε 1)) (pm1_cast4 (hε 0)) (pm1_cast4 (hε 2))
        (by rw [← pow_two]; exact odd_sq_zmod4 (x 1) (hx 1))
        (by linear_combination h4z) (by linear_combination h5c)
    push_cast
    exact key
  · have h0 : ¬ (2 : ℤ) ∣ w 0 := hndvd 0 (by decide)
    have h1 : ¬ (2 : ℤ) ∣ w 1 := hndvd 1 (by decide)
    have h4z : (((ε 0 * w 0^2 * x 1 * x 2 + ε 1 * w 1^2 * x 0 * x 2
        + ε 2 * w 2^2 * x 0 * x 1 : ℤ)) : ZMod 4) = 0 := by rw [hW]; simp
    rw [Int.cast_add, Int.cast_add] at h4z
    rw [term_cast4_odd (ε 0) (w 0) (x 1) (x 2) h0,
        term_cast4_odd (ε 1) (w 1) (x 0) (x 2) h1,
        term_cast4_even (ε 2) (w 2) (x 0) (x 1) hdvd_a] at h4z
    simp only [add_zero] at h4z
    change (4 : ℤ) ∣ x 2 + ε 2
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (x 2 + ε 2) 4).mp ?_
    have h5c : ((1 + ε 0 * x 0 + ε 1 * x 1 + ε 2 * x 2 : ℤ) : ZMod 4) = 0 := by
      rw [h5b1']; simp
    push_cast at h5c
    have key := zmod4_key (ε 2 : ZMod 4) (ε 0 : ZMod 4) (ε 1 : ZMod 4)
        (x 2 : ZMod 4) (x 0 : ZMod 4) (x 1 : ZMod 4)
        (pm1_cast4 (hε 2)) (pm1_cast4 (hε 0)) (pm1_cast4 (hε 1))
        (by rw [← pow_two]; exact odd_sq_zmod4 (x 2) (hx 2))
        (by linear_combination h4z) (by linear_combination h5c)
    push_cast
    exact key

-- ===== decomposition =====
private lemma exists_common_two_pow (z : Fin 3 → ℤ)
    (hpos : ∀ i, 0 < z i) (h4 : ∀ i, (4 : ℤ) ∣ z i) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ w : Fin 3 → ℤ,
      (∀ i, z i = (2 : ℤ) ^ k * w i) ∧ (∃ i, ¬ (2 : ℤ) ∣ w i) := by
  set P : ℕ → Prop := fun n => ∀ i, (2 : ℤ) ^ n ∣ z i with hPdef
  have : DecidablePred P := fun n => inferInstance
  have hB : 2 ≤ (z 0).natAbs := by
    have hle : (4 : ℤ) ≤ z 0 := Int.le_of_dvd (hpos 0) (h4 0)
    have hcast : (4 : ℤ) ≤ (((z 0).natAbs : ℕ) : ℤ) := by
      rwa [Int.natAbs_of_nonneg (le_of_lt (hpos 0))]
    have := Nat.cast_le.mp hcast
    omega
  have hP2 : P 2 := by
    intro i; have := h4 i; simpa [hPdef] using this
  have hPbound : ∀ n, P n → n ≤ (z 0).natAbs := by
    intro n hn
    have hle : (2 : ℤ) ^ n ≤ z 0 := Int.le_of_dvd (hpos 0) (hn 0)
    have hcast : ((2 ^ n : ℕ) : ℤ) ≤ (((z 0).natAbs : ℕ) : ℤ) := by
      rw [Int.natAbs_of_nonneg (le_of_lt (hpos 0))]
      push_cast
      exact hle
    have := Nat.cast_le.mp hcast
    have hn2 : n ≤ 2 ^ n := le_of_lt (Nat.lt_two_pow_self (n := n))
    omega
  set k : ℕ := Nat.findGreatest P (z 0).natAbs with hkdef
  have hPk : P k := Nat.findGreatest_spec hB hP2
  have hk2 : 2 ≤ k := Nat.le_findGreatest hB hP2
  have hmax : ¬ P (k + 1) := by
    intro hc
    have hle : k + 1 ≤ k := Nat.le_findGreatest (hPbound (k+1) hc) hc
    omega
  choose w hw using hPk
  obtain ⟨i0, hi0⟩ := not_forall.mp hmax
  refine ⟨k, hk2, w, fun i => hw i, ⟨i0, ?_⟩⟩
  intro h2
  obtain ⟨t, ht⟩ := h2
  apply hi0
  refine ⟨t, ?_⟩
  rw [hw i0, ht, pow_succ]
  ring

-- ===== main =====
private lemma integer_eq_of_rat (ε x z : Fin 3 → ℤ) (hx : ∀ i, Odd (x i))
    (h5b3 : ∑ i, (ε i : ℚ) * (z i : ℚ) ^ 2 / (x i : ℚ) = 0) :
    ε 0 * z 0 ^ 2 * x 1 * x 2 + ε 1 * z 1 ^ 2 * x 0 * x 2
      + ε 2 * z 2 ^ 2 * x 0 * x 1 = 0 := by
  rw [Fin.sum_univ_three] at h5b3
  have h0 : (x 0 : ℚ) ≠ 0 := by exact_mod_cast (odd_ne_zero (hx 0))
  have h1 : (x 1 : ℚ) ≠ 0 := by exact_mod_cast (odd_ne_zero (hx 1))
  have h2 : (x 2 : ℚ) ≠ 0 := by exact_mod_cast (odd_ne_zero (hx 2))
  have hkey : (ε 0 : ℚ) * (z 0 : ℚ)^2 * (x 1 : ℚ) * (x 2 : ℚ)
      + (ε 1 : ℚ) * (z 1 : ℚ)^2 * (x 0 : ℚ) * (x 2 : ℚ)
      + (ε 2 : ℚ) * (z 2 : ℚ)^2 * (x 0 : ℚ) * (x 1 : ℚ) = 0 := by
    field_simp at h5b3 ⊢
    linarith [h5b3]
  exact_mod_cast hkey

theorem glauberman_step11 (ε x z : Fin 3 → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hx : ∀ i, Odd (x i))
    (hzpos : ∀ i, 0 < z i)
    (hz : ∀ i, (4 : ℤ) ∣ z i)
    (h5b1 : 1 + ∑ i, ε i * x i = 0)
    (h5b3 : ∑ i, (ε i : ℚ) * (z i : ℚ) ^ 2 / (x i : ℚ) = 0) :
    ∃ i, (8 : ℤ) ∣ z i ∧ (4 : ℤ) ∣ (x i + ε i) := by
  have hZ := integer_eq_of_rat ε x z hx h5b3
  obtain ⟨k, hk2, w, hw, hodd⟩ := exists_common_two_pow z hzpos hz
  have hsq : ((2 : ℤ)^k)^2 = (4 : ℤ)^k := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hW : ε 0 * w 0 ^ 2 * x 1 * x 2 + ε 1 * w 1 ^ 2 * x 0 * x 2
      + ε 2 * w 2 ^ 2 * x 0 * x 1 = 0 := by
    have e1 : ((2:ℤ)^k * w 0)^2 = (4:ℤ)^k * w 0^2 := by rw [mul_pow, hsq]
    have e2 : ((2:ℤ)^k * w 1)^2 = (4:ℤ)^k * w 1^2 := by rw [mul_pow, hsq]
    have e3 : ((2:ℤ)^k * w 2)^2 = (4:ℤ)^k * w 2^2 := by rw [mul_pow, hsq]
    have hZ' : (4:ℤ)^k * (ε 0 * w 0^2 * x 1 * x 2 + ε 1 * w 1^2 * x 0 * x 2
        + ε 2 * w 2^2 * x 0 * x 1) = 0 := by
      rw [← hZ]
      rw [hw 0, hw 1, hw 2, e1, e2, e3]
      ring
    exact (mul_eq_zero.mp hZ').resolve_left (pow_ne_zero k (by norm_num))
  obtain ⟨i, hwi, hxi⟩ := glauberman_step11_core ε x w hε hx hodd h5b1 hW
  refine ⟨i, ?_, hxi⟩
  obtain ⟨t, ht⟩ := hwi
  refine ⟨2^(k-2) * t, ?_⟩
  rw [hw i, ht]
  have hk : (2:ℤ)^k = (2:ℤ)^(k-2) * 4 := by
    rw [show k = (k - 2) + 2 by omega, pow_add]; norm_num
  rw [hk]; ring

end Work.BrauerSuzuki.Arith
