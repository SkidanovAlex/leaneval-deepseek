import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddData
import Submission.Work.ZassenhausSuzuki.Odd.endgame_card_le_three
import Submission.Work.ZassenhausSuzuki.Odd.endgame_sum_T
import Submission.Work.ZassenhausSuzuki.Odd.endgame_sum_inv_lt
import Submission.Work.ZassenhausSuzuki.Odd.endgame_B_three
import Submission.Work.ZassenhausSuzuki.Odd.quad_descent
import Submission.Work.ZassenhausSuzuki.Odd.endgame_numeric

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.Odd

set_option maxHeartbeats 3000000

/-- Coprimality with `q * (q-1)` upgrades to coprimality with `q² * (q-1)`. -/
private lemma classify_coprime_sq_mul {q a : ℕ} (h : Nat.Coprime a (q * (q - 1))) :
    Nat.Coprime a (q ^ 2 * (q - 1)) :=
  ((h.coprime_dvd_right (dvd_mul_right q (q - 1))).pow_right 2).mul_right
    (h.coprime_dvd_right (dvd_mul_left (q - 1) q))

/-- If `a ∣ q²(q-1)(q²+1)` and `a` is coprime to `q(q-1)` then `a ∣ q²+1`. -/
private lemma classify_dvd_qsq_add_one {q a : ℕ} (hcop : Nat.Coprime a (q * (q - 1)))
    (hdiv : a ∣ q ^ 2 * (q - 1) * (q ^ 2 + 1)) : a ∣ q ^ 2 + 1 :=
  (classify_coprime_sq_mul hcop).dvd_of_dvd_mul_left hdiv

/-- `q + 1 ∣ q² + 1` forces `q ≤ 1`. -/
private lemma classify_dvd_qq_add_one {q : ℕ} (h : q + 1 ∣ q ^ 2 + 1) : q ≤ 1 := by
  have h3 : q + 1 ∣ q ^ 2 + q := ⟨q, by ring⟩
  have h4 : q + 1 ∣ q ^ 2 + q - (q ^ 2 + 1) := Nat.dvd_sub h3 h
  have heq : q ^ 2 + q - (q ^ 2 + 1) = q - 1 := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0; norm_num
    · omega
  rw [heq] at h4
  have := Nat.eq_zero_of_dvd_of_lt h4 (by omega : q - 1 < q + 1)
  omega

/-- `2q + 1 ∣ q² + 1` forces `q ≤ 2`. -/
private lemma classify_dvd_twoq_add_one {q : ℕ} (h : 2 * q + 1 ∣ q ^ 2 + 1) : q ≤ 2 := by
  by_cases hq : q ≤ 2
  · exact hq
  · exfalso
    have hq3 : 3 ≤ q := by omega
    have h4 : 2 * q + 1 ∣ 4 * (q ^ 2 + 1) := by
      have hmul := h.mul_right 4
      rwa [show (q ^ 2 + 1) * 4 = 4 * (q ^ 2 + 1) by ring] at hmul
    have h5 : 2 * q + 1 ∣ (2 * q + 1) ^ 2 := ⟨2 * q + 1, by ring⟩
    have h6 : 2 * q + 1 ∣ (2 * q + 1) ^ 2 - 4 * (q ^ 2 + 1) := Nat.dvd_sub h5 h4
    have he1 : (2 * q + 1) ^ 2 - 4 * (q ^ 2 + 1) = 4 * q - 3 := by
      have e : (2 * q + 1) ^ 2 = 4 * q ^ 2 + 4 * q + 1 := by ring
      rw [e]
      have e2 : 4 * (q ^ 2 + 1) = 4 * q ^ 2 + 4 := by ring
      rw [e2]
      omega
    rw [he1] at h6
    have h7 : 2 * q + 1 ∣ 4 * q + 2 := ⟨2, by ring⟩
    have h8 : 2 * q + 1 ∣ 4 * q + 2 - (4 * q - 3) := Nat.dvd_sub h7 h6
    have he2 : 4 * q + 2 - (4 * q - 3) = 5 := by omega
    rw [he2] at h8
    have := Nat.le_of_dvd (by norm_num : 0 < 5) h8
    omega

theorem endgame_classify {q : ℕ} {V : Finset ℕ} {m k : ℕ → ℕ}
    (hq : 1 ≤ q)
    (hV : ∀ a ∈ V, 5 ≤ a)
    (hk : ∀ a ∈ V, k a = 2 ∨ k a = 4)
    (hm : ∀ a ∈ V, m a * a * k a = q ^ 2 * (q - 1) * (q ^ 2 + 1))
    (hsum1 : ∑ a ∈ V, (m a : ℚ) * (a - 1)
        = (q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℚ) - (q : ℚ) ^ 4)
    (hsum2 : ∑ a ∈ V, (m a : ℚ) * a * (a - 1)
        = (q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℚ) * (q - 1))
    (hD : q - 1 ∈ V) (hDk : k (q - 1) = 2)
    (hcop : ∀ a ∈ V, a ≠ q - 1 → Nat.Coprime a (q * (q - 1)))
    (hcop2 : ∀ a ∈ V, a ≠ q - 1 → ∀ b ∈ V, b ≠ q - 1 → a ≠ b → Nat.Coprime a b) :
    V.card = 3 ∧ ∃ a b : ℕ, a ≠ b ∧ V = {q - 1, a, b} ∧ k a = 4 ∧ k b = 4 ∧
      a + b = 2 * q + 2 ∧ a * b = q ^ 2 + 1 := by
  have hq6 : 6 ≤ q := by have := hV (q - 1) hD; omega
  have hNpos : 0 < q ^ 2 * (q - 1) * (q ^ 2 + 1) := by
    have h1 : 0 < q ^ 2 := pow_pos (by omega : 0 < q) 2
    have h2 : 0 < q - 1 := by omega
    have h3 : 0 < q ^ 2 + 1 := by positivity
    exact mul_pos (mul_pos h1 h2) h3
  have hsum1_0 : ∑ a ∈ V, (m a : ℚ) * (a - 1)
      = (q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℚ) - (q : ℚ) ^ 4 - ((0 : ℕ) : ℚ) := by
    simpa using hsum1
  have hcard : V.card ≤ 3 :=
    endgame_card_le_three (B := 0) hq hV hk hm hsum1_0 hD hDk
  have hT : ∑ a ∈ V, ((a : ℚ) - 1) / (k a : ℚ) = (q : ℚ) - 1 :=
    endgame_sum_T hNpos hV hk hm hsum2
  have hInv : ∑ a ∈ V, (1 : ℚ) / (k a : ℚ) < 5 / 4 :=
    endgame_sum_inv_lt (B := 0) hNpos hV hk hm hsum1_0
  have hpos : 0 < V.card := Finset.card_pos.mpr ⟨q - 1, hD⟩
  have hcastq : (((q - 1 : ℕ) : ℚ) - 1) = (q : ℚ) - 2 := by
    rw [Nat.cast_sub hq]; push_cast; ring
  rcases (by omega : V.card = 1 ∨ V.card = 2 ∨ V.card = 3) with hc1 | hc2 | hc3
  · -- ## `|V| = 1`
    exfalso
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc1
    have hxe : x = q - 1 := by
      have hmem : q - 1 ∈ ({x} : Finset ℕ) := hx ▸ hD
      rw [Finset.mem_singleton] at hmem
      exact hmem.symm
    subst hxe
    rw [hx, Finset.sum_singleton, hDk] at hT
    simp only [Nat.cast_ofNat] at hT
    rw [hcastq] at hT
    have hq' : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
    linarith
  · -- ## `|V| = 2`
    exfalso
    have hcardEr : (V.erase (q - 1)).card = 1 := by
      rw [Finset.card_erase_of_mem hD]; omega
    obtain ⟨a, ha_eq⟩ := Finset.card_eq_one.mp hcardEr
    have hVeq : V = {q - 1, a} := by
      rw [← Finset.insert_erase hD, ha_eq]
    have ha_er : a ∈ V.erase (q - 1) := by
      rw [ha_eq]; exact Finset.mem_singleton_self a
    have haV : a ∈ V := (Finset.mem_erase.mp ha_er).2
    have ha_ne : a ≠ q - 1 := (Finset.mem_erase.mp ha_er).1
    have hs2 : ∑ x ∈ V, ((x : ℚ) - 1) / (k x : ℚ)
        = (((q - 1 : ℕ) : ℚ) - 1) / (k (q - 1) : ℚ) + ((a : ℚ) - 1) / (k a : ℚ) := by
      rw [hVeq, Finset.sum_insert (by
        simp only [Finset.mem_singleton]; exact fun h => ha_ne h.symm),
        Finset.sum_singleton]
    rw [hs2, hDk] at hT
    simp only [Nat.cast_ofNat] at hT
    rw [hcastq] at hT
    have hTa : ((a : ℚ) - 1) / (k a : ℚ) = (q : ℚ) / 2 := by linarith
    have hadiv : a ∣ q ^ 2 + 1 := by
      refine classify_dvd_qsq_add_one (hcop a haV ha_ne) ?_
      exact ⟨m a * k a, by have := hm a haV; rw [← this]; ring⟩
    rcases hk a haV with hka | hka
    · rw [hka] at hTa
      simp only [Nat.cast_ofNat] at hTa
      have haeq : a = q + 1 := by
        have h3 : (a : ℚ) = ((q + 1 : ℕ) : ℚ) := by
          push_cast
          linarith
        exact_mod_cast h3
      rw [haeq] at hadiv
      have := classify_dvd_qq_add_one hadiv
      omega
    · rw [hka] at hTa
      simp only [Nat.cast_ofNat] at hTa
      have haeq : a = 2 * q + 1 := by
        have h3 : (a : ℚ) = ((2 * q + 1 : ℕ) : ℚ) := by
          push_cast
          linarith
        exact_mod_cast h3
      rw [haeq] at hadiv
      have := classify_dvd_twoq_add_one hadiv
      omega
  · -- ## `|V| = 3`
    have hcardEr : (V.erase (q - 1)).card = 2 := by
      rw [Finset.card_erase_of_mem hD]; omega
    obtain ⟨a, b, hab, hab_eq⟩ := Finset.card_eq_two.mp hcardEr
    have hVeq : V = {q - 1, a, b} := by
      rw [← Finset.insert_erase hD, hab_eq]
    have ha_er : a ∈ V.erase (q - 1) := by rw [hab_eq]; simp
    have hb_er : b ∈ V.erase (q - 1) := by rw [hab_eq]; simp
    have haV : a ∈ V := (Finset.mem_erase.mp ha_er).2
    have hbV : b ∈ V := (Finset.mem_erase.mp hb_er).2
    have ha_ne : a ≠ q - 1 := (Finset.mem_erase.mp ha_er).1
    have hb_ne : b ≠ q - 1 := (Finset.mem_erase.mp hb_er).1
    have ha5 : 5 ≤ a := hV a haV
    have hb5 : 5 ≤ b := hV b hbV
    have hsInv : ∑ x ∈ V, (1 : ℚ) / (k x : ℚ)
        = (1 : ℚ) / (k (q - 1) : ℚ)
          + ((1 : ℚ) / (k a : ℚ) + (1 : ℚ) / (k b : ℚ)) := by
      rw [hVeq, Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => ha_ne h.symm, fun h => hb_ne h.symm⟩),
          Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hab),
          Finset.sum_singleton]
    have hInv3 : (1 : ℚ) / (k a : ℚ) + (1 : ℚ) / (k b : ℚ) < 3 / 4 := by
      rw [hsInv, hDk] at hInv
      simp only [Nat.cast_ofNat] at hInv
      norm_num at hInv ⊢
      linarith
    have hka4 : k a = 4 := by
      rcases hk a haV with hk2 | hk4
      · exfalso
        rw [hk2] at hInv3
        simp only [Nat.cast_ofNat] at hInv3
        rcases hk b hbV with hk2' | hk4'
        · rw [hk2'] at hInv3; norm_num at hInv3
        · rw [hk4'] at hInv3; norm_num at hInv3
      · exact hk4
    have hkb4 : k b = 4 := by
      rcases hk b hbV with hk2 | hk4
      · exfalso
        rw [hk2, hka4] at hInv3
        norm_num at hInv3
      · exact hk4
    have hsT : ∑ x ∈ V, ((x : ℚ) - 1) / (k x : ℚ)
        = (((q - 1 : ℕ) : ℚ) - 1) / (k (q - 1) : ℚ)
          + (((a : ℚ) - 1) / (k a : ℚ) + ((b : ℚ) - 1) / (k b : ℚ)) := by
      rw [hVeq, Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => ha_ne h.symm, fun h => hb_ne h.symm⟩),
          Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hab),
          Finset.sum_singleton]
    rw [hsT, hDk, hka4, hkb4] at hT
    simp only [Nat.cast_ofNat] at hT
    rw [hcastq] at hT
    have hsum3 : a + b = 2 * q + 2 := by
      have hrat : (a : ℚ) + (b : ℚ) = 2 * (q : ℚ) + 2 := by linarith
      have h1 : ((a + b : ℕ) : ℚ) = ((2 * q + 2 : ℕ) : ℚ) := by push_cast; linarith
      exact_mod_cast h1
    have hadiv : a ∣ q ^ 2 + 1 := by
      refine classify_dvd_qsq_add_one (hcop a haV ha_ne) ?_
      exact ⟨m a * k a, by have := hm a haV; rw [← this]; ring⟩
    have hbdiv : b ∣ q ^ 2 + 1 := by
      refine classify_dvd_qsq_add_one (hcop b hbV hb_ne) ?_
      exact ⟨m b * k b, by have := hm b hbV; rw [← this]; ring⟩
    have habcop : Nat.Coprime a b := hcop2 a haV ha_ne b hbV hb_ne hab
    have habdiv : a * b ∣ q ^ 2 + 1 := habcop.mul_dvd_of_dvd_of_dvd hadiv hbdiv
    set M : ℕ := (q ^ 2 + 1) / (a * b) with hMdef
    have hM : a * b * M = q ^ 2 + 1 := by
      rw [hMdef]
      exact Nat.mul_div_cancel' habdiv
    have hm1 : m (q - 1) * (q - 1) * 2 = q ^ 2 * (q - 1) * (q ^ 2 + 1) := by
      have h := hm (q - 1) hD; rwa [hDk] at h
    have hma : m a * a * 4 = q ^ 2 * (q - 1) * (q ^ 2 + 1) := by
      have h := hm a haV; rwa [hka4] at h
    have hmb : m b * b * 4 = q ^ 2 * (q - 1) * (q ^ 2 + 1) := by
      have h := hm b hbV; rwa [hkb4] at h
    have hs1 : ∑ x ∈ V, (m x : ℚ) * ((x : ℚ) - 1)
        = (m (q - 1) : ℚ) * (((q - 1 : ℕ) : ℚ) - 1)
          + ((m a : ℚ) * ((a : ℚ) - 1) + (m b : ℚ) * ((b : ℚ) - 1)) := by
      rw [hVeq, Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => ha_ne h.symm, fun h => hb_ne h.symm⟩),
          Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hab),
          Finset.sum_singleton]
    have hsum1_3 : (m (q - 1) : ℚ) * (((q - 1 : ℕ) : ℚ) - 1) + (m a : ℚ) * ((a : ℚ) - 1)
        + (m b : ℚ) * ((b : ℚ) - 1)
        = (q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℚ) - (q : ℚ) ^ 4 - ((0 : ℕ) : ℚ) := by
      rw [hs1] at hsum1
      have h0 : ((0 : ℕ) : ℚ) = 0 := by norm_num
      rw [h0]
      linarith [hsum1]
    have hBform := endgame_B_three (q := q) (B := 0) (a := a) (b := b) (M := M) (m := m)
      (by omega) (by omega) (by omega) hm1 hma hmb hsum1_3 hsum3 hM
    have hM1 : M = 1 := by
      have hcne : (q : ℚ) ^ 2 * ((q : ℚ) - 1) * ((q : ℚ) + 1) ≠ 0 := by
        apply mul_ne_zero
        apply mul_ne_zero
        · refine pow_ne_zero 2 ?_
          intro h
          have h' : q = 0 := by exact_mod_cast h
          omega
        · have h1 : (1 : ℚ) < (q : ℚ) := by exact_mod_cast (by omega : 1 < q)
          linarith
        · have h0 : (0 : ℚ) ≤ (q : ℚ) := by positivity
          linarith
      have h2 : (q : ℚ) ^ 2 * ((q : ℚ) - 1) * ((q : ℚ) + 1) * ((M : ℚ) - 1) = 0 := by
        have h := hBform
        have h0 : ((0 : ℕ) : ℚ) = 0 := by norm_num
        rw [h0] at h
        linarith [h]
      have hone : (M : ℚ) - 1 = 0 := (mul_eq_zero.mp h2).resolve_left hcne
      have : (M : ℚ) = 1 := by linarith
      exact_mod_cast this
    have hab_eq : a * b = q ^ 2 + 1 := by
      rw [hM1] at hM
      simpa using hM
    exact ⟨hc3, a, b, hab, hVeq, hka4, hkb4, hsum3, hab_eq⟩

end Work.ZassenhausSuzuki.Odd
