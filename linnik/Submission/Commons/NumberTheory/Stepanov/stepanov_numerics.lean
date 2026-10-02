import Mathlib
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.Stepanov

theorem stepanov_numerics (e d : ℕ) (he : 2 ≤ e) (hd : 1 ≤ d) (D : ℕ) (hD : D ≤ d)
    (q : ℕ) (hq : (4 * e * (d + 1) + 2 * e ^ 3 * (d + 1) + 4) ^ 2 ≤ q) :
    1 ≤ Nat.sqrt q ∧ 2 * e ≤ Nat.sqrt q ∧
      Nat.sqrt q ≤ (q - 1) / e ∧
      Nat.sqrt q / e + d + 3 < q ∧
      e * (Nat.sqrt q * Nat.sqrt q / (2 * e) + 1) + e ^ 3 * (D + 1) < q ∧
      Nat.sqrt q * ((Nat.sqrt q * Nat.sqrt q / (2 * e) + 1) + (Nat.sqrt q / e + d + 3) + 1)
        + D * (Nat.sqrt q * (Nat.sqrt q - 1) / 2)
        < e * (((Nat.sqrt q * Nat.sqrt q / (2 * e) + 1) + 1) * ((Nat.sqrt q / e + d + 3) + 1)) := by
  set s := Nat.sqrt q with hs
  set A := s * s / (2 * e) with hAdef
  set B := s / e + d + 3 with hBdef
  set C := s * (s - 1) / 2 with hCdef
  have hM : 4 * e * (d + 1) + 2 * e ^ 3 * (d + 1) + 4 ≤ s := by
    rw [hs]
    exact Nat.le_sqrt.2 (by simpa [pow_two] using hq)
  have hs2 : s * s ≤ q := by
    rw [hs]; simpa [pow_two] using Nat.sqrt_le' q
  have hM2e : 2 * e ≤ 4 * e * (d + 1) + 2 * e ^ 3 * (d + 1) + 4 := by
    have h2 : 2 * e ≤ 4 * e * (d + 1) := by
      have h3 : 2 ≤ 4 * (d + 1) := by omega
      calc 2 * e = e * 2 := by ring
        _ ≤ e * (4 * (d + 1)) := Nat.mul_le_mul_left e h3
        _ = 4 * e * (d + 1) := by ring
    omega
  have hs2e : 2 * e ≤ s := le_trans hM2e hM
  have hs1 : 1 ≤ s := by omega
  have hs_e1 : e + 1 ≤ s := by omega
  have hMd4 : d + 4 ≤ 4 * e * (d + 1) + 2 * e ^ 3 * (d + 1) + 4 := by
    have h2 : d + 4 ≤ 8 * (d + 1) := by omega
    have h3 : 8 * (d + 1) ≤ 4 * e * (d + 1) := by
      calc 8 * (d + 1) = (4 * 2) * (d + 1) := by ring
        _ ≤ (4 * e) * (d + 1) := Nat.mul_le_mul_right (d+1) (by omega)
        _ = 4 * e * (d + 1) := by ring
    omega
  have hsd4 : d + 4 ≤ s := le_trans hMd4 hM
  have hA : 2 * e * A ≤ s * s := by
    have h : A * (2 * e) ≤ s * s := by
      rw [hAdef]; exact Nat.div_mul_le_self (s * s) (2 * e)
    calc 2 * e * A = A * (2 * e) := by ring
      _ ≤ s * s := h
  refine ⟨hs1, hs2e, ?_, ?_, ?_, ?_⟩
  · -- claim 3: s ≤ (q-1)/e
    rw [Nat.le_div_iff_mul_le (by omega : 0 < e)]
    have h1 : s * e ≤ (s - 1) * s := by
      rw [Nat.mul_comm (s - 1) s]
      exact Nat.mul_le_mul_left s (by omega)
    have h2 : (s - 1) * s = s * s - s := by
      rw [Nat.mul_comm (s - 1) s, Nat.mul_sub_left_distrib, Nat.mul_one]
    have h3 : s * s - s ≤ q - 1 := by
      have h4 : s * s - 1 ≤ q - 1 := Nat.sub_le_sub_right hs2 1
      have h5 : s * s - s ≤ s * s - 1 := by omega
      omega
    calc s * e ≤ (s - 1) * s := h1
      _ = s * s - s := h2
      _ ≤ q - 1 := h3
  · -- claim 4
    have hdiv : s / e ≤ s := Nat.div_le_self s e
    have hsq : s + d + 3 < s * s := by
      linarith only [Nat.mul_le_mul_left s hsd4, Nat.le_mul_of_pos_left d (by omega : 0 < s), hsd4]
    omega
  · -- claim 5
    have hlt : 2 * e + 2 * e ^ 3 * (D + 1) < s * s := by
      have h1 : 2 * e ^ 3 * (D + 1) ≤ 2 * e ^ 3 * (d + 1) :=
        Nat.mul_le_mul_left (2 * e ^ 3) (by omega)
      have h2 : 2 * e + 2 * e ^ 3 * (d + 1) < 4 * e * (d + 1) + 2 * e ^ 3 * (d + 1) + 4 := by
        linarith only [Nat.zero_le (e * d), he]
      have h3 : 4 * e * (d + 1) + 2 * e ^ 3 * (d + 1) + 4 ≤ s * s :=
        le_trans hM (Nat.le_mul_of_pos_left s (by omega))
      omega
    have hkey : 2 * (e * (A + 1) + e ^ 3 * (D + 1)) < 2 * q := by
      have heq : 2 * (e * (A + 1) + e ^ 3 * (D + 1)) = 2 * e * A + (2 * e + 2 * e ^ 3 * (D + 1)) := by ring
      rw [heq]
      calc 2 * e * A + (2 * e + 2 * e ^ 3 * (D + 1)) < s * s + s * s := add_lt_add_of_le_of_lt hA hlt
        _ = 2 * (s * s) := by ring
        _ ≤ 2 * q := by omega
    exact Nat.lt_of_mul_lt_mul_left hkey
  · -- claim 6
    have h2nat : s * s + 1 ≤ 2 * e * (A + 1) := by
      have hx : s * s / (2 * e) < A + 1 := by rw [hAdef]; exact Nat.lt_succ_self _
      have hlt : s * s < (A + 1) * (2 * e) := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * e)).mp hx
      have hcomm : (A + 1) * (2 * e) = 2 * e * (A + 1) := by ring
      omega
    have h3nat : s + e * (d + 2) ≤ e * B := by
      have hmod : s % e < e := Nat.mod_lt s (by omega)
      have hdecomp : e * (s / e) + s % e = s := Nat.div_add_mod s e
      have hexp : e * B = e * (s / e) + e * d + 3 * e := by rw [hBdef]; ring
      have hd2 : e * (d + 2) = e * d + 2 * e := by ring
      rw [hexp, hd2]
      omega
    have h4nat : B ≤ s + d + 3 := by
      have := Nat.div_le_self s e
      rw [hBdef]; omega
    have h5nat : 2 * C ≤ s * (s - 1) := by
      have h : C * 2 ≤ s * (s - 1) := by rw [hCdef]; exact Nat.div_mul_le_self (s * (s - 1)) 2
      omega
    have hZ : ((s * ((A + 1) + B + 1) + D * C : ℕ) : ℤ)
        < ((e * (((A + 1) + 1) * (B + 1)) : ℕ) : ℤ) := by
      have i1 : 2 * (e : ℤ) * (A : ℤ) ≤ (s : ℤ) * (s : ℤ) := by exact_mod_cast hA
      have i2 : (s : ℤ) * (s : ℤ) + 1 ≤ 2 * (e : ℤ) * ((A : ℤ) + 1) := by exact_mod_cast h2nat
      have i3 : (s : ℤ) + (e : ℤ) * ((d : ℤ) + 2) ≤ (e : ℤ) * (B : ℤ) := by exact_mod_cast h3nat
      have i4 : (B : ℤ) ≤ (s : ℤ) + (d : ℤ) + 3 := by exact_mod_cast h4nat
      have i5 : 2 * (C : ℤ) ≤ (s : ℤ) * ((s : ℤ) - 1) := by
        have := Nat.cast_le (α := ℤ).mpr h5nat
        push_cast at this ⊢
        rw [Nat.cast_sub hs1] at this
        exact this
      have i6 : (D : ℤ) ≤ (d : ℤ) := by exact_mod_cast hD
      have i7 : 2 * (e : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs2e
      have i8 : (d : ℤ) + 4 ≤ (s : ℤ) := by exact_mod_cast hsd4
      have i9 : (2 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he
      have i9b : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
      have hs0 : (0 : ℤ) ≤ (s : ℤ) := by linarith only [i7, i9]
      have he0 : (0 : ℤ) ≤ (e : ℤ) := by linarith only [i9]
      have hd0 : (0 : ℤ) ≤ (d : ℤ) := by linarith only [i9b]
      have hD0 : (0 : ℤ) ≤ (D : ℤ) := Nat.cast_nonneg _
      have hB0 : (0 : ℤ) ≤ (B : ℤ) + 1 := by positivity
      have hss1 : (0 : ℤ) ≤ (s : ℤ) * ((s : ℤ) - 1) := mul_nonneg hs0 (by linarith only [i7, i9])
      have hq0 : (0 : ℤ) ≤ ((s : ℤ) - 1) ^ 2 + 2 * (e : ℤ) := by positivity
      have T1 := mul_le_mul_of_nonneg_left i2 (mul_nonneg he0 hB0)
      have T2 := mul_le_mul_of_nonneg_left i5 (mul_nonneg he0 hD0)
      have T3 := mul_le_mul_of_nonneg_left i6 (mul_nonneg he0 hss1)
      have T4 := mul_le_mul_of_nonneg_left i1 hs0
      have T5 := mul_le_mul_of_nonneg_left i3 hq0
      have Q1 := mul_nonneg (mul_nonneg hs0 (by linarith only [i8] : (0 : ℤ) ≤ (s : ℤ) - (d : ℤ) - 4))
        (by linarith only [i9] : (0 : ℤ) ≤ 3 * (e : ℤ) - 2)
      have Q2 := mul_nonneg (mul_nonneg hs0 hd0) (by linarith only [i9] : (0 : ℤ) ≤ (e : ℤ) - 1)
      have Q3 := mul_nonneg hs0 (by linarith only [i9] : (0 : ℤ) ≤ (e : ℤ) - 2)
      have Q4 := mul_nonneg he0 hd0
      have Q5 := mul_nonneg (mul_nonneg he0 he0) hd0
      have Q6 := mul_nonneg he0 he0
      have key : (e : ℤ) * (2 * ((s : ℤ) * (((A : ℤ) + 1) + (B : ℤ) + 1) + (D : ℤ) * (C : ℤ)))
          < (e : ℤ) * (2 * ((e : ℤ) * ((((A : ℤ) + 1) + 1) * ((B : ℤ) + 1)))) := by
        linarith only [T1, T2, T3, T4, T5, Q1, Q2, Q3, Q4, Q5, Q6, i9]
      have key2 := lt_of_mul_lt_mul_left key he0
      push_cast
      linarith only [key2]
    exact_mod_cast hZ

end Commons.NumberTheory.Stepanov
