import Mathlib

namespace Work.ZeroEst

open PowerSeries Finset.HasAntidiagonal

/-- Left-hand coefficient extraction for the Wronskian identity.

If `f` vanishes below degree `m` and `g` vanishes below degree `n` (with `0 < m + n`), then the
coefficient of `X^(m+n-1)` of `f' * g` is `m * (coeff m f) * (coeff n g)`. -/
lemma ps_coeff_deriv_mul {m n : ℕ} (f g : PowerSeries ℚ)
    (hf : ∀ i < m, coeff i f = 0) (hg : ∀ i < n, coeff i g = 0)
    (hpos : 0 < m + n) :
    coeff (m + n - 1) (PowerSeries.derivative (R := ℚ) f * g) = (m : ℚ) * coeff m f * coeff n g := by
  rw [coeff_mul]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [zero_add] at hpos ⊢
    have hsum : (∑ x ∈ antidiagonal (n - 1),
        coeff x.1 (PowerSeries.derivative (R := ℚ) f) * coeff x.2 g) = 0 := by
      apply Finset.sum_eq_zero
      rintro ⟨a, b⟩ hx
      rw [mem_antidiagonal] at hx
      have hb : b < n := by omega
      rw [hg b hb, mul_zero]
    rw [hsum]
    simp
  · rw [Finset.sum_eq_single (m - 1, n)]
    · rw [coeff_derivative, Nat.sub_add_cancel hm, Nat.cast_sub hm]
      ring
    · rintro ⟨a, b⟩ hx hne
      rw [mem_antidiagonal] at hx
      rw [coeff_derivative]
      rcases lt_or_ge (a + 1) m with ha | ha
      · rw [hf (a + 1) ha]; ring
      · have hble : b ≤ n := by omega
        have hbne : b ≠ n := by
          intro hbn
          apply hne
          have ha0 : a = m - 1 := by omega
          rw [ha0, hbn]
        have hb : b < n := lt_of_le_of_ne hble hbne
        rw [hg b hb]; ring
    · intro hc
      exact absurd (mem_antidiagonal.mpr (by omega)) hc

/-- Right-hand coefficient extraction for the Wronskian identity, companion to
`ps_coeff_deriv_mul`. -/
lemma ps_coeff_mul_deriv {m n : ℕ} (f g : PowerSeries ℚ)
    (hf : ∀ i < m, coeff i f = 0) (hg : ∀ i < n, coeff i g = 0)
    (hpos : 0 < m + n) :
    coeff (m + n - 1) (f * PowerSeries.derivative (R := ℚ) g) = (n : ℚ) * coeff m f * coeff n g := by
  rw [coeff_mul]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [add_zero] at hpos ⊢
    have hsum : (∑ x ∈ antidiagonal (m - 1),
        coeff x.1 f * coeff x.2 (PowerSeries.derivative (R := ℚ) g)) = 0 := by
      apply Finset.sum_eq_zero
      rintro ⟨a, b⟩ hx
      rw [mem_antidiagonal] at hx
      have ha : a < m := by omega
      rw [hf a ha]; ring
    rw [hsum]
    simp
  · rw [Finset.sum_eq_single (m, n - 1)]
    · rw [coeff_derivative, Nat.sub_add_cancel hn, Nat.cast_sub hn]
      ring
    · rintro ⟨a, b⟩ hx hne
      rw [mem_antidiagonal] at hx
      rw [coeff_derivative]
      rcases lt_or_ge (b + 1) n with hb | hb
      · rw [hg (b + 1) hb]; ring
      · have hale : a ≤ m := by omega
        have hane : a ≠ m := by
          intro ham
          apply hne
          have hb0 : b = n - 1 := by omega
          rw [ham, hb0]
        have ha : a < m := lt_of_le_of_ne hale hane
        rw [hf a ha]; ring
    · intro hc
      exact absurd (mem_antidiagonal.mpr (by omega)) hc

/-- If `f`, `g` are nonzero with `f' * g = f * g'`, and `m`, `n` are their respective lowest
nonzero degrees, then `m = n`. -/
lemma ps_eq_of_coeffs {f g : PowerSeries ℚ}
    (h : PowerSeries.derivative (R := ℚ) f * g = f * PowerSeries.derivative (R := ℚ) g)
    {m n : ℕ} (hm : coeff m f ≠ 0) (hfm : ∀ i < m, coeff i f = 0)
    (hn : coeff n g ≠ 0) (hgn : ∀ i < n, coeff i g = 0) : m = n := by
  rcases Nat.eq_zero_or_pos (m + n) with hpos | hpos
  · omega
  · have e1 := ps_coeff_deriv_mul f g hfm hgn hpos
    have e2 := ps_coeff_mul_deriv f g hfm hgn hpos
    have key : (m : ℚ) * coeff m f * coeff n g = (n : ℚ) * coeff m f * coeff n g := by
      rw [← e1, h, e2]
    rw [mul_assoc, mul_assoc] at key
    have hne : coeff m f * coeff n g ≠ 0 := mul_ne_zero hm hn
    have hcq : (m : ℚ) = (n : ℚ) := mul_right_cancel₀ hne key
    exact_mod_cast hcq

/-- Two nonzero power series over `ℚ` satisfying the Wronskian identity `f' * g = f * g'`
have the same order. -/
lemma ps_order_eq_of_deriv_mul_eq {f g : PowerSeries ℚ} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : PowerSeries.derivative (R := ℚ) f * g = f * PowerSeries.derivative (R := ℚ) g) : f.order = g.order := by
  have hkey := ps_eq_of_coeffs h (coeff_order hf)
    (fun i hi => coeff_of_lt_order_toNat i hi) (coeff_order hg)
    (fun i hi => coeff_of_lt_order_toNat i hi)
  rw [← coe_toNat_order hf, ← coe_toNat_order hg, hkey]

theorem ps_eq_C_mul_of_deriv_mul {A B : PowerSeries ℚ} (hB : B ≠ 0)
    (h : PowerSeries.derivative (R := ℚ) A * B = A * PowerSeries.derivative (R := ℚ) B) :
    ∃ c : ℚ, A = PowerSeries.C c * B := by
  rcases eq_or_ne A 0 with hA | hA
  · exact ⟨0, by rw [hA, map_zero, zero_mul]⟩
  have hord : A.order = B.order := ps_order_eq_of_deriv_mul_eq hA hB h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, A.order = (m : ℕ∞) := ⟨A.order.toNat, (coe_toNat_order hA).symm⟩
  have hmB : B.order = (m : ℕ∞) := by rw [← hord, hm]
  have hmA_toNat : A.order.toNat = m := by rw [hm]; simp
  have hmB_toNat : B.order.toNat = m := by rw [hmB]; simp
  have hcmB : coeff m B ≠ 0 := by rw [← hmB_toNat]; exact coeff_order hB
  refine ⟨coeff m A / coeff m B, ?_⟩
  set c : ℚ := coeff m A / coeff m B with hcdef
  set D : PowerSeries ℚ := A - PowerSeries.C c * B with hDdef
  have hDrel : PowerSeries.derivative (R := ℚ) D * B = D * PowerSeries.derivative (R := ℚ) B := by
    have hder : PowerSeries.derivative (R := ℚ) D
        = PowerSeries.derivative (R := ℚ) A - PowerSeries.C c * PowerSeries.derivative (R := ℚ) B := by
      rw [hDdef, Derivation.map_sub, Derivation.leibniz, PowerSeries.derivative_C]
      simp only [smul_eq_mul, mul_zero, add_zero]
    rw [hder, hDdef]
    simp only [sub_mul]
    rw [h]
    ring
  have hD0 : D = 0 := by
    by_contra hDne
    have hordD : D.order = B.order := ps_order_eq_of_deriv_mul_eq hDne hB hDrel
    have hDcoeff : ∀ i < m + 1, coeff i D = 0 := by
      intro i hi
      rw [hDdef, map_sub, PowerSeries.coeff_C_mul]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
      · rw [PowerSeries.coeff_of_lt_order_toNat i (by rw [hmA_toNat]; exact hlt),
            PowerSeries.coeff_of_lt_order_toNat i (by rw [hmB_toNat]; exact hlt)]
        ring
      · subst heq
        rw [hcdef]
        rw [div_mul_cancel₀ _ hcmB]
        ring
    have hle : ((m + 1 : ℕ) : ℕ∞) ≤ D.order := PowerSeries.nat_le_order D (m + 1) hDcoeff
    rw [hordD, hmB] at hle
    rw [ENat.natCast_le_natCast] at hle
    omega
  have hAD : A - PowerSeries.C c * B = 0 := by rw [← hDdef]; exact hD0
  exact sub_eq_zero.mp hAD

end Work.ZeroEst
