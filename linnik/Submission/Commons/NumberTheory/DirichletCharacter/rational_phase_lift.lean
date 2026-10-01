import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.criticalClass_gaussSum_primePow

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.DirichletCharacter

open Polynomial

/-! ### Elementary facts about polynomials of degree ≤ 2 over `ℤ` -/

lemma poly_eq_of_natDegree_le_two (P : Polynomial ℤ) (h : P.natDegree ≤ 2) :
    P = C (P.coeff 0) + C (P.coeff 1) * X + C (P.coeff 2) * X ^ 2 := by
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow' (n := 3) (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ring

lemma poly_eval_eq_of_natDegree_le_two (P : Polynomial ℤ) (h : P.natDegree ≤ 2) (z : ℤ) :
    P.eval z = P.coeff 0 + P.coeff 1 * z + P.coeff 2 * z ^ 2 := by
  conv_lhs => rw [poly_eq_of_natDegree_le_two P h]
  simp

lemma poly_derivative_eval_eq_of_natDegree_le_two (P : Polynomial ℤ) (h : P.natDegree ≤ 2)
    (z : ℤ) : P.derivative.eval z = P.coeff 1 + 2 * P.coeff 2 * z := by
  conv_lhs => rw [poly_eq_of_natDegree_le_two P h]
  simp [Polynomial.derivative_pow]
  ring

lemma poly_eval_add_of_natDegree_le_two (P : Polynomial ℤ) (h : P.natDegree ≤ 2) (x t : ℤ) :
    P.eval (x + t) = P.eval x + t * P.derivative.eval x + t ^ 2 * P.coeff 2 := by
  rw [poly_eval_eq_of_natDegree_le_two P h, poly_eval_eq_of_natDegree_le_two P h,
      poly_derivative_eval_eq_of_natDegree_le_two P h]
  ring

/-- The abstract algebraic rearrangement on which `rational_phase_lift` rests. -/
lemma rational_phase_lift_key {R : Type*} [CommRing R] [Inv R] (p : R) (a : ℕ)
    (n0 Nu Gu gg h : R) (hh : h * h⁻¹ = 1) (hgg : gg * gg⁻¹ = 1)
    (hgh : (gg * h)⁻¹ = gg⁻¹ * h⁻¹) (heq : h = gg + p ^ 2 * Gu) :
    p ^ a * (n0 + p ^ 2 * Nu) * h⁻¹
      = p ^ a * n0 * gg⁻¹ + p ^ (a + 2) * (gg * Nu - n0 * Gu) * (gg * h)⁻¹ := by
  have key : p ^ a * (n0 + p ^ 2 * Nu) * gg
      = p ^ a * n0 * h + p ^ (a + 2) * (gg * Nu - n0 * Gu) := by
    rw [heq, pow_add]; ring
  have step1 : (p ^ a * (n0 + p ^ 2 * Nu) * gg) * (gg * h)⁻¹
      = p ^ a * (n0 + p ^ 2 * Nu) * h⁻¹ := by
    rw [hgh]
    rw [show p ^ a * (n0 + p ^ 2 * Nu) * gg * (gg⁻¹ * h⁻¹)
        = p ^ a * (n0 + p ^ 2 * Nu) * (gg * gg⁻¹) * h⁻¹ by ring]
    simp [hgg]
  have step2 : (p ^ a * n0 * h + p ^ (a + 2) * (gg * Nu - n0 * Gu)) * (gg * h)⁻¹
      = p ^ a * n0 * gg⁻¹ + p ^ (a + 2) * (gg * Nu - n0 * Gu) * (gg * h)⁻¹ := by
    rw [hgh, add_mul]
    rw [show p ^ a * n0 * h * (gg⁻¹ * h⁻¹) = p ^ a * n0 * gg⁻¹ * (h * h⁻¹) by ring, hh, mul_one]
  rw [← step1, key, step2]

theorem rational_phase_lift (p e a : ℕ) [Fact p.Prime] (he : 2 ≤ e) (ha : 1 ≤ a)
    (A : ZMod (p ^ e)) (hA : (p : ZMod (p ^ e)) ∣ A - 1)
    (N₂ G₂ : Polynomial ℤ) (hN : N₂.natDegree ≤ 2) (hN2 : ¬ (p : ℤ) ∣ N₂.coeff 2)
    (hG : G₂.natDegree ≤ 2) (hG1 : (p : ℤ) ∣ G₂.coeff 1) (hG2 : (p : ℤ) ∣ G₂.coeff 2)
    (hG0 : ¬ (p : ℤ) ∣ G₂.coeff 0)
    (a₀ : ℕ) (hroot : (p : ℤ) ∣ (Polynomial.derivative N₂).eval (a₀ : ℤ)) :
    ∃ (A' : ZMod (p ^ e)) (N' G' : Polynomial ℤ),
      N'.natDegree ≤ 2 ∧ ¬ (p : ℤ) ∣ N'.coeff 2 ∧
      G'.natDegree ≤ 2 ∧ (p : ℤ) ∣ G'.coeff 1 ∧ (p : ℤ) ∣ G'.coeff 2 ∧ ¬ (p : ℤ) ∣ G'.coeff 0 ∧
      (p : ZMod (p ^ e)) ∣ A' - 1 ∧
      (∀ u : ℕ, A + (p : ZMod (p ^ e)) ^ a
            * ((N₂.eval ((a₀ + p * u : ℕ) : ℤ) : ℤ) : ZMod (p ^ e))
            * (((G₂.eval ((a₀ + p * u : ℕ) : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹
          = A' + (p : ZMod (p ^ e)) ^ (a + 2)
            * ((N'.eval (u : ℤ) : ℤ) : ZMod (p ^ e))
            * (((G'.eval (u : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  -- `G₂'(a₀) ≡ 0 (mod p)`
  have hrootG : (p : ℤ) ∣ (Polynomial.derivative G₂).eval (a₀ : ℤ) := by
    rw [poly_derivative_eval_eq_of_natDegree_le_two G₂ hG (a₀ : ℤ)]
    refine dvd_add hG1 ?_
    obtain ⟨k, hk⟩ := hG2
    exact ⟨2 * k * (a₀ : ℤ), by rw [hk]; ring⟩
  obtain ⟨m, hm⟩ := hroot
  obtain ⟨n, hn⟩ := hrootG
  set n0 : ℤ := N₂.eval (a₀ : ℤ) with hn0
  set g0 : ℤ := G₂.eval (a₀ : ℤ) with hg0
  set Nt : Polynomial ℤ := C m * X + C (N₂.coeff 2) * X ^ 2 with hNt
  set Gt : Polynomial ℤ := C n * X + C (G₂.coeff 2) * X ^ 2 with hGt
  set N' : Polynomial ℤ := C g0 * Nt - C n0 * Gt with hN'def
  set G' : Polynomial ℤ := C g0 * (C g0 + C ((p : ℤ) ^ 2) * Gt) with hG'def
  set A' : ZMod (p ^ e) :=
    A + (p : ZMod (p ^ e)) ^ a * ((n0 : ℤ) : ZMod (p ^ e)) * (((g0 : ℤ) : ZMod (p ^ e)))⁻¹
    with hA'def
  -- `g₀` is prime to `p`, hence a unit of `ZMod (p^e)`
  have hg0c0 : g0 - G₂.coeff 0 = G₂.coeff 1 * (a₀ : ℤ) + G₂.coeff 2 * (a₀ : ℤ) ^ 2 := by
    rw [hg0, poly_eval_eq_of_natDegree_le_two G₂ hG]
    ring
  have hdvd_g0c0 : (p : ℤ) ∣ g0 - G₂.coeff 0 := by
    rw [hg0c0]
    exact dvd_add (hG1.mul_right (a₀ : ℤ)) (hG2.mul_right ((a₀ : ℤ) ^ 2))
  have hg0_not_dvd : ¬ (p : ℤ) ∣ g0 := by
    intro h
    have h1 : (p : ℤ) ∣ G₂.coeff 0 := by
      have := h.sub hdvd_g0c0
      simpa using this
    exact hG0 h1
  have hcop : IsCoprime ((p ^ e : ℕ) : ℤ) g0 := by
    have h1 : IsCoprime (p : ℤ) g0 := hpZ.coprime_iff_not_dvd.mpr hg0_not_dvd
    have h2 : IsCoprime ((p : ℤ) ^ e) g0 := h1.pow_left
    rwa [← Nat.cast_pow] at h2
  have hunit_gg : IsUnit (((g0 : ℤ) : ZMod (p ^ e))) :=
    (ZMod.coe_int_isUnit_iff_isCoprime g0 (p ^ e)).mpr hcop
  have hgg : (((g0 : ℤ) : ZMod (p ^ e))) * (((g0 : ℤ) : ZMod (p ^ e)))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hunit_gg
  have hpz_pow : (p : ZMod (p ^ e)) ^ e = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hpz2_pow : ((p : ZMod (p ^ e)) ^ 2) ^ e = 0 := by
    rw [← pow_mul, show 2 * e = e * 2 by ring, pow_mul, hpz_pow, zero_pow (by norm_num)]
  -- polynomial decompositions of `N'` and `G'`
  have hN'eq : N' = C (g0 * m - n0 * n) * X ^ 1
      + C (g0 * (N₂.coeff 2) - n0 * (G₂.coeff 2)) * X ^ 2 := by
    rw [hN'def, hNt, hGt]
    simp only [Polynomial.C_mul, Polynomial.C_sub]
    ring
  have hN'c2 : N'.coeff 2 = g0 * (N₂.coeff 2) - n0 * (G₂.coeff 2) := by
    rw [hN'eq]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    norm_num
  have hG'eq : G' = C (g0 * g0) + C (g0 * (p : ℤ) ^ 2 * n) * X ^ 1
      + C (g0 * (p : ℤ) ^ 2 * (G₂.coeff 2)) * X ^ 2 := by
    rw [hG'def, hGt]
    simp only [Polynomial.C_mul]
    ring
  have hG'c0 : G'.coeff 0 = g0 * g0 := by
    rw [hG'eq]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C]
    norm_num
  have hG'c1 : G'.coeff 1 = g0 * (p : ℤ) ^ 2 * n := by
    rw [hG'eq]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C]
    norm_num
  have hG'c2 : G'.coeff 2 = g0 * (p : ℤ) ^ 2 * (G₂.coeff 2) := by
    rw [hG'eq]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C]
    norm_num
  refine ⟨A', N', G', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN'eq]
    refine le_trans (natDegree_add_le _ _)
      (max_le (le_trans (natDegree_C_mul_X_pow_le _ 1) (by norm_num))
        (natDegree_C_mul_X_pow_le _ 2))
  · rw [hN'c2]
    have hpd2 : ¬ (p : ℤ) ∣ g0 * (N₂.coeff 2) := by
      intro h
      rcases hpZ.dvd_mul.mp h with h' | h'
      · exact hg0_not_dvd h'
      · exact hN2 h'
    intro h
    have hpc2 : (p : ℤ) ∣ n0 * (G₂.coeff 2) := by
      obtain ⟨k, hk⟩ := hG2
      exact ⟨n0 * k, by rw [hk]; ring⟩
    have : (p : ℤ) ∣ g0 * (N₂.coeff 2) := by
      have := h.add hpc2
      simpa using this
    exact hpd2 this
  · rw [hG'eq]
    refine le_trans (natDegree_add_le _ _)
      (max_le ?_ (natDegree_C_mul_X_pow_le _ 2))
    refine le_trans (natDegree_add_le _ _)
      (max_le ?_ (le_trans (natDegree_C_mul_X_pow_le _ 1) (by norm_num)))
    rw [natDegree_C]; norm_num
  · rw [hG'c1]; exact ⟨g0 * (p : ℤ) * n, by ring⟩
  · rw [hG'c2]; exact ⟨g0 * (p : ℤ) * (G₂.coeff 2), by ring⟩
  · rw [hG'c0]
    intro h
    rcases hpZ.dvd_mul.mp h with h' | h'
    · exact hg0_not_dvd h'
    · exact hg0_not_dvd h'
  · have hA'1 : A' - 1 = (A - 1) + (p : ZMod (p ^ e)) ^ a * ((n0 : ℤ) : ZMod (p ^ e))
        * (((g0 : ℤ) : ZMod (p ^ e)))⁻¹ := by
      rw [hA'def]; ring
    rw [hA'1]
    refine dvd_add hA ?_
    refine ⟨(p : ZMod (p ^ e)) ^ (a - 1) * ((n0 : ℤ) : ZMod (p ^ e))
      * (((g0 : ℤ) : ZMod (p ^ e)))⁻¹, ?_⟩
    conv_lhs => rw [show a = (a - 1) + 1 by omega]
    rw [pow_succ']
    ring
  · intro u
    set GX : ZMod (p ^ e) := ((G₂.eval ((a₀ + p * u : ℕ) : ℤ) : ℤ) : ZMod (p ^ e)) with hGXdef
    have hcast : ((a₀ + p * u : ℕ) : ℤ) = (a₀ : ℤ) + (p : ℤ) * (u : ℤ) := by push_cast; ring
    have hNx : N₂.eval ((a₀ + p * u : ℕ) : ℤ) = n0 + (p : ℤ) ^ 2 * Nt.eval (u : ℤ) := by
      rw [hcast, poly_eval_add_of_natDegree_le_two N₂ hN (a₀ : ℤ) ((p : ℤ) * (u : ℤ)), hm, ← hn0]
      rw [hNt]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_pow]
      ring
    have hGx : G₂.eval ((a₀ + p * u : ℕ) : ℤ) = g0 + (p : ℤ) ^ 2 * Gt.eval (u : ℤ) := by
      rw [hcast, poly_eval_add_of_natDegree_le_two G₂ hG (a₀ : ℤ) ((p : ℤ) * (u : ℤ)), hn, ← hg0]
      rw [hGt]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_pow]
      ring
    have hNv : N'.eval (u : ℤ) = g0 * Nt.eval (u : ℤ) - n0 * Gt.eval (u : ℤ) := by
      rw [hN'def]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    have hGv : G'.eval (u : ℤ) = g0 * (g0 + (p : ℤ) ^ 2 * Gt.eval (u : ℤ)) := by
      rw [hG'def]
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C]
    have hNxR : ((N₂.eval ((a₀ + p * u : ℕ) : ℤ) : ℤ) : ZMod (p ^ e))
        = ((n0 : ℤ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) ^ 2
          * ((Nt.eval (u : ℤ) : ℤ) : ZMod (p ^ e)) := by
      rw [hNx]; push_cast; ring
    have hGxR : GX = ((g0 : ℤ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) ^ 2
          * ((Gt.eval (u : ℤ) : ℤ) : ZMod (p ^ e)) := by
      rw [hGXdef, hGx]; push_cast; ring
    have hNvR : ((N'.eval (u : ℤ) : ℤ) : ZMod (p ^ e))
        = ((g0 : ℤ) : ZMod (p ^ e)) * ((Nt.eval (u : ℤ) : ℤ) : ZMod (p ^ e))
          - ((n0 : ℤ) : ZMod (p ^ e)) * ((Gt.eval (u : ℤ) : ℤ) : ZMod (p ^ e)) := by
      rw [hNv]; push_cast; ring
    have hGvR : ((G'.eval (u : ℤ) : ℤ) : ZMod (p ^ e))
        = ((g0 : ℤ) : ZMod (p ^ e)) * (((g0 : ℤ) : ZMod (p ^ e))
          + (p : ZMod (p ^ e)) ^ 2 * ((Gt.eval (u : ℤ) : ℤ) : ZMod (p ^ e))) := by
      rw [hGv]; push_cast; ring
    have hunit_y : IsUnit (1 + (((g0 : ℤ) : ZMod (p ^ e))⁻¹
        * ((p : ZMod (p ^ e)) ^ 2 * ((Gt.eval (u : ℤ) : ℤ) : ZMod (p ^ e))))) := by
      refine isUnit_one_add_of_pow_eq_zero
        (x := ((g0 : ℤ) : ZMod (p ^ e))⁻¹
          * ((p : ZMod (p ^ e)) ^ 2 * ((Gt.eval (u : ℤ) : ℤ) : ZMod (p ^ e)))) ?_
      rw [mul_pow, mul_pow, hpz2_pow, zero_mul, mul_zero]
    have hfac : ((g0 : ℤ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) ^ 2
          * ((Gt.eval (u : ℤ) : ℤ) : ZMod (p ^ e))
        = ((g0 : ℤ) : ZMod (p ^ e)) * (1 + (((g0 : ℤ) : ZMod (p ^ e))⁻¹
          * ((p : ZMod (p ^ e)) ^ 2 * ((Gt.eval (u : ℤ) : ℤ) : ZMod (p ^ e))))) := by
      rw [mul_add, mul_one, ← mul_assoc, hgg, one_mul]
    have hunit_GX : IsUnit GX := by
      rw [hGxR, hfac]; exact hunit_gg.mul hunit_y
    have hh : GX * GX⁻¹ = 1 := ZMod.mul_inv_of_unit GX hunit_GX
    have hgh : (((g0 : ℤ) : ZMod (p ^ e)) * GX)⁻¹
        = (((g0 : ℤ) : ZMod (p ^ e)))⁻¹ * GX⁻¹ :=
      inv_mul_eq_mul_inv _ _ hunit_gg hunit_GX
    have key := rational_phase_lift_key (p := (p : ZMod (p ^ e))) (a := a)
      (n0 := ((n0 : ℤ) : ZMod (p ^ e))) (Nu := ((Nt.eval (u : ℤ) : ℤ) : ZMod (p ^ e)))
      (Gu := ((Gt.eval (u : ℤ) : ℤ) : ZMod (p ^ e))) (gg := ((g0 : ℤ) : ZMod (p ^ e)))
      (h := GX) hh hgg hgh hGxR
    rw [hA'def, hNxR, hNvR, hGvR, ← hGxR, key]
    ring

end Commons.NumberTheory.DirichletCharacter
