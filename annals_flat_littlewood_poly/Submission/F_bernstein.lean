
import Mathlib

open Complex Polynomial Finset
open scoped Polynomial BigOperators ComplexConjugate

noncomputable section

namespace BernsteinPoly

/-- `A n m = (2m+1)π/(2n)`, the angle of the `m`-th root. -/
def A (n m : ℕ) : ℝ := (2 * (m : ℝ) + 1) * Real.pi / (2 * (n : ℝ))

/-- `η_m = exp(i·A n m)`. -/
def om (n m : ℕ) : ℂ := Complex.exp ((A n m : ℂ) * Complex.I)

lemma om_norm (n : ℕ) (m : ℕ) : ‖om n m‖ = 1 := by
  rw [om]
  simp [Complex.norm_exp_ofReal_mul_I]

lemma om_arg_pow (n : ℕ) (hn : 0 < n) (m : ℕ) :
    ((2 * n : ℕ) : ℂ) * ((A n m : ℂ) * Complex.I) =
      (((2 * m + 1 : ℝ) * Real.pi) : ℂ) * Complex.I := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2nC : ((2 * (n : ℝ)) : ℂ) ≠ 0 := by
    intro h
    have hnz2 : (2 : ℂ) ≠ 0 := by norm_num
    have hx0 : ((n : ℝ) : ℂ) = 0 := (mul_eq_zero.mp h).resolve_left hnz2
    have h0 : (n : ℝ) = 0 := Complex.ofReal_eq_zero.mp hx0
    nlinarith
  have hnC : (n : ℂ) ≠ 0 := by
    intro h
    exact (Nat.ne_of_gt hn) (Nat.cast_eq_zero.mp h)
  rw [A]
  push_cast
  field_simp [h2nC, hnC]

lemma om_pow_two_n (n : ℕ) (hn : 0 < n) (m : ℕ) : (om n m) ^ (2 * n) = -1 := by
  rw [om]
  rw [← Complex.exp_nat_mul]
  rw [om_arg_pow n hn m]
  have hnat : (((2 * m + 1 : ℝ) * Real.pi) : ℂ) * Complex.I =
      (2 * m + 1 : ℕ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hnat, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  norm_num [pow_succ, pow_mul]

lemma om_ne_one (n : ℕ) (hn : 0 < n) (m : ℕ) : om n m ≠ 1 := by
  intro h
  have hpow := congrArg (fun x : ℂ => x ^ (2 * n)) h
  rw [om_pow_two_n n hn, one_pow] at hpow
  norm_num at hpow

lemma om_ne_zero (n : ℕ) (m : ℕ) : om n m ≠ 0 := by
  intro h
  have hnorm := congrArg norm h
  rw [om_norm n m] at hnorm
  norm_num at hnorm

lemma normSq_eq_mul_star (w : ℂ) : (‖w‖ ^ 2 : ℂ) = star w * w := by
  have hns := Complex.normSq_eq_conj_mul_self (z := w)
  have hnorm : (‖w‖ ^ 2 : ℂ) = (normSq w : ℂ) := by
    exact_mod_cast (Complex.normSq_eq_norm_sq w).symm
  calc (‖w‖ ^ 2 : ℂ) = (normSq w : ℂ) := hnorm
    _ = star w * w := by simpa [mul_comm] using hns

lemma om_conj_eq_inv (n : ℕ) (m : ℕ) : star (om n m) = (om n m)⁻¹ := by
  have hw : om n m ≠ 0 := om_ne_zero n m
  have hsq : (1 : ℂ) = star (om n m) * (om n m) := by
    have hn : (1 : ℂ) = (‖om n m‖ ^ 2 : ℂ) := by rw [om_norm n m]; norm_num
    rw [hn]
    exact normSq_eq_mul_star (om n m)
  calc star (om n m) = star (om n m) * (om n m * (om n m)⁻¹) := by rw [mul_inv_cancel₀ hw]; ring
    _ = (star (om n m) * (om n m)) * (om n m)⁻¹ := by ring
    _ = (om n m)⁻¹ := by rw [← hsq]; simp

/-- `‖om - 1‖² = (om - 1)·(star om - 1)` (as complex numbers). -/
lemma normSq_om_sub_one (n : ℕ) (m : ℕ) :
    (‖om n m - 1‖ ^ 2 : ℂ) = (om n m - 1) * (star (om n m) - 1) := by
  calc (‖om n m - 1‖ ^ 2 : ℂ) = star (om n m - 1) * (om n m - 1) := normSq_eq_mul_star (om n m - 1)
    _ = (star (om n m) - 1) * (om n m - 1) := by simp [map_sub, map_one]
    _ = (om n m - 1) * (star (om n m) - 1) := by ring

/-- `1/‖om - 1‖² = -om·(om-1)⁻²`. -/
lemma inv_normSq_om (n : ℕ) (hn : 0 < n) (m : ℕ) :
    ((1 : ℂ) / (‖om n m - 1‖ ^ 2 : ℂ)) = -(om n m) * (((om n m - 1)⁻¹) ^ 2) := by
  have hz : om n m - 1 ≠ 0 := sub_ne_zero.mpr (om_ne_one n hn m)
  have hz2 : om n m ≠ 0 := om_ne_zero n m
  have hz1 : 1 - om n m ≠ 0 := by
    have hneg : -(om n m - 1) ≠ 0 := neg_ne_zero.mpr hz
    convert hneg using 1 <;> ring
  have hsq : (‖om n m - 1‖ ^ 2 : ℂ) = (om n m - 1) * (star (om n m) - 1) := normSq_om_sub_one n m
  calc (1 : ℂ) / (‖om n m - 1‖ ^ 2 : ℂ)
      = (1 : ℂ) / ((om n m - 1) * (star (om n m) - 1)) := by rw [hsq]
    _ = (1 : ℂ) / ((om n m - 1) * ((om n m)⁻¹ - 1)) := by rw [om_conj_eq_inv]
    _ = -(om n m) * (((om n m - 1)⁻¹) ^ 2) := by
          field [hz, hz2, hz1]

lemma A_decomp (n : ℕ) (hn : 0 < n) (m : ℕ) : A n m = A n 0 + (m : ℝ) * (Real.pi / (n : ℝ)) := by
  rw [A, A]
  field_simp [show (2 * (n : ℝ)) ≠ 0 by positivity, show (n : ℝ) ≠ 0 by
    exact_mod_cast (Nat.ne_of_gt hn)]
  ring

def rho (n : ℕ) : ℂ := Complex.exp (((Real.pi / (n : ℝ)) : ℂ) * Complex.I)

lemma om_eq_om_zero_mul (n : ℕ) (hn : 0 < n) (m : ℕ) : om n m = om n 0 * (rho n) ^ m := by
  rw [om, om, rho]
  rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_add]
  congr 1
  rw [A_decomp n hn]
  push_cast
  ring

lemma om_pow_split (n : ℕ) (hn : 0 < n) (m t : ℕ) :
    (om n m) ^ t = (om n 0) ^ t * ((rho n) ^ t) ^ m := by
  rw [om_eq_om_zero_mul n hn]
  rw [mul_pow]
  congr 1
  have hp : ((rho n) ^ m) ^ t = ((rho n) ^ t) ^ m := by
    calc ((rho n) ^ m) ^ t = (rho n) ^ (m * t) := by rw [← pow_mul]
      _ = (rho n) ^ (t * m) := by rw [Nat.mul_comm]
      _ = ((rho n) ^ t) ^ m := by rw [pow_mul]
  exact hp

lemma rhoT_ne_one (n : ℕ) (hn : 0 < n) (t : ℕ) (ht1 : 1 ≤ t) (ht2 : t < 2 * n) :
    Complex.exp (((Real.pi * (t : ℝ) / (n : ℝ)) : ℂ) * Complex.I) ≠ 1 := by
  intro hq
  obtain ⟨j, hj⟩ := Complex.exp_eq_one_iff.mp hq
  have hi : I ≠ 0 := by norm_num
  have hπc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have harg : ((t : ℝ) : ℂ) / ((n : ℝ) : ℂ) = (2 : ℂ) * (j : ℂ) := by
    have h1 := congrArg (fun x : ℂ => x / I) hj
    field_simp [hi, hπc] at h1
    simpa [mul_comm] using h1
  have hreal : (t : ℝ) / (n : ℝ) = 2 * (j : ℝ) := by
    exact_mod_cast harg
  have ht : (t : ℝ) = 2 * (n : ℝ) * (j : ℝ) := by
    have h1 := congrArg (fun x : ℝ => x * (n : ℝ)) hreal
    field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn)] at h1
    nlinarith
  have hz : (t : ℤ) = 2 * (n : ℤ) * j := by
    apply Int.cast_injective (α := ℝ)
    norm_num at ht ⊢
    exact ht
  by_cases hjp : 1 ≤ j
  · nlinarith
  · have hj0 : j ≤ 0 := by omega
    have htle : (t : ℤ) ≤ 0 := by nlinarith
    omega

lemma rho_two_n (n : ℕ) (hn : 0 < n) : (rho n) ^ (2 * n) = 1 := by
  rw [rho]
  rw [← Complex.exp_nat_mul]
  congr 1
  have harg : ((2 * n : ℕ) : ℂ) * (((Real.pi / (n : ℝ)) : ℂ) * Complex.I) =
      ((2 * Real.pi) : ℂ) * Complex.I := by
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnC : (n : ℂ) ≠ 0 := by
      intro h
      exact (Nat.ne_of_gt hn) (Nat.cast_eq_zero.mp h)
    push_cast
    field_simp [hnC, show ((n : ℝ) : ℂ) ≠ 0 by
      intro h; have h0 : (n : ℝ) = 0 := Complex.ofReal_eq_zero.mp h; nlinarith]
  rw [harg]
  simpa [mul_assoc, mul_comm, mul_left_comm] using Complex.exp_two_pi_mul_I

lemma rho_pow (n : ℕ) (t : ℕ) : (rho n) ^ t = Complex.exp (((Real.pi * (t : ℝ) / (n : ℝ)) : ℂ) * Complex.I) := by
  rw [rho]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma geom_sum_of_pow_eq_one (L : ℕ) {q : ℂ} (hq : q ≠ 1) (hqpow : q ^ L = 1) :
    (∑ m ∈ Finset.range L, q ^ m) = 0 := by
  have h := geom_sum_mul q L
  rw [hqpow] at h
  have hz : (∑ m ∈ Finset.range L, q ^ m) * (q - 1) = 0 := by simpa using h
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hq)

def psum (n t : ℕ) : ℂ := ∑ m ∈ Finset.range (2 * n), (om n m) ^ t

lemma psum_zero (n : ℕ) (hn : 0 < n) {t : ℕ} (ht1 : 1 ≤ t) (ht2 : t < 2 * n) :
    psum n t = 0 := by
  unfold psum
  let q : ℂ := (rho n) ^ t
  have hsplit : ∀ m ∈ Finset.range (2 * n), (om n m) ^ t = (om n 0) ^ t * q ^ m := by
    intro m hm
    rw [om_pow_split n hn]
  calc
    (∑ m ∈ Finset.range (2 * n), (om n m) ^ t)
        = ∑ m ∈ Finset.range (2 * n), ((om n 0) ^ t * q ^ m) := by
            apply sum_congr rfl
            intro m hm
            exact hsplit m hm
    _ = (om n 0) ^ t * (∑ m ∈ Finset.range (2 * n), q ^ m) := by rw [mul_sum]
    _ = 0 := by
          have hq : q ≠ 1 := by
            dsimp [q]
            rw [rho_pow]
            exact rhoT_ne_one n hn t ht1 ht2
          have hqpow : q ^ (2 * n) = 1 := by
            dsimp [q]
            rw [← pow_mul]
            rw [Nat.mul_comm t (2 * n), pow_mul]
            rw [rho_two_n n hn]
            simp
          have hsum : (∑ m ∈ Finset.range (2 * n), q ^ m) = 0 :=
            geom_sum_of_pow_eq_one (2 * n) hq hqpow
          rw [hsum]
          all_goals ring

lemma psum_zero_value (n : ℕ) : psum n 0 = (2 * n : ℂ) := by
  unfold psum
  simp

def gsum (n p : ℕ) : ℂ := ∑ m ∈ Finset.range (2 * n), (om n m) ^ p * (om n m - 1)⁻¹

def fsum (n p : ℕ) : ℂ := ∑ m ∈ Finset.range (2 * n), (om n m) ^ p * (((om n m - 1)⁻¹) ^ 2)

lemma om_inv_geom (n : ℕ) (hn : 0 < n) (m : ℕ) :
    (om n m - 1)⁻¹ = -((2 : ℂ)⁻¹) * (∑ t ∈ Finset.range (2 * n), (om n m) ^ t) := by
  have hz : om n m - 1 ≠ 0 := sub_ne_zero.mpr (om_ne_one n hn m)
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hgeo : (∑ t ∈ Finset.range (2 * n), (om n m) ^ t) * (om n m - 1) = -2 := by
    have h := geom_sum_mul (om n m) (2 * n)
    rw [om_pow_two_n n hn m] at h
    norm_num at h
    exact h
  have hS : (∑ t ∈ Finset.range (2 * n), (om n m) ^ t) = -2 * (om n m - 1)⁻¹ := by
    calc
      (∑ t ∈ Finset.range (2 * n), (om n m) ^ t)
          = (∑ t ∈ Finset.range (2 * n), (om n m) ^ t) * (om n m - 1) * (om n m - 1)⁻¹ := by field [hz]
      _ = (-2) * (om n m - 1)⁻¹ := by rw [hgeo]
  calc
    (om n m - 1)⁻¹ = -((2 : ℂ)⁻¹) * (∑ t ∈ Finset.range (2 * n), (om n m) ^ t) := by
      rw [hS]
      field [hz, htwo]

lemma gsum_zero_eq (n : ℕ) (hn : 0 < n) : gsum n 0 = -((n : ℕ) : ℂ) := by
  calc
    gsum n 0 = ∑ m ∈ Finset.range (2 * n), (om n m - 1)⁻¹ := by
        unfold gsum
        simp
    _ = ∑ m ∈ Finset.range (2 * n), (-((2 : ℂ)⁻¹) * (∑ t ∈ Finset.range (2 * n), (om n m) ^ t)) := by
        apply sum_congr rfl
        intro m hm
        rw [om_inv_geom n hn m]
    _ = -((2 : ℂ)⁻¹) * (∑ m ∈ Finset.range (2 * n), (∑ t ∈ Finset.range (2 * n), (om n m) ^ t)) := by
        rw [mul_sum]
    _ = -((2 : ℂ)⁻¹) * (∑ t ∈ Finset.range (2 * n), psum n t) := by
        have hsc : (∑ m ∈ Finset.range (2 * n), (∑ t ∈ Finset.range (2 * n), (om n m) ^ t)) =
            (∑ t ∈ Finset.range (2 * n), psum n t) := by
          unfold psum
          rw [Finset.sum_comm]
        rw [hsc]
    _ = -((2 : ℂ)⁻¹) * (2 * n : ℂ) := by
        congr 1
        have hsum : (∑ t ∈ Finset.range (2 * n), psum n t) = psum n 0 := by
          apply Finset.sum_eq_single 0
          · intro b hb hb0
            have hb1 : 1 ≤ b := by omega
            have hb2 : b < 2 * n := by simpa using hb
            exact psum_zero n hn hb1 hb2
          · simp [show 0 < 2 * n by omega]
        rw [hsum]
        rw [psum_zero_value]
    _ = -((n : ℕ) : ℂ) := by
        norm_num
        ring

lemma gsum_term (n : ℕ) (hn : 0 < n) (m p : ℕ) :
    (om n m) ^ (p + 1) * (om n m - 1)⁻¹ =
      (om n m) ^ p * (om n m - 1)⁻¹ + (om n m) ^ p := by
  have hz : om n m - 1 ≠ 0 := sub_ne_zero.mpr (om_ne_one n hn m)
  calc
    (om n m) ^ (p + 1) * (om n m - 1)⁻¹
        = ((om n m) ^ p * (om n m)) * (om n m - 1)⁻¹ := by rw [pow_succ]
    _ = (om n m) ^ p * ((om n m) * (om n m - 1)⁻¹) := by ring
    _ = (om n m) ^ p * (1 + (om n m - 1)⁻¹) := by
          congr 1
          field [hz]
    _ = (om n m) ^ p * (om n m - 1)⁻¹ + (om n m) ^ p := by ring

lemma gsum_succ (n : ℕ) (hn : 0 < n) (p : ℕ) : gsum n (p + 1) = gsum n p + psum n p := by
  unfold gsum psum
  rw [← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro m hm
  exact gsum_term n hn m p

lemma fsum_term (n : ℕ) (hn : 0 < n) (m p : ℕ) :
    (om n m) ^ (p + 1) * (((om n m - 1)⁻¹) ^ 2) =
      (om n m) ^ p * (om n m - 1)⁻¹ + (om n m) ^ p * (((om n m - 1)⁻¹) ^ 2) := by
  have hz : om n m - 1 ≠ 0 := sub_ne_zero.mpr (om_ne_one n hn m)
  calc
    (om n m) ^ (p + 1) * (((om n m - 1)⁻¹) ^ 2)
        = ((om n m) ^ p * (om n m)) * (((om n m - 1)⁻¹) ^ 2) := by rw [pow_succ]
    _ = (om n m) ^ p * ((om n m) * (((om n m - 1)⁻¹) ^ 2)) := by ring
    _ = (om n m) ^ p * ((om n m - 1)⁻¹ + ((om n m - 1)⁻¹) ^ 2) := by
          congr 1
          field [hz]
    _ = (om n m) ^ p * (om n m - 1)⁻¹ + (om n m) ^ p * (((om n m - 1)⁻¹) ^ 2) := by ring

lemma fsum_succ (n : ℕ) (hn : 0 < n) (p : ℕ) : fsum n (p + 1) = fsum n p + gsum n p := by
  unfold fsum gsum
  rw [← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro m hm
  simpa [add_comm] using fsum_term n hn m p

lemma gsum_eq (n : ℕ) (hn : 0 < n) (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * n) :
    gsum n p = (n : ℂ) := by
  induction' p with p ih
  · omega
  · by_cases hp0 : p = 0
    · subst p
      rw [gsum_succ n hn]
      rw [gsum_zero_eq n hn, psum_zero_value]
      ring
    · have hp1' : 1 ≤ p := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp0)
      have hps : p < 2 * n := by omega
      rw [gsum_succ n hn]
      rw [psum_zero n hn hp1' hps]
      rw [ih hp1' (le_of_lt hps)]
      ring

lemma fsum_eq_pos (n : ℕ) (hn : 0 < n) (p : ℕ) (hp2 : p ≤ 2 * n + 1) (hp1 : 1 ≤ p) :
    fsum n p = fsum n 1 + ((p : ℂ) - 1) * (n : ℂ) := by
  induction' p with p ih
  · omega
  · by_cases hp0 : p = 0
    · subst p
      ring
    · have hp1' : 1 ≤ p := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp0)
      have hp1'2 : p ≤ 2 * n := by omega
      rw [fsum_succ n hn]
      rw [gsum_eq n hn p hp1' hp1'2]
      rw [ih (by omega) hp1']
      norm_num
      push_cast
      ring

lemma fsum_neg (n : ℕ) (hn : 0 < n) : fsum n (2 * n + 1) = - fsum n 1 := by
  unfold fsum
  rw [← Finset.sum_neg_distrib]
  apply sum_congr rfl
  intro m hm
  have hpow : (om n m) ^ (2 * n + 1) = - (om n m) := by
    calc (om n m) ^ (2 * n + 1) = (om n m) * (om n m) ^ (2 * n) := by rw [pow_succ']
      _ = -(om n m) := by rw [om_pow_two_n n hn m]; ring
  rw [hpow]
  ring

lemma fsum_one_neg (n : ℕ) (hn : 0 < n) : fsum n 1 = - ((n : ℂ) ^ 2) := by
  have h1 : fsum n (2 * n + 1) = - fsum n 1 := fsum_neg n hn
  have h2 : fsum n (2 * n + 1) = fsum n 1 + (2 * n : ℂ) * (n : ℂ) := by
    rw [fsum_eq_pos n hn (2 * n + 1)]
    · push_cast
      ring
    · omega
    · norm_num
  have h3 : fsum n 1 + (2 * n : ℂ) * (n : ℂ) = - fsum n 1 := by
    calc fsum n 1 + (2 * n : ℂ) * (n : ℂ) = fsum n (2 * n + 1) := h2.symm
      _ = - fsum n 1 := h1
  have h3' : 2 * fsum n 1 = -(2 : ℂ) * (n : ℂ) ^ 2 := by
    calc 2 * fsum n 1 = (fsum n 1 + (2 * (n : ℂ)) * (n : ℂ)) - (2 * (n : ℂ)) * (n : ℂ) + fsum n 1 := by ring
      _ = (-fsum n 1) - (2 * (n : ℂ)) * (n : ℂ) + fsum n 1 := by rw [h3]
      _ = -(2 * (n : ℂ)) * (n : ℂ) := by ring
      _ = -(2 : ℂ) * (n : ℂ) ^ 2 := by ring
  calc fsum n 1 = (2 * fsum n 1) / 2 := by field [show (2 : ℂ) ≠ 0 by norm_num]
    _ = (-(2 : ℂ) * (n : ℂ) ^ 2) / 2 := by rw [h3']
    _ = - (n : ℂ) ^ 2 := by field [show (2 : ℂ) ≠ 0 by norm_num]


section weight

/-- The quadrature weight at a root: `W_n(η) = I·η^(n+1)/(n·(η-1)^2)`. -/
def W (n : ℕ) (η : ℂ) : ℂ := (Complex.I * η ^ (n + 1)) * (((η - 1)⁻¹) ^ 2) * (n : ℂ)⁻¹

/-- `fsum n (n+1+k) = n*k` for `k ≤ n`. -/
lemma fsum_nat_mul (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k ≤ n) :
    fsum n (n + 1 + k) = (n : ℂ) * (k : ℂ) := by
  have hle : n + 1 + k ≤ 2 * n + 1 := by omega
  have hge : 1 ≤ n + 1 + k := by omega
  rw [fsum_eq_pos n hn (n + 1 + k) hle hge]
  rw [fsum_one_neg n hn]
  push_cast
  ring

/-- monomial identity: `∑_m W(η_m)·η_m^k = I·k` for `k ≤ n`. -/
lemma wsum_eq (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k ≤ n) :
    (∑ m ∈ Finset.range (2 * n), W n (om n m) * (om n m) ^ k) = Complex.I * (k : ℂ) := by
  calc
    (∑ m ∈ Finset.range (2 * n), W n (om n m) * (om n m) ^ k)
        = (∑ m ∈ Finset.range (2 * n),
            Complex.I * (n : ℂ)⁻¹ * ((om n m) ^ (n + 1 + k) * (((om n m - 1)⁻¹) ^ 2))) := by
            apply sum_congr rfl
            intro m hm
            unfold W
            have hp : (om n m) ^ (n + 1) * (om n m) ^ k = (om n m) ^ (n + 1 + k) := by
              rw [← pow_add]
            calc ((Complex.I * (om n m) ^ (n + 1)) * (((om n m - 1)⁻¹) ^ 2)) * (n : ℂ)⁻¹ * (om n m) ^ k
                = Complex.I * (n : ℂ)⁻¹ * ((om n m) ^ (n + 1) * (om n m) ^ k) *
                    (((om n m - 1)⁻¹) ^ 2) := by ring
              _ = Complex.I * (n : ℂ)⁻¹ * ((om n m) ^ (n + 1 + k) *
                    (((om n m - 1)⁻¹) ^ 2)) := by rw [hp]; ring
    _ = Complex.I * (n : ℂ)⁻¹ * fsum n (n + 1 + k) := by
          unfold fsum
          rw [← Finset.mul_sum]
    _ = Complex.I * (k : ℂ) := by
          rw [fsum_nat_mul n hn k hk]
          field [show (n : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn)]

/-- expand `P` as a sum of monomials up to `n`. -/
lemma as_sum_coeff (P : ℂ[X]) (n : ℕ) (hdeg : P.natDegree ≤ n) :
    P = ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (P.coeff i) := by
  calc P = ∑ i ∈ Finset.range (P.natDegree + 1), Polynomial.monomial i (P.coeff i) := by
        exact (Polynomial.as_sum_range P)
    _ = ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (P.coeff i) := by
        have hsplit : n + 1 = P.natDegree + 1 + (n - P.natDegree) := by omega
        conv_rhs => rw [hsplit]
        conv_rhs => rw [Finset.sum_range_add]
        have htail : (∑ x ∈ Finset.range (n - P.natDegree),
            Polynomial.monomial (P.natDegree + 1 + x) (P.coeff (P.natDegree + 1 + x))) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          have hlt : P.natDegree < P.natDegree + 1 + x := by omega
          have hz : P.coeff (P.natDegree + 1 + x) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
          rw [hz]
          simp
        rw [htail]
        simp

lemma eval_eq_sum_coeff (P : ℂ[X]) (n : ℕ) (hdeg : P.natDegree ≤ n) (x : ℂ) :
    P.eval x = ∑ i ∈ Finset.range (n + 1), P.coeff i * x ^ i := by
  calc P.eval x = (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (P.coeff i)).eval x := by
        conv_lhs => rw [as_sum_coeff P n hdeg]
    _ = ∑ i ∈ Finset.range (n + 1), (Polynomial.monomial i (P.coeff i)).eval x := by
        rw [Polynomial.eval_finset_sum]
    _ = ∑ i ∈ Finset.range (n + 1), P.coeff i * x ^ i := by
        apply sum_congr rfl
        intro i hi
        rw [Polynomial.eval_monomial]

lemma derivative_eval_sum_coeff (P : ℂ[X]) (n : ℕ) (hdeg : P.natDegree ≤ n) (x : ℂ) :
    (P.derivative).eval x = ∑ i ∈ Finset.range (n + 1), P.coeff i * (i : ℂ) * x ^ (i - 1) := by
  calc (P.derivative).eval x = (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (P.coeff i)).derivative.eval x := by
        conv_lhs => rw [as_sum_coeff P n hdeg]
    _ = (∑ i ∈ Finset.range (n + 1), (Polynomial.monomial i (P.coeff i)).derivative).eval x := by
        rw [map_sum]
    _ = ∑ i ∈ Finset.range (n + 1), (Polynomial.monomial i (P.coeff i)).derivative.eval x := by
        rw [Polynomial.eval_finset_sum]
    _ = ∑ i ∈ Finset.range (n + 1), P.coeff i * (i : ℂ) * x ^ (i - 1) := by
        apply sum_congr rfl
        intro i hi
        rw [Polynomial.derivative_monomial]
        rw [Polynomial.eval_monomial]

/-- main quadrature identity for an arbitrary polynomial of degree `≤ n`. -/
lemma eval_sum_eq (P : ℂ[X]) (n : ℕ) (hn : 0 < n) (hdeg : P.natDegree ≤ n) (z : ℂ) :
    (∑ m ∈ Finset.range (2 * n), W n (om n m) * P.eval (z * om n m)) =
      Complex.I * z * (P.derivative).eval z := by
  calc
    (∑ m ∈ Finset.range (2 * n), W n (om n m) * P.eval (z * om n m))
        = (∑ m ∈ Finset.range (2 * n), W n (om n m) *
            (∑ i ∈ Finset.range (n + 1), P.coeff i * (z * om n m) ^ i)) := by
            apply sum_congr rfl
            intro m hm
            rw [eval_eq_sum_coeff P n hdeg (z * om n m)]
    _ = ∑ m ∈ Finset.range (2 * n), ∑ i ∈ Finset.range (n + 1),
            (W n (om n m) * (P.coeff i * (z * om n m) ^ i)) := by
            apply sum_congr rfl
            intro m hm
            rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (2 * n),
            (W n (om n m) * (P.coeff i * (z * om n m) ^ i)) := by
            rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range (n + 1), P.coeff i * z ^ i * (Complex.I * (i : ℂ)) := by
            apply sum_congr rfl
            intro i hi
            calc (∑ m ∈ Finset.range (2 * n), W n (om n m) * (P.coeff i * (z * om n m) ^ i))
                = ∑ m ∈ Finset.range (2 * n),
                    P.coeff i * z ^ i * (W n (om n m) * (om n m) ^ i) := by
                    apply sum_congr rfl
                    intro m hm
                    simp only [mul_pow]
                    ring
              _ = P.coeff i * z ^ i *
                    (∑ m ∈ Finset.range (2 * n), W n (om n m) * (om n m) ^ i) := by
                    rw [← Finset.mul_sum]
              _ = P.coeff i * z ^ i * (Complex.I * (i : ℂ)) := by
                    rw [wsum_eq n hn i (by simpa using (Finset.mem_range.mp hi))]
    _ = Complex.I * z * (P.derivative).eval z := by
            have hder : (P.derivative).eval z = ∑ i ∈ Finset.range (n + 1), P.coeff i * (i : ℂ) * z ^ (i - 1) := by
              exact derivative_eval_sum_coeff P n hdeg z
            rw [hder]
            rw [mul_sum]
            apply sum_congr rfl
            intro i hi
            by_cases hiz : i = 0
            · subst i
              simp
            · have hz : z ^ i = z * z ^ (i - 1) := by
                rw [← pow_succ']
                congr 1
                omega
              rw [hz]
              ring

/-- `‖W n (om n m)‖ = 1/(n·‖om-1‖²)`. -/
lemma W_norm_term (n : ℕ) (hn : 0 < n) (m : ℕ) :
    ‖W n (om n m)‖ = (1 : ℝ) / ((n : ℝ) * ‖om n m - 1‖ ^ 2) := by
  unfold W
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnz : ‖om n m - 1‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    exact sub_ne_zero.mpr (om_ne_one n hn m)
  calc
    ‖(Complex.I * (om n m) ^ (n + 1)) * (((om n m - 1)⁻¹) ^ 2) * (n : ℂ)⁻¹‖
        = ‖Complex.I * (om n m) ^ (n + 1)‖ * ‖((om n m - 1)⁻¹) ^ 2‖ * ‖(n : ℂ)⁻¹‖ := by
            rw [norm_mul, norm_mul]
    _ = (1 : ℝ) * ‖om n m‖ ^ (n + 1) * ((‖om n m - 1‖)⁻¹) ^ 2 * ((n : ℝ)⁻¹) := by
            rw [norm_mul, norm_pow, Complex.norm_I]
            rw [norm_pow, norm_inv, norm_inv]
            rw [Complex.norm_natCast]
    _ = (1 : ℝ) / ((n : ℝ) * ‖om n m - 1‖ ^ 2) := by
            rw [om_norm n m]
            field [hnR, hnz]

/-- `∑_m 1/‖om-1‖² = n²`. -/
lemma sum_inv_normSq (n : ℕ) (hn : 0 < n) :
    (∑ m ∈ Finset.range (2 * n), (1 : ℝ) / ‖om n m - 1‖ ^ 2) = (n : ℝ) ^ 2 := by
  have hc : (∑ m ∈ Finset.range (2 * n), ((1 : ℂ) / (‖om n m - 1‖ ^ 2 : ℂ))) = (n : ℂ) ^ 2 := by
    calc
      (∑ m ∈ Finset.range (2 * n), ((1 : ℂ) / (‖om n m - 1‖ ^ 2 : ℂ)))
          = ∑ m ∈ Finset.range (2 * n), (-(om n m) * (((om n m - 1)⁻¹) ^ 2)) := by
              apply sum_congr rfl
              intro m hm
              rw [inv_normSq_om n hn m]
      _ = -(∑ m ∈ Finset.range (2 * n), (om n m) * (((om n m - 1)⁻¹) ^ 2)) := by
              rw [← Finset.sum_neg_distrib]
              apply sum_congr rfl
              intro m hm
              ring
      _ = - fsum n 1 := by
              congr 1
              unfold fsum
              apply sum_congr rfl
              intro m hm
              simp [pow_one]
      _ = (n : ℂ) ^ 2 := by
              rw [fsum_one_neg n hn]
              ring
  have hreal : (↑(∑ m ∈ Finset.range (2 * n), (1 : ℝ) / ‖om n m - 1‖ ^ 2) : ℂ) = (n : ℂ) ^ 2 := by
    calc (↑(∑ m ∈ Finset.range (2 * n), (1 : ℝ) / ‖om n m - 1‖ ^ 2) : ℂ)
        = ∑ m ∈ Finset.range (2 * n), ((1 : ℂ) / (‖om n m - 1‖ ^ 2 : ℂ)) := by
            rw [Complex.ofReal_sum]
            apply sum_congr rfl
            intro m hm
            rw [Complex.ofReal_div]
            norm_num
      _ = (n : ℂ) ^ 2 := hc
  exact_mod_cast hreal

/-- `∑_m ‖W n (om n m)‖ = n`. -/
lemma sum_norm_W (n : ℕ) (hn : 0 < n) :
    (∑ m ∈ Finset.range (2 * n), ‖W n (om n m)‖) = (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    (∑ m ∈ Finset.range (2 * n), ‖W n (om n m)‖)
        = ∑ m ∈ Finset.range (2 * n), ((1 : ℝ) / ((n : ℝ) * ‖om n m - 1‖ ^ 2)) := by
            apply sum_congr rfl
            intro m hm
            rw [W_norm_term n hn m]
    _ = (1 / (n : ℝ)) * (∑ m ∈ Finset.range (2 * n), (1 : ℝ) / ‖om n m - 1‖ ^ 2) := by
            rw [Finset.mul_sum]
            apply sum_congr rfl
            intro m hm
            have hnz : ‖om n m - 1‖ ≠ 0 := by
              apply norm_ne_zero_iff.mpr
              exact sub_ne_zero.mpr (om_ne_one n hn m)
            field [hnR, hnz]
    _ = (n : ℝ) := by
            rw [sum_inv_normSq n hn]
            field [hnR]

/-- Bernstein's inequality (sharp constant `n`), inner lemma for `0 < n`. -/
lemma bernstein_core (P : ℂ[X]) (n : ℕ) (hn : 0 < n) (hdeg : P.natDegree ≤ n)
    (M : ℝ) (hM : ∀ w : ℂ, ‖w‖ = 1 → ‖P.eval w‖ ≤ M) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(P.derivative).eval z‖ ≤ (n : ℝ) * M := by
  have hnorm : ‖Complex.I * z * (P.derivative).eval z‖ = ‖(P.derivative).eval z‖ := by
    rw [norm_mul, norm_mul]
    rw [hz, Complex.norm_I]
    norm_num
  have hzom : ∀ m ∈ Finset.range (2 * n), ‖z * om n m‖ = 1 := by
    intro m hm
    rw [norm_mul, hz, om_norm n m]
    norm_num
  calc
    ‖(P.derivative).eval z‖
        = ‖Complex.I * z * (P.derivative).eval z‖ := hnorm.symm
    _ = ‖∑ m ∈ Finset.range (2 * n), W n (om n m) * P.eval (z * om n m)‖ := by
          congr 1
          exact (eval_sum_eq P n hn hdeg z).symm
    _ ≤ ∑ m ∈ Finset.range (2 * n), ‖W n (om n m) * P.eval (z * om n m)‖ := by
          exact norm_sum_le (Finset.range (2 * n))
            (fun m => W n (om n m) * P.eval (z * om n m))
    _ ≤ ∑ m ∈ Finset.range (2 * n), ‖W n (om n m)‖ * M := by
          apply Finset.sum_le_sum
          intro m hm
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hM (z * om n m) (hzom m hm)) (norm_nonneg (W n (om n m)))
    _ = (∑ m ∈ Finset.range (2 * n), ‖W n (om n m)‖) * M := by
          rw [Finset.sum_mul]
    _ = (n : ℝ) * M := by
          rw [sum_norm_W n hn]

end weight



end BernsteinPoly

/-! The statement of Bernstein's inequality as fixed by the parent agent. -/

open BernsteinPoly

lemma bernstein_poly (P : ℂ[X]) (n : ℕ) (hdeg : P.natDegree ≤ n)
    (M : ℝ) (hM : ∀ w : ℂ, ‖w‖ = 1 → ‖Polynomial.eval w P‖ ≤ M) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖Polynomial.eval z (Polynomial.derivative P)‖ ≤ (n : ℝ) * M := by
  by_cases hn : 0 < n
  · exact BernsteinPoly.bernstein_core P n hn hdeg M hM z hz
  · have hn0 : n = 0 := by omega
    subst n
    have hP : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hdeg
    rw [hP]
    simp [Polynomial.derivative_C, Polynomial.eval_zero]
