import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.primitive_factor_coprime
import Submission.Commons.NumberTheory.DirichletCharacter.primitive_factor_coprime_order
import Submission.Commons.NumberTheory.DirichletCharacter.weil_bound_poly
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_moment_prime
import Submission.Commons.NumberTheory.DirichletCharacter.charSum_product_poly_weil
import Submission.Commons.NumberTheory.DirichletCharacter.lcm_gcd_count_sqfree
import Submission.Commons.Algebra.Polynomial.mult_modEq_of_const_mul_pow

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.DirichletCharacter

/-! ## Stage 1: expansion of the fourth moment for a general modulus -/

lemma chi_conj_eq_pow_pred {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hm : 2 ≤ orderOf χ) (y : ZMod q) :
    (starRingEnd ℂ) (χ y) = χ y ^ (orderOf χ - 1) := by
  have hm1 : orderOf χ - 1 ≠ 0 := by omega
  by_cases hunit : IsUnit y
  · have hpow1 : (χ y) ^ orderOf χ = 1 := by
      have hp : χ ^ orderOf χ = (1 : DirichletCharacter ℂ q) := pow_orderOf_eq_one χ
      have h2 : (χ ^ orderOf χ) y = 1 := by rw [hp, MulChar.one_apply hunit]
      rwa [MulChar.pow_apply' χ (by omega : orderOf χ ≠ 0) y] at h2
    have hconj : (starRingEnd ℂ) (χ y) = (χ y)⁻¹ := by
      rw [show (starRingEnd ℂ) (χ y) = star (χ y) from rfl, MulChar.star_apply' χ y,
        MulChar.inv_apply_eq_inv' χ y]
    have hpow : χ y ^ (orderOf χ - 1) = (χ y)⁻¹ := by
      refine eq_inv_of_mul_eq_one_right ?_
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (orderOf_pos χ), hpow1]
    rw [hconj, hpow]
  · rw [MulChar.map_nonunit χ hunit, map_zero, zero_pow hm1]

lemma chi_mul_conj_eq_q {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hm : 2 ≤ orderOf χ) (f g : Polynomial (ZMod q)) (x : ZMod q) :
    χ (f.eval x) * (starRingEnd ℂ) (χ (g.eval x))
      = χ ((f * g ^ (orderOf χ - 1)).eval x) := by
  rw [Polynomial.eval_mul, Polynomial.eval_pow, map_mul, map_pow]
  rw [chi_conj_eq_pow_pred χ hm (g.eval x)]

lemma S_pow_eq' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (H r m : ℕ) :
    (∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)) ^ r
      = ∑ f : Fin r → Fin H, χ ((Pf q H r f).eval (m : ZMod q)) := by
  rw [sum_Ioc_eq_sum_fin]
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro f _
  rw [← map_prod]
  congr 1
  unfold Pf
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

lemma S_conj_pow_eq' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (H r m : ℕ) :
    (starRingEnd ℂ) ((∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)) ^ r)
      = ∑ g : Fin r → Fin H, (starRingEnd ℂ) (χ ((Pf q H r g).eval (m : ZMod q))) := by
  rw [S_pow_eq', map_sum]

lemma Smulconj_eq' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (H r m : ℕ) :
    (∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)) ^ r *
      (starRingEnd ℂ) ((∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)) ^ r)
      = ∑ f : Fin r → Fin H, ∑ g : Fin r → Fin H,
          χ ((Pf q H r f).eval (m : ZMod q)) *
            (starRingEnd ℂ) (χ ((Pf q H r g).eval (m : ZMod q))) := by
  rw [S_conj_pow_eq', S_pow_eq', Finset.sum_mul_sum]

noncomputable def Tgq {q : ℕ} [NeZero q] (H r : ℕ) (χ : DirichletCharacter ℂ q)
    (f g : Fin r → Fin H) : ℂ :=
  ∑ x : ZMod q, χ ((Pf q H r f * (Pf q H r g) ^ (orderOf χ - 1)).eval x)

lemma Z_eq' {q : ℕ} [NeZero q] (H r : ℕ) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    (∑ m ∈ Finset.range q, (∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)) ^ r *
        (starRingEnd ℂ) ((∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)) ^ r))
      = ∑ f : Fin r → Fin H, ∑ g : Fin r → Fin H, Tgq H r χ f g := by
  have hm2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  simp_rw [Smulconj_eq' χ H r]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro f _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro g _
  simp only [Tgq]
  simp_rw [chi_mul_conj_eq_q χ hm2 (Pf q H r f) (Pf q H r g)]
  exact zmod_sum_range_eq q (fun z : ZMod q =>
    χ (Polynomial.eval z (Pf q H r f * (Pf q H r g) ^ (orderOf χ - 1))))



lemma roots_count_prod_X_add_C' {K : Type*} [Field K] [DecidableEq K]
    {ι : Type*} [Fintype ι] (a : ι → K) (x : K) :
    (∏ i, (Polynomial.X + Polynomial.C (a i))).roots.count (-x)
      = (Finset.univ.filter (fun i => a i = x)).card := by
  classical
  have hne : (∏ i, (Polynomial.X + Polynomial.C (a i))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (Polynomial.monic_X_add_C (a i)).ne_zero)
  rw [Polynomial.roots_prod (fun i => Polynomial.X + Polynomial.C (a i)) Finset.univ hne]
  simp only [Polynomial.roots_X_add_C]
  rw [Multiset.bind_singleton, Multiset.count_map, ← Finset.filter_val]
  congr 1; ext i; simp [eq_comm, neg_inj]

/-- Version of `mult_modEq_of_const_mul_pow` with exponent `m-1` and modulus `mp` dividing `m`. -/
theorem mult_modEq_pow {K : Type*} [Field K] [DecidableEq K] {r m mp : ℕ} (hmp : 2 ≤ mp)
    (hm1 : 1 ≤ m) (hmdvd : mp ∣ m) (a b : Fin r → K) {c : K} {Q : Polynomial K}
    (h : (∏ i, (Polynomial.X + Polynomial.C (a i)))
       * (∏ i, (Polynomial.X + Polynomial.C (b i))) ^ (m - 1)
       = Polynomial.C c * Q ^ mp) :
    ∀ x : K, (Finset.univ.filter (fun i => a i = x)).card % mp
           = (Finset.univ.filter (fun i => b i = x)).card % mp := by
  classical
  intro x
  set na : ℕ := (Finset.univ.filter (fun i => a i = x)).card with hna
  set nb : ℕ := (Finset.univ.filter (fun i => b i = x)).card with hnb
  set A : Polynomial K := ∏ i, (Polynomial.X + Polynomial.C (a i)) with hA
  set B : Polynomial K := ∏ i, (Polynomial.X + Polynomial.C (b i)) with hB
  have hA0 : A ≠ 0 := by
    rw [hA]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => (Polynomial.monic_X_add_C (a i)).ne_zero)
  have hB0 : B ≠ 0 := by
    rw [hB]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => (Polynomial.monic_X_add_C (b i)).ne_zero)
  have hAB0 : A * B ^ (m - 1) ≠ 0 := mul_ne_zero hA0 (pow_ne_zero _ hB0)
  have hc : c ≠ 0 := by
    intro hc0
    apply hAB0
    rw [h, hc0, Polynomial.C_0, zero_mul]
  have hL : (A * B ^ (m - 1)).roots = A.roots + (m - 1) • B.roots := by
    rw [Polynomial.roots_mul hAB0, Polynomial.roots_pow]
  have hR : (Polynomial.C c * Q ^ mp).roots = mp • Q.roots := by
    rw [Polynomial.roots_C_mul (Q ^ mp) hc, Polynomial.roots_pow]
  have hmult : A.roots + (m - 1) • B.roots = mp • Q.roots := by
    rw [← hL, ← hR, h]
  have hcount := congrArg (fun s : Multiset K => s.count (-x)) hmult
  rw [Multiset.count_add, Multiset.count_nsmul, Multiset.count_nsmul] at hcount
  rw [hA, hB, roots_count_prod_X_add_C', roots_count_prod_X_add_C'] at hcount
  rw [← hna, ← hnb] at hcount
  have hmb : (m - 1) * nb + nb = m * nb := by
    conv_rhs => rw [show m = (m - 1) + 1 from (Nat.sub_add_cancel hm1).symm]
    rw [Nat.add_mul, one_mul]
  have key : na + m * nb = mp * (Q.roots.count (-x)) + nb := by
    rw [← hmb, ← add_assoc, hcount]
  have hmod : na % mp = nb % mp := by
    have hA2 : (na + m * nb) % mp = na % mp := by
      obtain ⟨k, rfl⟩ := hmdvd
      rw [show na + mp * k * nb = na + (nb * k) * mp by ring,
        Nat.add_mul_mod_self_right]
    have hB2 : (mp * (Q.roots.count (-x)) + nb) % mp = nb % mp := by
      rw [Nat.mul_add_mod]
    rw [← hA2, key, hB2]
  exact hmod

lemma card_filter_fin2 {K : Type*} [DecidableEq K] (f : Fin 2 → K) (x : K) :
    (Finset.univ.filter (fun i : Fin 2 => f i = x)).card
      = (if f 0 = x then 1 else 0) + (if f 1 = x then 1 else 0) := by
  rw [Finset.card_filter, Fin.sum_univ_two]

lemma mod_two_ne_one {m : ℕ} (hm : 2 ≤ m) : 2 % m ≠ 1 % m := by
  have h1 : 1 % m = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  rcases eq_or_lt_of_le hm with h | h
  · subst h; norm_num
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

lemma zero_mod_ne_one {m : ℕ} (hm : 2 ≤ m) : 0 % m ≠ 1 % m := by
  have h1 : 1 % m = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1, Nat.zero_mod]; omega

lemma xor_of_cnt_mod {m : ℕ} (hm : 2 ≤ m) {p q : Prop} [Decidable p] [Decidable q]
    (h : ((if p then 1 else 0) + (if q then 1 else 0)) % m = 1 % m) :
    (p ∧ ¬ q) ∨ (q ∧ ¬ p) := by
  by_cases hp : p <;> by_cases hq : q
  · exfalso
    rw [if_pos hp, if_pos hq] at h
    exact mod_two_ne_one hm h
  · exact Or.inl ⟨hp, hq⟩
  · exact Or.inr ⟨hq, hp⟩
  · exfalso
    rw [if_neg hp, if_neg hq] at h
    simp only [add_zero] at h
    exact zero_mod_ne_one hm h

/-- Congruence of fiber cardinalities for two maps `Fin 2 → K` forces either constancy or
equality of the elementary symmetric functions. -/
lemma type_of_multicongr {K : Type*} [Field K] [DecidableEq K] {m : ℕ} (hm : 2 ≤ m)
    (a b : Fin 2 → K)
    (h : ∀ x, (Finset.univ.filter (fun i => a i = x)).card % m
            = (Finset.univ.filter (fun i => b i = x)).card % m) :
    (a 0 = a 1 ∧ b 0 = b 1) ∨ (a 0 + a 1 = b 0 + b 1 ∧ a 0 * a 1 = b 0 * b 1) := by
  have hc1 : 1 % m = 1 := Nat.mod_eq_of_lt (by omega)
  by_cases hab : a 0 = a 1
  · by_cases hcd : b 0 = b 1
    · exact Or.inl ⟨hab, hcd⟩
    · exfalso
      -- cardB (b 0) = 1
      have hb0 : (Finset.univ.filter (fun i : Fin 2 => b i = b 0)).card = 1 := by
        rw [card_filter_fin2, if_pos rfl, if_neg (fun hh => hcd hh.symm)]
      have hA : (Finset.univ.filter (fun i : Fin 2 => a i = b 0)).card
          = 2 * (if a 0 = b 0 then 1 else 0) := by
        rw [card_filter_fin2, ← hab]
        by_cases hh : a 0 = b 0 <;> simp [hh]
      have h1 := h (b 0)
      rw [hb0, hc1, hA] at h1
      by_cases hh : a 0 = b 0
      · rw [if_pos hh] at h1
        exact mod_two_ne_one hm (by rw [hc1]; exact h1)
      · rw [if_neg hh] at h1
        simp only [mul_zero] at h1
        exact zero_mod_ne_one hm (by rw [hc1]; exact h1)
  · -- a nonconstant
    have ha0 : (Finset.univ.filter (fun i : Fin 2 => a i = a 0)).card = 1 := by
      rw [card_filter_fin2, if_pos rfl, if_neg (fun hh => hab hh.symm)]
    have ha1 : (Finset.univ.filter (fun i : Fin 2 => a i = a 1)).card = 1 := by
      rw [card_filter_fin2, if_neg hab, if_pos rfl, zero_add]
    have hb0 := xor_of_cnt_mod hm (p := b 0 = a 0) (q := b 1 = a 0)
      (by rw [← card_filter_fin2]; rw [← h (a 0), ha0, hc1])
    have hb1 := xor_of_cnt_mod hm (p := b 0 = a 1) (q := b 1 = a 1)
      (by rw [← card_filter_fin2]; rw [← h (a 1), ha1, hc1])
    rcases hb0 with ⟨e1, e1'⟩ | ⟨e1, e1'⟩
    · -- b 0 = a 0
      have e2 : b 1 = a 1 := by
        rcases hb1 with ⟨f1, f2⟩ | ⟨f1, f2⟩
        · exfalso; exact hab (e1.symm.trans f1)
        · exact f1
      exact Or.inr ⟨by rw [e1, e2], by rw [e1, e2]⟩
    · -- b 1 = a 0
      have e0 : b 0 = a 1 := by
        rcases hb1 with ⟨f1, f2⟩ | ⟨f1, f2⟩
        · exact f1
        · exfalso; exact hab (e1.symm.trans f1)
      exact Or.inr ⟨by rw [e0, e1, add_comm], by rw [e0, e1, mul_comm]⟩




noncomputable def WL (q a b c d : ℕ) : ℝ :=
  Real.sqrt ((Eg0 q a b c d).lcm (Eg1 q a b c d))

lemma Eg0_dvd {q q' a b c d : ℕ} (h : q' ∣ q) : Eg0 q' a b c d ∣ Eg0 q a b c d := by
  unfold Eg0
  exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (Nat.dvd_trans (Nat.gcd_dvd_right _ _) h)

lemma Eg1_dvd {q q' a b c d : ℕ} (h : q' ∣ q) : Eg1 q' a b c d ∣ Eg1 q a b c d := by
  unfold Eg1
  exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (Nat.dvd_trans (Nat.gcd_dvd_right _ _) h)

lemma Eg0_pos {q a b c d : ℕ} (hq : q ≠ 0) : 0 < Eg0 q a b c d := by
  unfold Eg0
  exact Nat.pos_of_ne_zero (fun h0 => hq (Nat.eq_zero_of_gcd_eq_zero_right h0))

lemma Eg1_pos {q a b c d : ℕ} (hq : q ≠ 0) : 0 < Eg1 q a b c d := by
  unfold Eg1
  exact Nat.pos_of_ne_zero (fun h0 => hq (Nat.eq_zero_of_gcd_eq_zero_right h0))

lemma WL_mono {q q' a b c d : ℕ} (h : q' ∣ q) (hq : q ≠ 0) : WL q' a b c d ≤ WL q a b c d := by
  unfold WL
  apply Real.sqrt_le_sqrt
  have h3 : Nat.lcm (Eg0 q' a b c d) (Eg1 q' a b c d) ∣ Nat.lcm (Eg0 q a b c d) (Eg1 q a b c d) :=
    Nat.lcm_dvd (Nat.dvd_trans (Eg0_dvd h) (Nat.dvd_lcm_left _ _))
      (Nat.dvd_trans (Eg1_dvd h) (Nat.dvd_lcm_right _ _))
  have hpos : 0 < Nat.lcm (Eg0 q a b c d) (Eg1 q a b c d) :=
    lt_of_lt_of_le (Eg0_pos hq) (Nat.le_lcm_left (Eg0 q a b c d) (Eg1_pos hq))
  have hle : Nat.lcm (Eg0 q' a b c d) (Eg1 q' a b c d)
      ≤ Nat.lcm (Eg0 q a b c d) (Eg1 q a b c d) := Nat.le_of_dvd hpos h3
  exact_mod_cast hle

lemma dvd_Eg0 {p q a b c d : ℕ} (hpq : p ∣ q) :
    p ∣ Eg0 q a b c d ↔ ((p:ℤ) ∣ (a:ℤ) - (b:ℤ) ∧ (p:ℤ) ∣ (c:ℤ) - (d:ℤ)) := by
  unfold Eg0
  rw [Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨h1, _⟩
    have h3 : (p:ℤ) ∣ ((Int.gcd ((a:ℤ)-(b:ℤ)) ((c:ℤ)-(d:ℤ)) : ℕ) : ℤ) := by exact_mod_cast h1
    exact ⟨h3.trans (Int.gcd_dvd_left _ _), h3.trans (Int.gcd_dvd_right _ _)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Int.dvd_gcd h1 h2, hpq⟩

lemma dvd_Eg1 {p q a b c d : ℕ} (hpq : p ∣ q) :
    p ∣ Eg1 q a b c d ↔
      ((p:ℤ) ∣ (((a:ℤ)+(b:ℤ)) - ((c:ℤ)+(d:ℤ))) ∧
        (p:ℤ) ∣ ((a:ℤ)*(b:ℤ) - (c:ℤ)*(d:ℤ))) := by
  unfold Eg1
  rw [Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨h1, _⟩
    have h3 : (p:ℤ) ∣ ((Int.gcd (((a:ℤ)+(b:ℤ))-((c:ℤ)+(d:ℤ)))
        ((a:ℤ)*(b:ℤ)-(c:ℤ)*(d:ℤ)) : ℕ) : ℤ) := by exact_mod_cast h1
    exact ⟨h3.trans (Int.gcd_dvd_left _ _), h3.trans (Int.gcd_dvd_right _ _)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Int.dvd_gcd h1 h2, hpq⟩

/-! ## Character power with a shifted exponent -/

lemma char_pow_eq_pow_orderOf {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {m : ℕ}
    (hmd : orderOf χ ∣ m) (hm : m ≠ 0) (x : ZMod q) : χ x ^ m = χ x ^ orderOf χ := by
  by_cases hunit : IsUnit x
  · obtain ⟨k, rfl⟩ := hmd
    rw [pow_mul]
    have h1 : (χ x) ^ orderOf χ = 1 := by
      have hp : χ ^ orderOf χ = (1 : DirichletCharacter ℂ q) := pow_orderOf_eq_one χ
      have h2 := congrArg (fun f : DirichletCharacter ℂ q => f x) hp
      rw [MulChar.pow_apply' χ (orderOf_pos χ).ne'] at h2
      rw [h2, MulChar.one_apply hunit]
    rw [h1, one_pow]
  · rw [MulChar.map_nonunit χ hunit]
    have ho : orderOf χ ≠ 0 := (orderOf_pos χ).ne'
    rw [zero_pow hm, zero_pow ho]

lemma char_pow_pred_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {m : ℕ}
    (hmd : orderOf χ ∣ m) (hm : m ≠ 0) (hm2 : 2 ≤ m) (hχ : χ ≠ 1) (x : ZMod q) :
    χ x ^ (m - 1) = χ x ^ (orderOf χ - 1) := by
  have ho2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  have hle : orderOf χ ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hmd
  by_cases hunit : IsUnit x
  · have ha0 : χ x ≠ 0 := by
      rw [← hunit.unit_spec, ← MulChar.coe_toUnitHom χ hunit.unit]
      exact (χ.toUnitHom hunit.unit).ne_zero
    have key : χ x ^ m = χ x ^ orderOf χ := char_pow_eq_pow_orderOf χ hmd hm x
    have hsub : χ x ^ (m - orderOf χ) = 1 := by
      have h : χ x ^ orderOf χ * χ x ^ (m - orderOf χ) = χ x ^ orderOf χ * 1 := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' hle, key]
      exact mul_left_cancel₀ (pow_ne_zero _ ha0) h
    calc χ x ^ (m - 1) = χ x ^ ((orderOf χ - 1) + (m - orderOf χ)) := by
          rw [show (orderOf χ - 1) + (m - orderOf χ) = m - 1 by omega]
      _ = χ x ^ (orderOf χ - 1) * χ x ^ (m - orderOf χ) := pow_add _ _ _
      _ = χ x ^ (orderOf χ - 1) := by rw [hsub, mul_one]
  · rw [MulChar.map_nonunit χ hunit]
    rw [zero_pow (by omega : m - 1 ≠ 0), zero_pow (by omega : orderOf χ - 1 ≠ 0)]

/-! ## `lcm` arithmetic for the induction -/

lemma lcm_mul_left_of_not_dvd {p a b : ℕ} (hp : p.Prime) (hb : ¬ p ∣ b) :
    Nat.lcm (a * p) b = p * Nat.lcm a b := by
  have hg : Nat.gcd (a*p) b = Nat.gcd a b := by
    apply Nat.dvd_antisymm
    · apply Nat.dvd_gcd
      · have h1 : Nat.gcd (a*p) b ∣ a * p := Nat.gcd_dvd_left _ _
        have h2 : Nat.gcd (a*p) b ∣ b := Nat.gcd_dvd_right _ _
        have hpnd : ¬ p ∣ Nat.gcd (a*p) b := fun h => hb (dvd_trans h h2)
        exact ((hp.coprime_iff_not_dvd).mpr hpnd).symm.dvd_of_dvd_mul_right h1
      · exact Nat.gcd_dvd_right _ _
    · exact Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_mul_right a p))
        (Nat.gcd_dvd_right _ _)
  rw [Nat.lcm, Nat.lcm, hg]
  rw [show a * p * b = p * (a * b) by ring,
    Nat.mul_div_assoc p (dvd_mul_of_dvd_left (Nat.gcd_dvd_left a b) b)]

/-! ## Value of the CRT components -/

lemma isUnit_cast_iff {p v : ℕ} [NeZero p] [NeZero v] (hcop : p.Coprime v) (w : ZMod (p*v)) :
    IsUnit w ↔ IsUnit (w.cast : ZMod p) ∧ IsUnit (w.cast : ZMod v) := by
  have h1 : IsUnit w ↔ Nat.Coprime w.val (p*v) := by
    simpa using ZMod.isUnit_iff_coprime w.val (p*v)
  have h2 : IsUnit (w.cast : ZMod p) ↔ Nat.Coprime w.val p := by
    rw [ZMod.cast_eq_val]; exact ZMod.isUnit_iff_coprime w.val p
  have h3 : IsUnit (w.cast : ZMod v) ↔ Nat.Coprime w.val v := by
    rw [ZMod.cast_eq_val]; exact ZMod.isUnit_iff_coprime w.val v
  rw [h1, h2, h3, Nat.coprime_mul_iff_right]

lemma chi_eq_factors {p v : ℕ} [NeZero p] [NeZero v] (hcop : p.Coprime v)
    (χ : DirichletCharacter ℂ (p*v)) (w : ZMod (p*v)) :
    χ w = factorLeft hcop χ (w.cast : ZMod p) * factorRight hcop χ (w.cast : ZMod v) := by
  by_cases hw : IsUnit w
  · obtain ⟨u, rfl⟩ := hw
    have h := congrArg (fun f : DirichletCharacter ℂ (p*v) => f (↑u : ZMod (p*v)))
      (factor_eq hcop χ)
    rw [MulChar.mul_apply] at h
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd _ _ u,
      DirichletCharacter.changeLevel_eq_cast_of_dvd _ _ u] at h
    exact h.symm
  · rw [MulChar.map_nonunit χ hw]
    rcases (not_and_or.mp (fun hc => hw ((isUnit_cast_iff hcop w).mpr hc))) with h | h
    · rw [MulChar.map_nonunit _ h, zero_mul]
    · rw [MulChar.map_nonunit _ h, mul_zero]

/-! ## The per-prime estimates -/

lemma prime_good {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) {m : ℕ}
    (hm1 : 2 ≤ m) (a b c d : ℕ)
    (hgood : ∀ c₀ : ZMod p, ∀ Q : Polynomial (ZMod p),
      (Polynomial.X + Polynomial.C (a:ZMod p)) * (Polynomial.X + Polynomial.C (b:ZMod p)) *
        ((Polynomial.X + Polynomial.C (c:ZMod p)) * (Polynomial.X + Polynomial.C (d:ZMod p)))
          ^ (m - 1) ≠ Polynomial.C c₀ * Q ^ (orderOf χ)) :
    ‖∑ y : ZMod p, χ ((y + (a:ZMod p)) * (y + (b:ZMod p)) *
        ((y + (c:ZMod p)) * (y + (d:ZMod p))) ^ (m - 1))‖ ≤ 4 * Real.sqrt (p : ℝ) := by
  set A : Polynomial (ZMod p) := (Polynomial.X + Polynomial.C (a:ZMod p)) *
    (Polynomial.X + Polynomial.C (b:ZMod p)) with hA
  set B : Polynomial (ZMod p) := (Polynomial.X + Polynomial.C (c:ZMod p)) *
    (Polynomial.X + Polynomial.C (d:ZMod p)) with hB
  set F : Polynomial (ZMod p) := A * B ^ (m - 1) with hF
  have hA0 : A ≠ 0 := by
    rw [hA]; exact mul_ne_zero (Polynomial.monic_X_add_C _).ne_zero (Polynomial.monic_X_add_C _).ne_zero
  have hB0 : B ≠ 0 := by
    rw [hB]; exact mul_ne_zero (Polynomial.monic_X_add_C _).ne_zero (Polynomial.monic_X_add_C _).ne_zero
  have hF0 : F ≠ 0 := by
    rw [hF]; exact mul_ne_zero hA0 (pow_ne_zero _ hB0)
  have heval : ∀ y : ZMod p, F.eval y = (y + (a:ZMod p)) * (y + (b:ZMod p)) *
      ((y + (c:ZMod p)) * (y + (d:ZMod p))) ^ (m - 1) := by
    intro y; rw [hF, hA, hB]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
  have hnd : ∀ c₀ : ZMod p, ∀ Q : Polynomial (ZMod p), F ≠ Polynomial.C c₀ * Q ^ (orderOf χ) := by
    intro c₀ Q hc
    exact hgood c₀ Q (by rw [hF, hA, hB]; exact hc)
  have hdegA : A.natDegree = 2 := by
    rw [hA, Polynomial.natDegree_mul (Polynomial.monic_X_add_C _).ne_zero
      (Polynomial.monic_X_add_C _).ne_zero, Polynomial.natDegree_X_add_C, Polynomial.natDegree_X_add_C]
  have hdegB : B.natDegree = 2 := by
    rw [hB, Polynomial.natDegree_mul (Polynomial.monic_X_add_C _).ne_zero
      (Polynomial.monic_X_add_C _).ne_zero, Polynomial.natDegree_X_add_C, Polynomial.natDegree_X_add_C]
  have hd : 1 ≤ F.natDegree := by
    rw [hF, Polynomial.natDegree_mul hA0 (pow_ne_zero _ hB0), Polynomial.natDegree_pow,
      hdegA, hdegB]
    linarith only [hm1]
  have hb := weil_bound_poly p χ hχ F hF0 hd hnd
  have hcard : (F.rootSet (AlgebraicClosure (ZMod p))).ncard ≤ 4 := by
    have h := ncard_rootSet_mul_pow_le p A B (m - 1) (by omega)
    rw [hdegA, hdegB] at h
    omega
  have heq : (∑ y : ZMod p, χ ((y + (a:ZMod p)) * (y + (b:ZMod p)) *
      ((y + (c:ZMod p)) * (y + (d:ZMod p))) ^ (m - 1))) = ∑ y : ZMod p, χ (F.eval y) := by
    apply Finset.sum_congr rfl; intro y _; rw [heval]
  rw [heq]
  calc ‖∑ y : ZMod p, χ (F.eval y)‖
      ≤ ((F.rootSet (AlgebraicClosure (ZMod p))).ncard : ℝ) * Real.sqrt (p : ℝ) := hb
    _ ≤ 4 * Real.sqrt (p : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact_mod_cast hcard

lemma prime_bad {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) {m : ℕ}
    (hm1 : 1 ≤ m) (hmd : orderOf χ ∣ m) {q : ℕ} (hpq : p ∣ q) (a b c d : ℕ)
    (hbad : ∃ c₀ : ZMod p, ∃ Q : Polynomial (ZMod p),
      (Polynomial.X + Polynomial.C (a:ZMod p)) * (Polynomial.X + Polynomial.C (b:ZMod p)) *
        ((Polynomial.X + Polynomial.C (c:ZMod p)) * (Polynomial.X + Polynomial.C (d:ZMod p)))
          ^ (m - 1) = Polynomial.C c₀ * Q ^ (orderOf χ)) :
    p ∣ Eg0 q a b c d ∨ p ∣ Eg1 q a b c d := by
  obtain ⟨c₀, Q, hQ⟩ := hbad
  have hm2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  set f : Fin 2 → ZMod p := fun i => if i = 0 then (a:ZMod p) else (b:ZMod p) with hf
  set g : Fin 2 → ZMod p := fun i => if i = 0 then (c:ZMod p) else (d:ZMod p) with hg
  have hf0 : f 0 = (a:ZMod p) := by simp [hf]
  have hf1 : f 1 = (b:ZMod p) := by simp [hf]
  have hg0 : g 0 = (c:ZMod p) := by simp [hg]
  have hg1 : g 1 = (d:ZMod p) := by simp [hg]
  have hprod : (∏ i : Fin 2, (Polynomial.X + Polynomial.C (f i))) *
      (∏ i : Fin 2, (Polynomial.X + Polynomial.C (g i))) ^ (m - 1)
      = Polynomial.C c₀ * Q ^ (orderOf χ) := by
    rw [Fin.prod_univ_two, Fin.prod_univ_two, hf0, hf1, hg0, hg1]
    exact hQ
  have hmul := mult_modEq_pow (K := ZMod p) hm2 hm1 hmd f g hprod
  have htype := type_of_multicongr hm2 f g hmul
  rw [hf0, hf1, hg0, hg1] at htype
  have key : ∀ x y : ℕ, ((x:ZMod p) = (y:ZMod p)) → (p:ℤ) ∣ (x:ℤ) - (y:ℤ) := by
    intro x y hxy
    have h := ((ZMod.natCast_eq_natCast_iff x y p).mp hxy).dvd
    have h' : (p:ℤ) ∣ -((y:ℤ) - (x:ℤ)) := dvd_neg.mpr h
    simpa using h'
  rcases htype with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · left
    rw [dvd_Eg0 hpq]
    exact ⟨key a b e1, key c d e2⟩
  · right
    rw [dvd_Eg1 hpq]
    constructor
    · have h := key (a+b) (c+d) (by push_cast; exact e1)
      simpa using h
    · have h := key (a*b) (c*d) (by push_cast; exact e2)
      simpa using h

lemma split_sum {p v : ℕ} [NeZero p] [NeZero v] (hcop : p.Coprime v)
    (χ : DirichletCharacter ℂ (p*v)) (m a b c d : ℕ) :
    (∑ x : ZMod (p*v), χ ((x + (a:ZMod (p*v))) * (x + (b:ZMod (p*v))) *
        ((x + (c:ZMod (p*v))) * (x + (d:ZMod (p*v)))) ^ (m-1)))
    = (∑ y : ZMod p, factorLeft hcop χ ((y + (a:ZMod p)) * (y + (b:ZMod p)) *
        ((y + (c:ZMod p)) * (y + (d:ZMod p))) ^ (m-1)))
      * (∑ z : ZMod v, factorRight hcop χ ((z + (a:ZMod v)) * (z + (b:ZMod v)) *
        ((z + (c:ZMod v)) * (z + (d:ZMod v))) ^ (m-1))) := by
  have hcastp : ∀ x : ZMod (p*v),
      (((x + (a:ZMod (p*v))) * (x + (b:ZMod (p*v))) *
        ((x + (c:ZMod (p*v))) * (x + (d:ZMod (p*v)))) ^ (m-1)).cast : ZMod p)
      = ((x.cast : ZMod p) + (a:ZMod p)) * ((x.cast : ZMod p) + (b:ZMod p)) *
        (((x.cast : ZMod p) + (c:ZMod p)) * ((x.cast : ZMod p) + (d:ZMod p))) ^ (m-1) := by
    intro x
    simp only [ZMod.cast_mul (Nat.dvd_mul_right p v), ZMod.cast_add (Nat.dvd_mul_right p v),
      ZMod.cast_pow (Nat.dvd_mul_right p v), ZMod.cast_natCast (Nat.dvd_mul_right p v)]
  have hcastv : ∀ x : ZMod (p*v),
      (((x + (a:ZMod (p*v))) * (x + (b:ZMod (p*v))) *
        ((x + (c:ZMod (p*v))) * (x + (d:ZMod (p*v)))) ^ (m-1)).cast : ZMod v)
      = ((x.cast : ZMod v) + (a:ZMod v)) * ((x.cast : ZMod v) + (b:ZMod v)) *
        (((x.cast : ZMod v) + (c:ZMod v)) * ((x.cast : ZMod v) + (d:ZMod v))) ^ (m-1) := by
    intro x
    simp only [ZMod.cast_mul (Nat.dvd_mul_left v p), ZMod.cast_add (Nat.dvd_mul_left v p),
      ZMod.cast_pow (Nat.dvd_mul_left v p), ZMod.cast_natCast (Nat.dvd_mul_left v p)]
  simp_rw [chi_eq_factors hcop χ, hcastp, hcastv]
  have hstep := Fintype.sum_equiv (crtE hcop).toEquiv
    (fun x : ZMod (p*v) => factorLeft hcop χ (((x.cast : ZMod p) + (a:ZMod p)) *
        ((x.cast : ZMod p) + (b:ZMod p)) * (((x.cast : ZMod p) + (c:ZMod p)) *
        ((x.cast : ZMod p) + (d:ZMod p))) ^ (m-1)) *
      factorRight hcop χ (((x.cast : ZMod v) + (a:ZMod v)) * ((x.cast : ZMod v) + (b:ZMod v)) *
        (((x.cast : ZMod v) + (c:ZMod v)) * ((x.cast : ZMod v) + (d:ZMod v))) ^ (m-1)))
    (fun w : ZMod p × ZMod v => factorLeft hcop χ ((w.1 + (a:ZMod p)) * (w.1 + (b:ZMod p)) *
        ((w.1 + (c:ZMod p)) * (w.1 + (d:ZMod p))) ^ (m-1)) *
      factorRight hcop χ ((w.2 + (a:ZMod v)) * (w.2 + (b:ZMod v)) *
        ((w.2 + (c:ZMod v)) * (w.2 + (d:ZMod v))) ^ (m-1)))
    (fun x => by
      have h1 : ((crtE hcop).toEquiv x).1 = x.cast := crtE_fst hcop x
      have h2 : ((crtE hcop).toEquiv x).2 = x.cast := crtE_snd hcop x
      rw [h1, h2])
  rw [hstep, Fintype.sum_prod_type, ← Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)
    (f := fun y : ZMod p => factorLeft hcop χ ((y + (a:ZMod p)) * (y + (b:ZMod p)) *
        ((y + (c:ZMod p)) * (y + (d:ZMod p))) ^ (m-1)))
    (g := fun z : ZMod v => factorRight hcop χ ((z + (a:ZMod v)) * (z + (b:ZMod v)) *
        ((z + (c:ZMod v)) * (z + (d:ZMod v))) ^ (m-1)))]

lemma Eg0_mul {p v a b c d : ℕ} (hcop : p.Coprime v) :
    Eg0 (p*v) a b c d
      = Nat.gcd (Int.gcd ((a:ℤ)-(b:ℤ)) ((c:ℤ)-(d:ℤ))) p * Eg0 v a b c d := by
  unfold Eg0
  rw [Nat.Coprime.gcd_mul _ hcop]

lemma Eg1_mul {p v a b c d : ℕ} (hcop : p.Coprime v) :
    Eg1 (p*v) a b c d
      = Nat.gcd (Int.gcd (((a:ℤ)+(b:ℤ))-((c:ℤ)+(d:ℤ)))
          ((a:ℤ)*(b:ℤ)-(c:ℤ)*(d:ℤ))) p * Eg1 v a b c d := by
  unfold Eg1
  rw [Nat.Coprime.gcd_mul _ hcop]

lemma lcm_mul_right_of_not_dvd {p a b : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) :
    Nat.lcm a (b * p) = p * Nat.lcm a b := by
  rw [Nat.lcm_comm, lcm_mul_left_of_not_dvd hp ha, Nat.lcm_comm]

lemma lcm_Eg_step {p v a b c d : ℕ} (hp : p.Prime) (hcop : p.Coprime v)
    (hdiv : p ∣ Nat.lcm (Eg0 (p*v) a b c d) (Eg1 (p*v) a b c d)) :
    p * Nat.lcm (Eg0 v a b c d) (Eg1 v a b c d)
      = Nat.lcm (Eg0 (p*v) a b c d) (Eg1 (p*v) a b c d) := by
  have hpv : ¬ p ∣ v := (hp.coprime_iff_not_dvd).mp hcop
  have hpd0 : ¬ p ∣ Eg0 v a b c d := fun h => hpv (dvd_trans h (Nat.gcd_dvd_right _ _))
  have hpd1 : ¬ p ∣ Eg1 v a b c d := fun h => hpv (dvd_trans h (Nat.gcd_dvd_right _ _))
  set X := Int.gcd ((a:ℤ)-(b:ℤ)) ((c:ℤ)-(d:ℤ)) with hX
  set Y := Int.gcd (((a:ℤ)+(b:ℤ))-((c:ℤ)+(d:ℤ))) ((a:ℤ)*(b:ℤ)-(c:ℤ)*(d:ℤ)) with hY
  have h0 : Eg0 (p*v) a b c d = Nat.gcd X p * Eg0 v a b c d := by rw [hX]; exact Eg0_mul hcop
  have h1 : Eg1 (p*v) a b c d = Nat.gcd Y p * Eg1 v a b c d := by rw [hY]; exact Eg1_mul hcop
  have he0 : Nat.gcd X p = 1 ∨ Nat.gcd X p = p := (Nat.dvd_prime hp).mp (Nat.gcd_dvd_right _ _)
  have he1 : Nat.gcd Y p = 1 ∨ Nat.gcd Y p = p := (Nat.dvd_prime hp).mp (Nat.gcd_dvd_right _ _)
  rcases he0 with he0 | he0 <;> rcases he1 with he1 | he1
  · exfalso
    rw [h0, h1, he0, he1, one_mul, one_mul] at hdiv
    have h2 : p ∣ Eg0 v a b c d * Eg1 v a b c d :=
      dvd_trans hdiv (Nat.lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _))
    rcases hp.dvd_mul.mp h2 with h | h
    · exact hpd0 h
    · exact hpd1 h
  · rw [h0, h1, he0, he1, one_mul]
    rw [show p * Eg1 v a b c d = Eg1 v a b c d * p by ring, lcm_mul_right_of_not_dvd hp hpd0]
  · rw [h0, h1, he0, he1, one_mul]
    rw [show p * Eg0 v a b c d = Eg0 v a b c d * p by ring,
      lcm_mul_left_of_not_dvd hp hpd1]
  · rw [h0, h1, he0, he1]
    rw [show p * Eg0 v a b c d = Eg0 v a b c d * p by ring,
      show p * Eg1 v a b c d = Eg1 v a b c d * p by ring, Nat.lcm_mul_right]
    ring

theorem composite_weil : ∀ q : ℕ, Squarefree q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → χ ≠ 1 → ∀ a b c d : ℕ,
    ‖∑ x : ZMod q, χ ((x + (a:ZMod q)) * (x + (b:ZMod q)) *
        ((x + (c:ZMod q)) * (x + (d:ZMod q))) ^ (orderOf χ - 1))‖
      ≤ 4 ^ (q.primeFactors.card) * Real.sqrt (q : ℝ) * WL q a b c d := by
  intro q
  refine Nat.strong_induction_on q (fun q ih => ?_)
  intro hsq _inst χ hprim hne a b c d
  have hm2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  have hm0 : orderOf χ ≠ 0 := (orderOf_pos χ).ne'
  by_cases hq1 : q = 1
  · subst hq1; exact absurd (DirichletCharacter.level_one χ) hne
  by_cases hprime : q.Prime
  · haveI : Fact q.Prime := ⟨hprime⟩
    by_cases hgood : ∀ c₀ : ZMod q, ∀ Q : Polynomial (ZMod q),
        (Polynomial.X + Polynomial.C (a:ZMod q)) * (Polynomial.X + Polynomial.C (b:ZMod q)) *
          ((Polynomial.X + Polynomial.C (c:ZMod q)) * (Polynomial.X + Polynomial.C (d:ZMod q)))
            ^ (orderOf χ - 1) ≠ Polynomial.C c₀ * Q ^ (orderOf χ)
    · have hb := prime_good χ hne hm2 a b c d hgood
      have hW1 : 1 ≤ WL q a b c d := by
        unfold WL
        have h1 : (1:ℝ) ≤ ((Nat.lcm (Eg0 q a b c d) (Eg1 q a b c d) : ℕ) : ℝ) := by
          have h2 : 1 ≤ Nat.lcm (Eg0 q a b c d) (Eg1 q a b c d) :=
            Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
              (lt_of_lt_of_le (Eg0_pos (NeZero.ne q))
                (Nat.le_lcm_left (Eg0 q a b c d) (Eg1_pos (NeZero.ne q)))))
          exact_mod_cast h2
        calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
          _ ≤ Real.sqrt _ := Real.sqrt_le_sqrt h1
      calc ‖∑ x : ZMod q, χ ((x + (a:ZMod q)) * (x + (b:ZMod q)) *
              ((x + (c:ZMod q)) * (x + (d:ZMod q))) ^ (orderOf χ - 1))‖
          ≤ 4 * Real.sqrt (q:ℝ) := hb
        _ ≤ 4 ^ (q.primeFactors.card) * Real.sqrt (q:ℝ) * WL q a b c d := by
            rw [hprime.primeFactors, Finset.card_singleton, pow_one]
            nlinarith only [Real.sqrt_nonneg (q:ℝ), hW1]
    · push_neg at hgood
      obtain ⟨c₀, Q, hQ⟩ := hgood
      have hdiv := prime_bad χ hne (le_of_lt hm2) (dvd_refl (orderOf χ)) (dvd_refl q) a b c d
        ⟨c₀, Q, hQ⟩
      have hW : WL q a b c d = Real.sqrt (q:ℝ) := by
        unfold WL
        have hlcm : Nat.lcm (Eg0 q a b c d) (Eg1 q a b c d) = q := by
          apply Nat.dvd_antisymm
          · exact Nat.lcm_dvd (by unfold Eg0; exact Nat.gcd_dvd_right _ _)
              (by unfold Eg1; exact Nat.gcd_dvd_right _ _)
          · rcases hdiv with h | h
            · exact dvd_trans h (Nat.dvd_lcm_left _ _)
            · exact dvd_trans h (Nat.dvd_lcm_right _ _)
        rw [hlcm]
      have htriv : ‖∑ y : ZMod q, χ ((y + (a:ZMod q)) * (y + (b:ZMod q)) *
              ((y + (c:ZMod q)) * (y + (d:ZMod q))) ^ (orderOf χ - 1))‖ ≤ (q:ℝ) := by
        calc ‖∑ y : ZMod q, χ ((y + (a:ZMod q)) * (y + (b:ZMod q)) *
                ((y + (c:ZMod q)) * (y + (d:ZMod q))) ^ (orderOf χ - 1))‖
            ≤ ∑ y : ZMod q, ‖χ ((y + (a:ZMod q)) * (y + (b:ZMod q)) *
                ((y + (c:ZMod q)) * (y + (d:ZMod q))) ^ (orderOf χ - 1))‖ := norm_sum_le _ _
          _ ≤ ∑ _y : ZMod q, (1:ℝ) :=
              Finset.sum_le_sum (fun y _ => DirichletCharacter.norm_le_one χ _)
          _ = (q:ℝ) := by rw [Finset.sum_const, Finset.card_univ, ZMod.card]; simp
      calc ‖∑ y : ZMod q, χ ((y + (a:ZMod q)) * (y + (b:ZMod q)) *
              ((y + (c:ZMod q)) * (y + (d:ZMod q))) ^ (orderOf χ - 1))‖
          ≤ (q:ℝ) := htriv
        _ ≤ 4 ^ (q.primeFactors.card) * Real.sqrt (q:ℝ) * WL q a b c d := by
            rw [hW, hprime.primeFactors, Finset.card_singleton, pow_one]
            have hsq : Real.sqrt (q:ℝ) * Real.sqrt (q:ℝ) = (q:ℝ) := by
              rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg q)]
            linarith only [hsq, (Nat.cast_nonneg q : (0:ℝ) ≤ (q:ℝ))]
  · have hqpos : 0 < q := Nat.pos_of_neZero q
    have hminprime : (q.minFac).Prime := Nat.minFac_prime hq1
    have hminmul : q.minFac * (q / q.minFac) = q := Nat.mul_div_cancel' (Nat.minFac_dvd q)
    have hminusq : ¬ q.minFac ∣ q / q.minFac := by
      intro h
      obtain ⟨k, hk⟩ := h
      have hpp : q.minFac * q.minFac ∣ q := by
        refine ⟨k, ?_⟩
        calc q = q.minFac * (q / q.minFac) := hminmul.symm
          _ = q.minFac * (q.minFac * k) := by rw [hk]
          _ = q.minFac * q.minFac * k := by ring
      exact hminprime.ne_one (Nat.dvd_one.mp (hsq q.minFac hpp).dvd)
    have hmincop : (q.minFac).Coprime (q / q.minFac) :=
      (hminprime.coprime_iff_not_dvd).mpr hminusq
    have hminvne : q / q.minFac ≠ 0 := by
      intro h; rw [h, mul_zero] at hminmul; exact NeZero.ne q hminmul.symm
    have hminvlt : q / q.minFac < q := Nat.div_lt_self hqpos hminprime.one_lt
    obtain ⟨p, v, hpprime, hpv_eq, hvne, hvlt, hcop⟩ :
        ∃ p v : ℕ, p.Prime ∧ p * v = q ∧ v ≠ 0 ∧ v < q ∧ p.Coprime v :=
      ⟨q.minFac, q / q.minFac, hminprime, hminmul, hminvne, hminvlt, hmincop⟩
    have hq_eq : q = p * v := hpv_eq.symm
    subst hq_eq
    have hsqv : Squarefree v := hsq.squarefree_of_dvd (by rw [← hpv_eq]; exact dvd_mul_left _ _)
    have hcard : (p * v).primeFactors.card = v.primeFactors.card + 1 := by
      rw [Nat.primeFactors_mul hpprime.ne_zero hvne, hpprime.primeFactors,
        Finset.singleton_union, Finset.card_insert_of_notMem]
      intro h; exact ((hpprime.coprime_iff_not_dvd).mp hcop) (Nat.mem_primeFactors.mp h).2.1
    haveI : Fact p.Prime := ⟨hpprime⟩
    haveI : NeZero p := ⟨hpprime.ne_zero⟩
    haveI : NeZero v := ⟨hvne⟩
    set χp := factorLeft hcop χ with hχpdef
    set χv := factorRight hcop χ with hχvdef
    have hprim_p : χp.IsPrimitive := factorLeft_isPrimitive hcop χ hprim
    have hprim_v : χv.IsPrimitive := factorRight_isPrimitive hcop χ hprim
    have hne_p : χp ≠ 1 := by
      intro h1
      rw [DirichletCharacter.eq_one_iff_conductor_eq_one] at h1
      rw [(DirichletCharacter.isPrimitive_def χp).mp hprim_p] at h1
      exact hpprime.ne_one h1
    have hne_v : χv ≠ 1 := by
      intro h1
      rw [DirichletCharacter.eq_one_iff_conductor_eq_one] at h1
      rw [(DirichletCharacter.isPrimitive_def χv).mp hprim_v] at h1
      exact hprime (by rw [h1, mul_one]; exact hpprime)
    have hdv_p : orderOf χp ∣ orderOf χ := orderOf_factorLeft_dvd hcop χ
    have hdv_v : orderOf χv ∣ orderOf χ := orderOf_factorRight_dvd hcop χ
    rw [split_sum hcop χ (orderOf χ) a b c d, norm_mul]
    have hconv : (∑ z : ZMod v, χv ((z + (a:ZMod v)) * (z + (b:ZMod v)) *
            ((z + (c:ZMod v)) * (z + (d:ZMod v))) ^ (orderOf χ - 1)))
        = (∑ z : ZMod v, χv ((z + (a:ZMod v)) * (z + (b:ZMod v)) *
            ((z + (c:ZMod v)) * (z + (d:ZMod v))) ^ (orderOf χv - 1))) := by
      apply Finset.sum_congr rfl; intro z _
      have hQ : (χv (z + (c:ZMod v)) * χv (z + (d:ZMod v))) ^ (orderOf χ - 1)
          = (χv (z + (c:ZMod v)) * χv (z + (d:ZMod v))) ^ (orderOf χv - 1) := by
        rw [← map_mul]
        exact char_pow_pred_eq χv hdv_v hm0 hm2 hne_v _
      simp only [map_mul, map_pow]
      rw [hQ]
    rw [hconv]
    have hih := ih v hvlt hsqv χv hprim_v hne_v a b c d
    by_cases hgoodp : ∀ c₀ : ZMod p, ∀ Q : Polynomial (ZMod p),
        (Polynomial.X + Polynomial.C (a:ZMod p)) * (Polynomial.X + Polynomial.C (b:ZMod p)) *
          ((Polynomial.X + Polynomial.C (c:ZMod p)) * (Polynomial.X + Polynomial.C (d:ZMod p)))
            ^ (orderOf χ - 1) ≠ Polynomial.C c₀ * Q ^ (orderOf χp)
    · have hbp := prime_good χp hne_p hm2 a b c d hgoodp
      have hWle : WL v a b c d ≤ WL (p*v) a b c d :=
        WL_mono (by rw [← hpv_eq]; exact dvd_mul_left _ _) (NeZero.ne (p*v))
      have hsq : Real.sqrt (p:ℝ) * Real.sqrt (v:ℝ) = Real.sqrt ((p*v : ℕ) : ℝ) := by
        rw [← Real.sqrt_mul (Nat.cast_nonneg p)]; push_cast; ring
      have hpw : (0:ℝ) < 4 ^ v.primeFactors.card := pow_pos (by norm_num) _
      calc ‖∑ y : ZMod p, χp ((y + (a:ZMod p)) * (y + (b:ZMod p)) *
              ((y + (c:ZMod p)) * (y + (d:ZMod p))) ^ (orderOf χ - 1))‖ *
            ‖∑ z : ZMod v, χv ((z + (a:ZMod v)) * (z + (b:ZMod v)) *
              ((z + (c:ZMod v)) * (z + (d:ZMod v))) ^ (orderOf χv - 1))‖
          ≤ (4 * Real.sqrt (p:ℝ)) * (4 ^ v.primeFactors.card * Real.sqrt (v:ℝ)
              * WL v a b c d) := by
            exact mul_le_mul hbp hih (norm_nonneg _) (by positivity)
        _ ≤ 4 ^ ((p*v).primeFactors.card) * Real.sqrt ((p*v : ℕ) : ℝ) * WL (p*v) a b c d := by
            rw [hcard, pow_succ, ← hsq]
            have hsp : (0:ℝ) ≤ Real.sqrt (p:ℝ) := Real.sqrt_nonneg _
            have hsv : (0:ℝ) ≤ Real.sqrt (v:ℝ) := Real.sqrt_nonneg _
            have key : 4 * Real.sqrt (p:ℝ) * (4 ^ v.primeFactors.card * Real.sqrt (v:ℝ) * WL v a b c d)
                = 4 ^ v.primeFactors.card * 4 * (Real.sqrt (p:ℝ) * Real.sqrt (v:ℝ)) * WL v a b c d := by
              ring
            rw [key]
            exact mul_le_mul_of_nonneg_left hWle
              (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (by norm_num))
                (mul_nonneg hsp hsv))
    · push_neg at hgoodp
      obtain ⟨c₀, Q, hQ⟩ := hgoodp
      have hdiv := prime_bad χp hne_p (le_of_lt hm2) hdv_p (dvd_mul_right p v) a b c d
        ⟨c₀, Q, hQ⟩
      have htriv : ‖∑ y : ZMod p, χp ((y + (a:ZMod p)) * (y + (b:ZMod p)) *
              ((y + (c:ZMod p)) * (y + (d:ZMod p))) ^ (orderOf χ - 1))‖ ≤ (p:ℝ) := by
        calc ‖∑ y : ZMod p, χp ((y + (a:ZMod p)) * (y + (b:ZMod p)) *
                ((y + (c:ZMod p)) * (y + (d:ZMod p))) ^ (orderOf χ - 1))‖
            ≤ ∑ y : ZMod p, ‖χp ((y + (a:ZMod p)) * (y + (b:ZMod p)) *
                ((y + (c:ZMod p)) * (y + (d:ZMod p))) ^ (orderOf χ - 1))‖ := norm_sum_le _ _
          _ ≤ ∑ _y : ZMod p, (1:ℝ) :=
              Finset.sum_le_sum (fun y _ => DirichletCharacter.norm_le_one χp _)
          _ = (p:ℝ) := by rw [Finset.sum_const, Finset.card_univ, ZMod.card]; simp
      have hdivl : p ∣ Nat.lcm (Eg0 (p*v) a b c d) (Eg1 (p*v) a b c d) := by
        rcases hdiv with h | h
        · exact dvd_trans h (Nat.dvd_lcm_left _ _)
        · exact dvd_trans h (Nat.dvd_lcm_right _ _)
      have hWeq : WL (p*v) a b c d = Real.sqrt (p:ℝ) * WL v a b c d := by
        unfold WL
        rw [← lcm_Eg_step hpprime hcop hdivl]
        rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p)]
      have hsq : Real.sqrt (p:ℝ) * Real.sqrt (v:ℝ) = Real.sqrt ((p*v : ℕ) : ℝ) := by
        rw [← Real.sqrt_mul (Nat.cast_nonneg p)]; push_cast; ring
      calc ‖∑ y : ZMod p, χp ((y + (a:ZMod p)) * (y + (b:ZMod p)) *
              ((y + (c:ZMod p)) * (y + (d:ZMod p))) ^ (orderOf χ - 1))‖ *
            ‖∑ z : ZMod v, χv ((z + (a:ZMod v)) * (z + (b:ZMod v)) *
              ((z + (c:ZMod v)) * (z + (d:ZMod v))) ^ (orderOf χv - 1))‖
          ≤ (p:ℝ) * (4 ^ v.primeFactors.card * Real.sqrt (v:ℝ) * WL v a b c d) := by
            exact mul_le_mul htriv hih (norm_nonneg _) (by positivity)
        _ ≤ 4 ^ ((p*v).primeFactors.card) * Real.sqrt ((p*v : ℕ) : ℝ) * WL (p*v) a b c d := by
            rw [hcard, hWeq, pow_succ]
            have hsp : (0:ℝ) ≤ Real.sqrt (p:ℝ) := Real.sqrt_nonneg _
            have hs : (0:ℝ) ≤ Real.sqrt ((p*v : ℕ) : ℝ) := Real.sqrt_nonneg _
            have hW0 : (0:ℝ) ≤ WL v a b c d := Real.sqrt_nonneg _
            have hpp' : (p:ℝ) = Real.sqrt (p:ℝ) * Real.sqrt (p:ℝ) := by
              rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg p)]
            have hX1 : (p:ℝ) * (4 ^ v.primeFactors.card * Real.sqrt (v:ℝ) * WL v a b c d)
                = 4 ^ v.primeFactors.card * Real.sqrt ((p*v : ℕ) : ℝ)
                  * (Real.sqrt (p:ℝ) * WL v a b c d) := by
              have hmul : Real.sqrt (p:ℝ) * Real.sqrt (p:ℝ) = (p:ℝ) := by
                rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg p)]
              calc (p:ℝ) * (4 ^ v.primeFactors.card * Real.sqrt (v:ℝ) * WL v a b c d)
                  = (Real.sqrt (p:ℝ) * Real.sqrt (p:ℝ))
                      * (4 ^ v.primeFactors.card * Real.sqrt (v:ℝ) * WL v a b c d) := by rw [hmul]
                _ = 4 ^ v.primeFactors.card * (Real.sqrt (p:ℝ) * Real.sqrt (v:ℝ))
                      * (Real.sqrt (p:ℝ) * WL v a b c d) := by ring
                _ = 4 ^ v.primeFactors.card * Real.sqrt ((p*v : ℕ) : ℝ)
                      * (Real.sqrt (p:ℝ) * WL v a b c d) := by rw [hsq]
            have hX2 : 4 ^ v.primeFactors.card * 4 * Real.sqrt ((p*v : ℕ) : ℝ)
                  * (Real.sqrt (p:ℝ) * WL v a b c d)
                = 4 * (4 ^ v.primeFactors.card * Real.sqrt ((p*v : ℕ) : ℝ)
                  * (Real.sqrt (p:ℝ) * WL v a b c d)) := by ring
            rw [hX1, hX2]
            exact le_mul_of_one_le_left
              (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hs) (mul_nonneg hsp hW0))
              (by norm_num)



lemma factorial_card_le_prod (S : Finset ℕ) (h : ∀ x ∈ S, 2 ≤ x) :
    Nat.factorial S.card ≤ ∏ x ∈ S, x := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha_not : a ∉ s := fun ha => absurd (hlt a ha) (lt_irrefl a)
    rw [Finset.prod_insert ha_not, Finset.card_insert_of_notMem ha_not, Nat.factorial_succ]
    have h1 : Nat.factorial s.card ≤ ∏ x ∈ s, x := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    have h2 : s.card + 1 ≤ a := by
      have ha2 : 2 ≤ a := h a (Finset.mem_insert_self a s)
      have hsub : s ⊆ Finset.Icc 2 (a - 1) := by
        intro x hx
        rw [Finset.mem_Icc]
        exact ⟨h x (Finset.mem_insert_of_mem hx), by have := hlt x hx; omega⟩
      have h3 := Finset.card_le_card hsub
      rw [Nat.card_Icc] at h3
      omega
    exact Nat.mul_le_mul h2 h1

lemma factorial_primeFactors_card_le {q : ℕ} (hq : 1 ≤ q) :
    Nat.factorial q.primeFactors.card ≤ q := by
  have h1 : Nat.factorial q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
    factorial_card_le_prod _ (fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le)
  have h2 : ∏ p ∈ q.primeFactors, p ≤ q :=
    Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  exact h1.trans h2

theorem four_pow_primeFactors_card_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 1 ≤ q → (4:ℝ) ^ (q.primeFactors.card : ℕ) ≤ C * (q:ℝ)^ε := by
  set K : ℝ := 4 * (4:ℝ)^((4:ℝ)/ε) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  refine ⟨(4:ℝ)^K, Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro q hq
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hqR0 : (0:ℝ) < (q:ℝ) := lt_of_lt_of_le one_pos hqR1
  have hqeps1 : (1:ℝ) ≤ (q:ℝ)^ε := Real.one_le_rpow hqR1 hε.le
  by_cases hlarge : K ≤ ((q.primeFactors.card : ℕ) : ℝ)
  · set k := q.primeFactors.card with hkdef
    have hkR : K ≤ (k:ℝ) := hlarge
    have hk4 : 4 ≤ k := by
      have h4K : (4:ℝ) ≤ K := by
        rw [hKdef]
        have : (1:ℝ) ≤ (4:ℝ)^((4:ℝ)/ε) := Real.one_le_rpow (by norm_num) (by positivity)
        linarith only [this]
      have : (4:ℝ) ≤ (k:ℝ) := le_trans h4K hkR
      exact_mod_cast this
    have hfact : Nat.factorial k ≤ q := by
      rw [hkdef]; exact factorial_primeFactors_card_le hq
    have hfactR : ((Nat.factorial k : ℕ) : ℝ) ≤ (q:ℝ) := by exact_mod_cast hfact
    have hfactpos : (0:ℝ) < ((Nat.factorial k : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos k
    have hlog : Real.log ((Nat.factorial k : ℕ) : ℝ) ≤ Real.log (q:ℝ) :=
      Real.log_le_log hfactpos hfactR
    set m := k / 2 with hmdef
    have hmle : m ≤ k := by omega
    have hpow : m ^ m ≤ Nat.factorial k := by
      have h := Nat.factorial_mul_pow_sub_le_factorial hmle
      have h3 : m ^ m ≤ m ^ (k - m) := Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : m ^ (k - m) ≤ Nat.factorial m * m ^ (k - m) :=
        Nat.le_mul_of_pos_left (m ^ (k - m)) (Nat.factorial_pos m)
      exact (h3.trans h4).trans h
    have hlog2 : (m:ℝ) * Real.log (m:ℝ) ≤ Real.log ((Nat.factorial k : ℕ) : ℝ) := by
      have h4 : (m:ℝ)^m ≤ ((Nat.factorial k : ℕ) : ℝ) := by
        rw [← Nat.cast_pow]; exact_mod_cast hpow
      have hmmpos : (0:ℝ) < (m:ℝ)^m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0]; simp
        · exact pow_pos (by exact_mod_cast h0) m
      have h5 := Real.log_le_log hmmpos h4
      rwa [Real.log_pow] at h5
    have hmge : (k:ℝ)/4 ≤ (m:ℝ) := by
      have hk1 : (k:ℝ) = 2 * (m:ℝ) + ((k % 2 : ℕ) : ℝ) := by
        have h : 2 * (k / 2) + k % 2 = k := by
          have := Nat.div_add_mod k 2; omega
        calc (k:ℝ) = ((2 * (k / 2) + k % 2 : ℕ) : ℝ) := by rw [h]
          _ = 2 * ((k / 2 : ℕ) : ℝ) + ((k % 2 : ℕ) : ℝ) := by push_cast; ring
          _ = 2 * (m:ℝ) + ((k % 2 : ℕ) : ℝ) := by rw [hmdef]
      have hmod : ((k % 2 : ℕ) : ℝ) ≤ 1 := by
        have h2 : k % 2 ≤ 1 := by have := Nat.mod_lt k (by norm_num : 0 < 2); omega
        exact_mod_cast h2
      have hm2 : (2:ℝ) ≤ (m:ℝ) := by
        have : 2 ≤ m := by omega
        exact_mod_cast this
      rw [hk1]; linarith only [hmod, hm2]
    have hmpos : (0:ℝ) < (m:ℝ) := by
      have : 0 < m := by omega
      exact_mod_cast this
    have hlogm : Real.log ((k:ℝ)/4) ≤ Real.log (m:ℝ) :=
      Real.log_le_log (by positivity) hmge
    have hlog4pos : (0:ℝ) ≤ Real.log ((k:ℝ)/4) := by
      apply Real.log_nonneg
      have : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk4
      linarith only [this]
    have hkey : (k:ℝ) * Real.log 4 ≤ ε * ((m:ℝ) * Real.log (m:ℝ)) := by
      have h1 : ((k:ℝ)/4) * Real.log ((k:ℝ)/4) ≤ (m:ℝ) * Real.log (m:ℝ) :=
        mul_le_mul hmge hlogm hlog4pos (by positivity)
      have h2 : (4:ℝ)/ε * Real.log 4 ≤ Real.log ((k:ℝ)/4) := by
        have h3 : (4:ℝ)^((4:ℝ)/ε) ≤ (k:ℝ)/4 := by
          have := hkR; rw [hKdef] at this; linarith only [hlarge]
        calc (4:ℝ)/ε * Real.log 4 = Real.log ((4:ℝ)^((4:ℝ)/ε)) := by
              rw [Real.log_rpow (by norm_num : (0:ℝ) < 4)]
          _ ≤ Real.log ((k:ℝ)/4) := Real.log_le_log (by positivity) h3
      have h6 : ε * ((4:ℝ)/ε * Real.log 4) = 4 * Real.log 4 := by
        field_simp
      have h5 : ε * ((4:ℝ)/ε * Real.log 4) ≤ ε * Real.log ((k:ℝ)/4) :=
        mul_le_mul_of_nonneg_left h2 hε.le
      have h4 : (k:ℝ) * Real.log 4 ≤ ε * (((k:ℝ)/4) * Real.log ((k:ℝ)/4)) := by
        calc (k:ℝ) * Real.log 4 = ((k:ℝ)/4) * (4 * Real.log 4) := by ring
          _ = ((k:ℝ)/4) * (ε * ((4:ℝ)/ε * Real.log 4)) := by rw [h6]
          _ ≤ ((k:ℝ)/4) * (ε * Real.log ((k:ℝ)/4)) :=
              mul_le_mul_of_nonneg_left h5 (by positivity)
          _ = ε * (((k:ℝ)/4) * Real.log ((k:ℝ)/4)) := by ring
      exact h4.trans (mul_le_mul_of_nonneg_left h1 hε.le)
    have hfin : (k:ℝ) * Real.log 4 ≤ ε * Real.log (q:ℝ) :=
      hkey.trans (mul_le_mul_of_nonneg_left (hlog2.trans hlog) hε.le)
    have hmain : (4:ℝ)^k ≤ (q:ℝ)^ε := by
      have hfin' : ((k:ℕ):ℝ) * Real.log 4 ≤ Real.log ((q:ℝ)^ε) := by
        rw [Real.log_rpow hqR0]; exact hfin
      rw [← Real.rpow_natCast (4:ℝ) k]
      exact (Real.rpow_le_iff_le_log (x := (4:ℝ)) (y := (q:ℝ)^ε) (z := ((k:ℕ):ℝ))
        (by norm_num) (Real.rpow_pos_of_pos hqR0 _)).mpr hfin'
    calc (4:ℝ) ^ (q.primeFactors.card : ℕ) = (4:ℝ)^k := by rw [hkdef]
      _ ≤ (q:ℝ)^ε := hmain
      _ ≤ (4:ℝ)^K * (q:ℝ)^ε :=
          le_mul_of_one_le_left (Real.rpow_nonneg hqR0.le _)
            (Real.one_le_rpow (by norm_num) hKpos.le)
  · have h1 : (4:ℝ)^((q.primeFactors.card:ℕ):ℝ) ≤ (4:ℝ)^K :=
      (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 4)).mpr (le_of_lt (not_le.mp hlarge))
    rw [← Real.rpow_natCast (4:ℝ) q.primeFactors.card]
    calc (4:ℝ)^((q.primeFactors.card:ℕ):ℝ) ≤ (4:ℝ)^K := h1
      _ ≤ (4:ℝ)^K * (q:ℝ)^ε := le_mul_of_one_le_right (Real.rpow_nonneg (by norm_num) _) hqeps1

/-! ## Reindexing and final assembly -/

lemma sum_fin_eq_sum_Icc (H : ℕ) (g : ℕ → ℝ) :
    (∑ a : Fin H, g ((a:ℕ)+1)) = ∑ a ∈ Finset.Icc 1 H, g a := by
  rw [Fin.sum_univ_eq_sum_range (fun a => g (a+1)) H]
  refine Finset.sum_bij (fun a _ => a+1) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_range] at ha; rw [Finset.mem_Icc]; omega
  · intro a _ b _ h; omega
  · intro b hb
    rw [Finset.mem_Icc] at hb
    exact ⟨b-1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro a _; rfl

lemma sum_fin2_eq_sum_Icc (H : ℕ) (g : ℕ → ℕ → ℝ) :
    (∑ c : Fin H, ∑ d : Fin H, g ((c:ℕ)+1) ((d:ℕ)+1))
      = ∑ c ∈ Finset.Icc 1 H, ∑ d ∈ Finset.Icc 1 H, g c d := by
  rw [sum_fin_eq_sum_Icc H (fun c => ∑ d : Fin H, g c ((d:ℕ)+1))]
  apply Finset.sum_congr rfl
  intro c _
  exact sum_fin_eq_sum_Icc H (g c)

lemma sum_fin_four_eq_sum_Icc {H : ℕ} (Ψ : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ f : Fin 2 → Fin H, ∑ g : Fin 2 → Fin H,
        Ψ ((f 0 : ℕ)+1) ((f 1 : ℕ)+1) ((g 0 : ℕ)+1) ((g 1 : ℕ)+1))
      = ∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
          ∑ d ∈ Finset.Icc 1 H, Ψ a b c d := by
  let e : (Fin 2 → Fin H) ≃ (Fin H × Fin H) :=
    { toFun := fun f => (f 0, f 1)
      invFun := fun p => fun i => if i = 0 then p.1 else p.2
      left_inv := by
        intro f; funext i; fin_cases i <;> simp
      right_inv := by intro p; simp }
  have h1 : (∑ f : Fin 2 → Fin H, ∑ g : Fin 2 → Fin H,
        Ψ ((f 0 : ℕ)+1) ((f 1 : ℕ)+1) ((g 0 : ℕ)+1) ((g 1 : ℕ)+1))
      = ∑ p : Fin H × Fin H, ∑ g : Fin 2 → Fin H,
        Ψ ((p.1 : ℕ)+1) ((p.2 : ℕ)+1) ((g 0 : ℕ)+1) ((g 1 : ℕ)+1) := by
    refine Fintype.sum_equiv e _ _ ?_
    intro f
    rfl
  rw [h1, Fintype.sum_prod_type]
  have h2 : ∀ a b : Fin H, (∑ g : Fin 2 → Fin H,
        Ψ ((a : ℕ)+1) ((b : ℕ)+1) ((g 0 : ℕ)+1) ((g 1 : ℕ)+1))
      = ∑ c : Fin H, ∑ d : Fin H, Ψ ((a : ℕ)+1) ((b : ℕ)+1) ((c : ℕ)+1) ((d : ℕ)+1) := by
    intro a b
    rw [Fintype.sum_equiv e (fun g : Fin 2 → Fin H =>
        Ψ ((a : ℕ)+1) ((b : ℕ)+1) ((g 0 : ℕ)+1) ((g 1 : ℕ)+1))
      (fun p : Fin H × Fin H => Ψ ((a : ℕ)+1) ((b : ℕ)+1) ((p.1 : ℕ)+1) ((p.2 : ℕ)+1))
      (by intro g; rfl)]
    rw [Fintype.sum_prod_type]
  simp_rw [h2]
  rw [sum_fin_eq_sum_Icc H (fun a => ∑ b : Fin H, ∑ c : Fin H, ∑ d : Fin H,
      Ψ a ((b:ℕ)+1) ((c:ℕ)+1) ((d:ℕ)+1))]
  apply Finset.sum_congr rfl; intro a _
  rw [sum_fin_eq_sum_Icc H (fun b => ∑ c : Fin H, ∑ d : Fin H,
      Ψ a b ((c:ℕ)+1) ((d:ℕ)+1))]
  apply Finset.sum_congr rfl; intro b _
  rw [sum_fin_eq_sum_Icc H (fun c => ∑ d : Fin H, Ψ a b c ((d:ℕ)+1))]
  apply Finset.sum_congr rfl; intro c _
  exact sum_fin_eq_sum_Icc H (fun d => Ψ a b c d)

lemma Tgq_apply {q : ℕ} [NeZero q] (H : ℕ) (χ : DirichletCharacter ℂ q) (f g : Fin 2 → Fin H) :
    Tgq H 2 χ f g = ∑ x : ZMod q, χ ((x + ((f 0 : ℕ) + 1 : ℕ)) * (x + ((f 1 : ℕ) + 1 : ℕ)) *
        ((x + ((g 0 : ℕ) + 1 : ℕ)) * (x + ((g 1 : ℕ) + 1 : ℕ))) ^ (orderOf χ - 1)) := by
  unfold Tgq Pf
  apply Finset.sum_congr rfl; intro x _
  congr 1
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_prod, Polynomial.eval_prod,
    Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

/-- Conditional form of the main theorem, with the counting lemma as a hypothesis. -/
theorem burgess_moment_squarefree_r2_aux
    (hcount : ∀ {ε : ℝ}, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (q H : ℕ), Squarefree q → H ≤ q →
      (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
        ∑ d ∈ Finset.Icc 1 H,
        Real.sqrt (Nat.lcm (Nat.gcd (Int.gcd ((a:ℤ) - (b:ℤ)) ((c:ℤ) - (d:ℤ))) q)
          (Nat.gcd (Int.gcd (((a:ℤ) + (b:ℤ)) - ((c:ℤ) + (d:ℤ)))
            ((a:ℤ) * (b:ℤ) - (c:ℤ) * (d:ℤ))) q)))
      ≤ C * (q : ℝ) ^ ε * ((H : ℝ)^4 + (H : ℝ)^2 * Real.sqrt (q : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], Squarefree q →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ H : ℕ, H ≤ q →
        ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)‖ ^ 4
          ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ 2 + (H : ℝ) ^ 4 * Real.sqrt (q : ℝ)) := by
  obtain ⟨C1, hC1pos, hC1⟩ := hcount (ε := ε/2) (by linarith only [hε])
  obtain ⟨C2, hC2pos, hC2⟩ := four_pow_primeFactors_card_le (ε := ε/2) (by linarith only [hε])
  refine ⟨2 * (C1 * C2 + 1), by positivity, ?_⟩
  intro q _inst hsq χ hprim hne H hHq
  rcases Nat.eq_zero_or_pos H with hH0 | hHpos
  · subst hH0
    have hzero : (∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + 0), χ (h : ZMod q)‖ ^ 4) = 0 := by
      apply Finset.sum_eq_zero
      intro m _
      rw [add_zero, Finset.Ioc_self, Finset.sum_empty, norm_zero]
      exact zero_pow (by norm_num : (4:ℕ) ≠ 0)
    rw [hzero]; positivity
  · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hqR0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
    have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
    have hH1 : (0:ℝ) ≤ (H:ℝ) := by positivity
    have h4p := hC2 q hq1
    rw [sum_norm_eq_norm_sum (p := q) (S := fun m => ∑ h ∈ Finset.Ioc m (m+H), χ (h:ZMod q)) 2]
    rw [Z_eq' H 2 χ hne]
    have hstep1 : ‖∑ f : Fin 2 → Fin H, ∑ g : Fin 2 → Fin H, Tgq H 2 χ f g‖
        ≤ ∑ f : Fin 2 → Fin H, ∑ g : Fin 2 → Fin H, ‖Tgq H 2 χ f g‖ := by
      calc ‖∑ f : Fin 2 → Fin H, ∑ g : Fin 2 → Fin H, Tgq H 2 χ f g‖
          ≤ ∑ f : Fin 2 → Fin H, ‖∑ g : Fin 2 → Fin H, Tgq H 2 χ f g‖ := norm_sum_le _ _
        _ ≤ ∑ f : Fin 2 → Fin H, ∑ g : Fin 2 → Fin H, ‖Tgq H 2 χ f g‖ :=
            Finset.sum_le_sum (fun f _ => norm_sum_le _ _)
    have hstep2 : ∑ f : Fin 2 → Fin H, ∑ g : Fin 2 → Fin H, ‖Tgq H 2 χ f g‖
        ≤ ∑ f : Fin 2 → Fin H, ∑ g : Fin 2 → Fin H,
            (4:ℝ)^(q.primeFactors.card) * Real.sqrt (q:ℝ) *
              WL q ((f 0 : ℕ)+1) ((f 1 : ℕ)+1) ((g 0 : ℕ)+1) ((g 1 : ℕ)+1) := by
      apply Finset.sum_le_sum; intro f _
      apply Finset.sum_le_sum; intro g _
      rw [Tgq_apply]
      exact composite_weil q hsq χ hprim hne ((f 0:ℕ)+1) ((f 1:ℕ)+1) ((g 0:ℕ)+1) ((g 1:ℕ)+1)
    have hstep3 : ∑ f : Fin 2 → Fin H, ∑ g : Fin 2 → Fin H,
            (4:ℝ)^(q.primeFactors.card) * Real.sqrt (q:ℝ) *
              WL q ((f 0 : ℕ)+1) ((f 1 : ℕ)+1) ((g 0 : ℕ)+1) ((g 1 : ℕ)+1)
        = (4:ℝ)^(q.primeFactors.card) * Real.sqrt (q:ℝ) *
            ∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
              ∑ d ∈ Finset.Icc 1 H, WL q a b c d := by
      rw [sum_fin_four_eq_sum_Icc (Ψ := fun a b c d =>
        (4:ℝ)^(q.primeFactors.card) * Real.sqrt (q:ℝ) * WL q a b c d)]
      simp only [Finset.mul_sum]
    have hstep4 : ∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
              ∑ d ∈ Finset.Icc 1 H, WL q a b c d
        ≤ C1 * (q:ℝ)^(ε/2) * ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ)) := by
      simpa only [WL, Eg0, Eg1] using hC1 q H hsq hHq
    have hpe : (q:ℝ)^(ε/2) * (q:ℝ)^(ε/2) = (q:ℝ)^ε := by
      rw [← Real.rpow_add hqR0]; norm_num
    have hsq : Real.sqrt (q:ℝ) * ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ))
        = (H:ℝ)^4 * Real.sqrt (q:ℝ) + (H:ℝ)^2 * (q:ℝ) := by
      have hss : Real.sqrt (q:ℝ) * Real.sqrt (q:ℝ) = (q:ℝ) := by
        rw [← pow_two, Real.sq_sqrt hqR0.le]
      nlinarith only [hss]
    have hfinal : (4:ℝ)^(q.primeFactors.card) * Real.sqrt (q:ℝ) *
          (C1 * (q:ℝ)^(ε/2) * ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ)))
        ≤ (2 * (C1 * C2 + 1)) * (q:ℝ)^ε *
            ((q:ℝ) * (H:ℝ)^2 + (H:ℝ)^4 * Real.sqrt (q:ℝ)) := by
      have hs0 : (0:ℝ) ≤ Real.sqrt (q:ℝ) := Real.sqrt_nonneg _
      have hX0 : (0:ℝ) ≤ (H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ) := by positivity
      have hqpe : (0:ℝ) ≤ (q:ℝ)^ε := Real.rpow_nonneg hqR0.le _
      have hqpe0 : (0:ℝ) ≤ (q:ℝ)^(ε/2) := Real.rpow_nonneg hqR0.le _
      have s1 : (4:ℝ)^(q.primeFactors.card) * (Real.sqrt (q:ℝ) * (C1 * (q:ℝ)^(ε/2) *
            ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ))))
          ≤ (C2 * (q:ℝ)^(ε/2)) * (Real.sqrt (q:ℝ) * (C1 * (q:ℝ)^(ε/2) *
            ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ)))) :=
        mul_le_mul_of_nonneg_right h4p (by positivity)
      have s2 : (C2 * (q:ℝ)^(ε/2)) * (Real.sqrt (q:ℝ) * (C1 * (q:ℝ)^(ε/2) *
            ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ))))
          = C1 * C2 * (q:ℝ)^ε * (Real.sqrt (q:ℝ) * ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ))) := by
        rw [← hpe]; ring
      have e1 : (H:ℝ)^4 * Real.sqrt (q:ℝ) + (H:ℝ)^2 * (q:ℝ)
          ≤ 2 * ((q:ℝ) * (H:ℝ)^2 + (H:ℝ)^4 * Real.sqrt (q:ℝ)) := by
        have := mul_comm ((H:ℝ)^2) ((q:ℝ))
        nlinarith only [hs0, this, hsq, hX0]
      have s4 : C1 * C2 * (q:ℝ)^ε *
            ((H:ℝ)^4 * Real.sqrt (q:ℝ) + (H:ℝ)^2 * (q:ℝ))
          ≤ (2 * (C1 * C2 + 1)) * (q:ℝ)^ε *
            ((q:ℝ) * (H:ℝ)^2 + (H:ℝ)^4 * Real.sqrt (q:ℝ)) := by
        have hAB0 : (0:ℝ) ≤ C1 * C2 := by positivity
        have hY0 : (0:ℝ) ≤ (q:ℝ) * (H:ℝ)^2 + (H:ℝ)^4 * Real.sqrt (q:ℝ) := by positivity
        calc C1 * C2 * (q:ℝ)^ε * ((H:ℝ)^4 * Real.sqrt (q:ℝ) + (H:ℝ)^2 * (q:ℝ))
            ≤ C1 * C2 * (q:ℝ)^ε *
                (2 * ((q:ℝ) * (H:ℝ)^2 + (H:ℝ)^4 * Real.sqrt (q:ℝ))) :=
              mul_le_mul_of_nonneg_left e1 (by positivity)
          _ = (C1 * C2 * 2) * (q:ℝ)^ε *
                ((q:ℝ) * (H:ℝ)^2 + (H:ℝ)^4 * Real.sqrt (q:ℝ)) := by ring
          _ ≤ (2 * (C1 * C2 + 1)) * (q:ℝ)^ε *
                ((q:ℝ) * (H:ℝ)^2 + (H:ℝ)^4 * Real.sqrt (q:ℝ)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only []) hqpe) hY0
      calc (4:ℝ)^(q.primeFactors.card) * Real.sqrt (q:ℝ) *
            (C1 * (q:ℝ)^(ε/2) * ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ)))
          = (4:ℝ)^(q.primeFactors.card) * (Real.sqrt (q:ℝ) * (C1 * (q:ℝ)^(ε/2) *
              ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ)))) := by ring
        _ ≤ (C2 * (q:ℝ)^(ε/2)) * (Real.sqrt (q:ℝ) * (C1 * (q:ℝ)^(ε/2) *
              ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ)))) := s1
        _ = C1 * C2 * (q:ℝ)^ε * (Real.sqrt (q:ℝ) *
              ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ))) := s2
        _ = C1 * C2 * (q:ℝ)^ε *
              ((H:ℝ)^4 * Real.sqrt (q:ℝ) + (H:ℝ)^2 * (q:ℝ)) := by rw [hsq]
        _ ≤ (2 * (C1 * C2 + 1)) * (q:ℝ)^ε *
              ((q:ℝ) * (H:ℝ)^2 + (H:ℝ)^4 * Real.sqrt (q:ℝ)) := s4
    have hA : (0:ℝ) ≤ (4:ℝ)^(q.primeFactors.card) * Real.sqrt (q:ℝ) := by positivity
    calc ‖∑ f : Fin 2 → Fin H, ∑ g : Fin 2 → Fin H, Tgq H 2 χ f g‖
        ≤ ∑ f : Fin 2 → Fin H, ∑ g : Fin 2 → Fin H, ‖Tgq H 2 χ f g‖ := hstep1
      _ ≤ ∑ f : Fin 2 → Fin H, ∑ g : Fin 2 → Fin H,
            (4:ℝ)^(q.primeFactors.card) * Real.sqrt (q:ℝ) *
              WL q ((f 0 : ℕ)+1) ((f 1 : ℕ)+1) ((g 0 : ℕ)+1) ((g 1 : ℕ)+1) := hstep2
      _ = (4:ℝ)^(q.primeFactors.card) * Real.sqrt (q:ℝ) *
            ∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
              ∑ d ∈ Finset.Icc 1 H, WL q a b c d := hstep3
      _ ≤ (4:ℝ)^(q.primeFactors.card) * Real.sqrt (q:ℝ) *
            (C1 * (q:ℝ)^(ε/2) * ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ))) :=
          mul_le_mul_of_nonneg_left hstep4 hA
      _ ≤ (2 * (C1 * C2 + 1)) * (q:ℝ)^ε *
            ((q:ℝ) * (H:ℝ)^2 + (H:ℝ)^4 * Real.sqrt (q:ℝ)) := hfinal

/-- **Burgess fourth-moment bound for squarefree modulus** (the `r = 2` case of the
moment input to Burgess's theorem). -/
theorem burgess_moment_squarefree_r2 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], Squarefree q →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ H : ℕ, H ≤ q →
        ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)‖ ^ 4
          ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ 2 + (H : ℝ) ^ 4 * Real.sqrt (q : ℝ)) :=
  burgess_moment_squarefree_r2_aux lcm_gcd_count_sqfree hε

end Commons.NumberTheory.DirichletCharacter
