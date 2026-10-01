import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.order_dvd_two_mul_of_primitive_prime_power
import Submission.Commons.NumberTheory.DirichletCharacter.primePowKernel_char_pow
import Submission.Commons.NumberTheory.DirichletCharacter.primePowSubgroup_quadratic_sum_bound
import Submission.Commons.NumberTheory.DirichletCharacter.p_pow_min_dvd_gcd_discriminant
import Submission.Commons.Algebra.BigOperators.sum_range_mul_eq
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation_criticalClasses
import Submission.Commons.NumberTheory.DirichletCharacter.sum_char_mul_conj
import Submission.Commons.NumberTheory.DirichletCharacter.primePowKernel_geom_sum_zmod
import Submission.Commons.NumberTheory.DirichletCharacter.rational_phase_sum_vanish
import Submission.Commons.NumberTheory.DirichletCharacter.rational_phase_sum_bound

namespace Commons.NumberTheory.DirichletCharacter

open scoped BigOperators

/-- `1 + p^(e-1)` is coprime to `p^e` (for `e ≥ 2`). -/
lemma coprime_one_add_prime_pow_top (p e : ℕ) [Fact p.Prime] (he : 2 ≤ e) :
    Nat.Coprime (1 + p^(e-1)) (p^e) := by
  refine Nat.Coprime.pow_right e ?_
  have h : 1 + p^(e-1) = 1 + p^(e-2) * p := by
    congr 1
    rw [show e - 1 = e - 2 + 1 by omega, pow_succ]
  rw [h]
  exact ((Nat.coprime_add_mul_right_right p 1 (p^(e-2))).mpr (Nat.coprime_one_right p)).symm

/-- `p^(e-1)` is nilpotent of square zero in `ZMod (p^e)` when `e ≥ 2`. -/
lemma sq_eq_zero_primePow_top (p e : ℕ) (he : 2 ≤ e) :
    ((p^(e-1) : ℕ) : ZMod (p^e)) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  have hle : e ≤ 2 * (e - 1) := by omega
  refine ⟨p ^ (2 * (e - 1) - e), ?_⟩
  rw [← pow_add, Nat.add_sub_cancel' hle,
      show (p ^ (e - 1)) ^ 2 = p ^ ((e-1)*2) from by rw [pow_mul],
      show (e-1)*2 = 2*(e-1) from by ring]

lemma pow_one_add_eq_of_sq_eq_zero' {R : Type*} [CommRing R] {a : R} (ha : a ^ 2 = 0) (n : ℕ) :
    (1 + a) ^ n = 1 + (n : R) * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    have h : (n : R) * a * a = 0 := by rw [mul_assoc, ← pow_two, ha, mul_zero]
    calc (1 + (n:R)*a) * (1+a) = 1 + (n:R)*a + a + (n:R)*a*a := by ring
      _ = 1 + (n:R)*a + a := by rw [h, add_zero]
      _ = 1 + ((n+1 : ℕ) : R)*a := by push_cast; ring

/-- **Primitive characters are non-trivial on the top kernel.** For `χ` primitive modulo `p^e`
(with `p` odd and `e ≥ 2`), `χ (1 + p^(e-1)) ≠ 1`. -/
theorem isPrimitive_top_ne_one (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p^e)) (hχ : χ.IsPrimitive) :
    χ (((1 + p^(e-1) : ℕ)) : ZMod (p^e)) ≠ 1 := by
  haveI : NeZero (p^e) := ⟨pow_ne_zero e (Fact.out : p.Prime).pos.ne'⟩
  have hd : p^(e-1) ∣ p^e := pow_dvd_pow p (by omega)
  set v : (ZMod (p^e))ˣ := ZMod.unitOfCoprime (1 + p^(e-1)) (coprime_one_add_prime_pow_top p e he) with hv
  have hvval : (v : ZMod (p^e)) = (((1 + p^(e-1) : ℕ)) : ZMod (p^e)) := by
    rw [hv, ZMod.coe_unitOfCoprime]
  have hvker : v ∈ (ZMod.unitsMap hd).ker := by
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [ZMod.unitsMap_val, hvval, ZMod.cast_natCast hd, Units.val_one]
    rw [show ((1 + p^(e-1) : ℕ) : ZMod (p^(e-1))) = 1 by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_self, add_zero]]
  have hvne : v ≠ 1 := by
    intro h1
    have h2 : (((1 + p^(e-1) : ℕ)) : ZMod (p^e)) = 1 := by rw [← hvval, h1]; rfl
    rw [Nat.cast_add, Nat.cast_one] at h2
    have h3 : (((p^(e-1) : ℕ)) : ZMod (p^e)) = 0 := by
      have h2' : (1 : ZMod (p^e)) + ((p^(e-1):ℕ):ZMod (p^e)) = 1 + 0 := by rw [add_zero]; exact h2
      exact add_left_cancel h2'
    rw [ZMod.natCast_eq_zero_iff] at h3
    have hlt : p^(e-1) < p^e := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
    have hpos : 0 < p^(e-1) := pow_pos (Fact.out : p.Prime).pos _
    have := Nat.le_of_dvd hpos h3
    omega
  have hvpow : v ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hvval]
    rw [show (((1 + p^(e-1) : ℕ)) : ZMod (p^e)) = 1 + ((p^(e-1) : ℕ) : ZMod (p^e)) by push_cast; ring]
    rw [pow_one_add_eq_of_sq_eq_zero' (sq_eq_zero_primePow_top p e he) p]
    rw [← Nat.cast_mul, show p * p^(e-1) = p^e by rw [← pow_succ']; congr 1; omega,
        ZMod.natCast_self, add_zero]
  have hordv : orderOf v = p := orderOf_eq_prime hvpow hvne
  have hkereq : (ZMod.unitsMap hd).ker = Subgroup.zpowers v := by
    have hle : Subgroup.zpowers v ≤ (ZMod.unitsMap hd).ker := Subgroup.zpowers_le.mpr hvker
    have hcard : Nat.card (ZMod.unitsMap hd).ker ≤ Nat.card (Subgroup.zpowers v) := by
      rw [Nat.card_zpowers, hordv]
      exact le_of_eq (card_ker_unitsMap_prime_pow (Fact.out : p.Prime) he hd)
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  intro hcon
  have hfac : χ.FactorsThrough (p^(e-1)) := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
    intro x hx
    rw [MonoidHom.mem_ker]
    rw [hkereq] at hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hv1 : χ.toUnitHom v = 1 := by
      apply Units.ext
      rw [MulChar.coe_toUnitHom, hvval]
      exact hcon
    rw [← hk, map_zpow, hv1, one_zpow]
  have hle : χ.conductor ≤ p^(e-1) := Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hfac)
  rw [(DirichletCharacter.isPrimitive_def χ).mp hχ] at hle
  have hlt : p^(e-1) < p^e := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
  omega

namespace CaseC

/-- Reindex a sum over `ZMod n` as a sum over `Finset.range n`. -/
lemma zmod_sum_univ_eq_sum_range' (n : ℕ) [NeZero n] {M : Type*} [AddCommMonoid M]
    (f : ZMod n → M) : ∑ x : ZMod n, f x = ∑ i ∈ Finset.range n, f (i : ZMod n) := by
  rw [Finset.sum_range]
  refine (Fintype.sum_equiv (Equiv.ofBijective (fun i : Fin n => ((i : ℕ) : ZMod n)) ?_) _ _ ?_).symm
  · constructor
    · intro i j hij
      simp only at hij
      have : (i : ℕ) % n = (j : ℕ) % n := by
        rw [← ZMod.natCast_eq_natCast_iff' i j n]; exact hij
      rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at this
      exact Fin.ext this
    · intro x
      refine ⟨⟨x.val, ZMod.val_lt x⟩, ?_⟩
      simp only
      rw [ZMod.natCast_zmod_val]
  · intro i
    rfl

lemma natAbs_pow_dvd_int {p m : ℕ} {A : ℤ} (h : p^m ∣ A.natAbs) : (p:ℤ)^m ∣ A := by
  have h2 : (((p^m : ℕ)) : ℤ) ∣ (A.natAbs : ℤ) := Nat.cast_dvd_cast h
  rw [Int.dvd_natAbs] at h2
  simpa using h2

lemma int_pow_dvd_natAbs {p m : ℕ} {A : ℤ} (h : (p:ℤ)^m ∣ A) : p^m ∣ A.natAbs := by
  have := (Int.natAbs_dvd_natAbs (a := ((p:ℤ))^m) (b := A)).mpr h
  simpa using this

lemma eq_C_add_C_mul_X_add_C_mul_X_sq {R : Type*} [CommSemiring R] (Q : Polynomial R)
    (h : Q.natDegree ≤ 2) :
    Q = Polynomial.C (Q.coeff 0) + Polynomial.C (Q.coeff 1) * Polynomial.X
        + Polynomial.C (Q.coeff 2) * Polynomial.X ^ 2 := by
  conv_lhs => rw [Q.as_sum_range_C_mul_X_pow]
  have hsum : (∑ i ∈ Finset.range (Q.natDegree + 1),
        Polynomial.C (Q.coeff i) * Polynomial.X ^ i)
      = ∑ i ∈ Finset.range 3, Polynomial.C (Q.coeff i) * Polynomial.X ^ i := by
    refine Finset.sum_subset (fun i hi => ?_) (fun i hi3 hni => ?_)
    · simp only [Finset.mem_range] at hi ⊢; omega
    · simp only [Finset.mem_range] at hi3 hni
      have : Q.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [this]
  rw [hsum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  ring

lemma eval_eq_coeff_deg2 {R : Type*} [CommSemiring R] (Q : Polynomial R) (h : Q.natDegree ≤ 2)
    (x : R) : Q.eval x = Q.coeff 0 + Q.coeff 1 * x + Q.coeff 2 * x ^ 2 := by
  conv_lhs => rw [eq_C_add_C_mul_X_add_C_mul_X_sq Q h]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]

lemma deriv_eval_eq_coeff_deg2 {R : Type*} [CommSemiring R] (Q : Polynomial R)
    (h : Q.natDegree ≤ 2) (x : R) :
    (Polynomial.derivative Q).eval x = Q.coeff 1 + 2 * Q.coeff 2 * x := by
  conv_lhs => rw [eq_C_add_C_mul_X_add_C_mul_X_sq Q h]
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_pow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_zero,
    Polynomial.eval_one]
  ring_nf

lemma eval_add_eq_deg2 {R : Type*} [CommRing R] (Q : Polynomial R) (h : Q.natDegree ≤ 2)
    (r s : R) : Q.eval (r + s) = Q.eval r + s * (Polynomial.derivative Q).eval r
      + s ^ 2 * Q.coeff 2 := by
  rw [eval_eq_coeff_deg2 Q h (r+s), eval_eq_coeff_deg2 Q h r, deriv_eval_eq_coeff_deg2 Q h r]
  ring

lemma eval_add_eq_deg1 {R : Type*} [CommRing R] (Q : Polynomial R) (h : Q.natDegree ≤ 1)
    (r s : R) : Q.eval (r + s) = Q.eval r + s * Q.coeff 1 := by
  have h2 : Q.natDegree ≤ 2 := by omega
  rw [eval_eq_coeff_deg2 Q h2 (r + s), eval_eq_coeff_deg2 Q h2 r]
  have hc2 : Q.coeff 2 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hc2]; ring

lemma linear_quadratic_expansion (p : ℕ) (H G : Polynomial ℤ) (hH : H.natDegree ≤ 1)
    (hG : G.natDegree ≤ 2) (r z γ : ℤ)
    (hγ : (H.derivative * G - H * G.derivative).eval r = (p : ℤ) * γ) :
    H.eval (r + (p:ℤ) * z) * G.eval r - H.eval r * G.eval (r + (p:ℤ) * z)
      = (p : ℤ)^2 * (γ * z - z^2 * H.eval r * G.coeff 2) := by
  have hG' : (Polynomial.derivative G).eval r = G.coeff 1 + 2 * G.coeff 2 * r :=
    deriv_eval_eq_coeff_deg2 G hG r
  have hH' : (Polynomial.derivative H).eval r = H.coeff 1 := by
    rw [deriv_eval_eq_coeff_deg2 H (by omega)]
    have h2 : H.coeff 2 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h2]; ring
  have hder : H.coeff 1 * G.eval r - H.eval r * (G.coeff 1 + 2 * G.coeff 2 * r) = (p:ℤ) * γ := by
    rw [← hγ, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, hH', hG']
  rw [eval_add_eq_deg1 H hH r ((p:ℤ)*z), eval_add_eq_deg2 G hG r ((p:ℤ)*z), hG']
  linear_combination ((p:ℤ)*z) * hder

end CaseC
namespace CaseC

def dif1 (a b c d : ℕ) : ℤ := (a:ℤ) + (b:ℤ) - (c:ℤ) - (d:ℤ)
def dif0 (a b c d : ℕ) : ℤ := (a:ℤ) * (b:ℤ) - (c:ℤ) * (d:ℤ)

variable {p : ℕ} [Fact p.Prime] {a b c d : ℕ}

lemma dif1_cast (hac : (a : ZMod p) = (c : ZMod p)) (hbd : (b : ZMod p) = (d : ZMod p)) :
    ((dif1 a b c d : ℤ) : ZMod p) = 0 := by
  rw [dif1]; push_cast; rw [hac, hbd]; ring

lemma dif0_cast (hac : (a : ZMod p) = (c : ZMod p)) (hbd : (b : ZMod p) = (d : ZMod p)) :
    ((dif0 a b c d : ℤ) : ZMod p) = 0 := by
  rw [dif0]; push_cast; rw [hac, hbd]; ring

lemma p_dvd_dif1 (hac : (a : ZMod p) = (c : ZMod p)) (hbd : (b : ZMod p) = (d : ZMod p)) :
    (p : ℤ) ∣ dif1 a b c d :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd (dif1 a b c d) p).mp (dif1_cast hac hbd)

lemma p_dvd_dif0 (hac : (a : ZMod p) = (c : ZMod p)) (hbd : (b : ZMod p) = (d : ZMod p)) :
    (p : ℤ) ∣ dif0 a b c d :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd (dif0 a b c d) p).mp (dif0_cast hac hbd)

end CaseC
namespace CaseC

/-- Existence of the maximal exponent `m`. -/
lemma exists_corrM (p e : ℕ) (A1 A0 : ℤ) :
    ∃ m : ℕ, m ≤ e ∧ (p : ℤ)^m ∣ A1 ∧ (p : ℤ)^m ∣ A0 ∧
      (∀ k ≤ e, (p:ℤ)^k ∣ A1 → (p:ℤ)^k ∣ A0 → k ≤ m) ∧
      (m = e ∨ ¬ ((p : ℤ)^(m+1) ∣ A1 ∧ (p : ℤ)^(m+1) ∣ A0)) := by
  classical
  set P : ℕ → Prop := fun k => p ^ k ∣ A1.natAbs ∧ p ^ k ∣ A0.natAbs with hP
  have key : P (Nat.findGreatest P e) :=
    Nat.findGreatest_spec (m := 0) (n := e) (Nat.zero_le e)
      (show P 0 from ⟨one_dvd _, one_dvd _⟩)
  refine ⟨Nat.findGreatest P e, Nat.findGreatest_le e,
    natAbs_pow_dvd_int key.1, natAbs_pow_dvd_int key.2, ?_, ?_⟩
  · intro k hk h1 h2
    exact Nat.le_findGreatest hk ⟨int_pow_dvd_natAbs h1, int_pow_dvd_natAbs h2⟩
  · by_cases h : Nat.findGreatest P e = e
    · exact Or.inl h
    · refine Or.inr ?_
      rintro ⟨h1, h2⟩
      have hlt : Nat.findGreatest P e < e :=
        lt_of_le_of_ne (Nat.findGreatest_le (P := P) e) h
      have hP1 : P (Nat.findGreatest P e + 1) :=
        ⟨int_pow_dvd_natAbs h1, int_pow_dvd_natAbs h2⟩
      exact Nat.findGreatest_is_greatest (n := e) (k := Nat.findGreatest P e + 1)
        (by omega) (by omega) hP1

end CaseC
namespace CaseC

/-- `h1 X + h0`. -/
noncomputable def Hpoly (h1 h0 : ℤ) : Polynomial ℤ :=
  Polynomial.C h1 * Polynomial.X + Polynomial.C h0

/-- `(X + c) * (X + d)`. -/
noncomputable def Gpoly (c d : ℕ) : Polynomial ℤ :=
  (Polynomial.X + Polynomial.C (c:ℤ)) * (Polynomial.X + Polynomial.C (d:ℤ))

/-- `H' G - H G'`, the stationary-phase critical polynomial. -/
noncomputable def Wpoly (h1 h0 : ℤ) (c d : ℕ) : Polynomial ℤ :=
  (Hpoly h1 h0).derivative * Gpoly c d - Hpoly h1 h0 * (Gpoly c d).derivative

lemma Gpoly_eq (c d : ℕ) : Gpoly c d = Polynomial.C ((c:ℤ)*(d:ℤ))
    + Polynomial.C ((c:ℤ) + (d:ℤ)) * Polynomial.X + Polynomial.X ^ 2 := by
  simp only [Gpoly]
  rw [Polynomial.C_add, Polynomial.C_mul]
  ring

lemma Hpoly_natDegree (h1 h0 : ℤ) : (Hpoly h1 h0).natDegree ≤ 1 := by
  have h1' : (Polynomial.C h1 * Polynomial.X).natDegree ≤ 1 := by
    simpa using Polynomial.natDegree_C_mul_X_pow_le h1 1
  have h0' : (Polynomial.C h0).natDegree ≤ 1 := by
    rw [Polynomial.natDegree_C]; omega
  rw [Hpoly]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le h1' h0')

lemma Hpoly_eval (h1 h0 : ℤ) (n : ℤ) : (Hpoly h1 h0).eval n = h1 * n + h0 := by
  simp only [Hpoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]

lemma Gpoly_natDegree (c d : ℕ) : (Gpoly c d).natDegree ≤ 2 := by
  have hA : (Polynomial.C ((c:ℤ)*(d:ℤ))
      + Polynomial.C ((c:ℤ) + (d:ℤ)) * Polynomial.X).natDegree ≤ 2 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_C _).trans_le (by norm_num)
    · simpa using (Polynomial.natDegree_C_mul_X_pow_le ((c:ℤ) + (d:ℤ)) 1).trans
        (show (1:ℕ) ≤ 2 by norm_num)
  calc (Gpoly c d).natDegree
      = (Polynomial.C ((c:ℤ)*(d:ℤ))
          + Polynomial.C ((c:ℤ) + (d:ℤ)) * Polynomial.X + Polynomial.X ^ 2).natDegree := by
        rw [Gpoly_eq]
    _ ≤ 2 := (Polynomial.natDegree_add_le _ _).trans (max_le hA (Polynomial.natDegree_X_pow_le 2))

lemma Gpoly_eval (c d : ℕ) (n : ℤ) : (Gpoly c d).eval n = (n + c) * (n + d) := by
  simp only [Gpoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]

lemma Gpoly_coeff1 (c d : ℕ) : (Gpoly c d).coeff 1 = (c:ℤ) + (d:ℤ) := by
  rw [Gpoly_eq]
  simp [Polynomial.coeff_add]

lemma Gpoly_coeff2 (c d : ℕ) : (Gpoly c d).coeff 2 = 1 := by
  rw [Gpoly_eq]
  simp [Polynomial.coeff_add]

lemma Hpoly_deriv (h1 h0 : ℤ) : (Hpoly h1 h0).derivative = Polynomial.C h1 := by
  simp [Hpoly]

lemma Gpoly_deriv (c d : ℕ) :
    (Gpoly c d).derivative = Polynomial.C (2:ℤ) * Polynomial.X + Polynomial.C ((c:ℤ)+(d:ℤ)) := by
  rw [Gpoly_eq]
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_C_mul_X, Polynomial.derivative_pow]
  simp
  ring

lemma Gpoly_deriv_natDegree (c d : ℕ) : (Gpoly c d).derivative.natDegree ≤ 1 := by
  rw [Gpoly_deriv]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simpa using Polynomial.natDegree_C_mul_X_pow_le (2:ℤ) 1
  · rw [Polynomial.natDegree_C]; omega

lemma Wpoly_eval_eq (h1 h0 : ℤ) (c d : ℕ) (r : ℤ) :
    (Wpoly h1 h0 c d).eval r =
      h1*(c:ℤ)*(d:ℤ) - h0*((c:ℤ)+(d:ℤ)) - 2*h0*r - h1*r^2 := by
  rw [Wpoly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, Hpoly_deriv,
    Gpoly_deriv, Hpoly_eval, Gpoly_eval]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

lemma Wpoly_natDegree (h1 h0 : ℤ) (c d : ℕ) : (Wpoly h1 h0 c d).natDegree ≤ 2 := by
  rw [Wpoly]
  have hA : ((Hpoly h1 h0).derivative * Gpoly c d).natDegree ≤ 2 := by
    rw [Hpoly_deriv]
    exact (Polynomial.natDegree_C_mul_le h1 (Gpoly c d)).trans (Gpoly_natDegree c d)
  have hB : (Hpoly h1 h0 * (Gpoly c d).derivative).natDegree ≤ 2 :=
    (Polynomial.natDegree_mul_le (p := Hpoly h1 h0) (q := (Gpoly c d).derivative)).trans
      (by have h1' := Hpoly_natDegree h1 h0; have h2 := Gpoly_deriv_natDegree c d; omega)
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le hA hB)

end CaseC
namespace CaseC

lemma isUnit_intCast_iff {p e : ℕ} (hp : p.Prime) (he : 0 < e) (m : ℤ) :
    IsUnit ((m : ℤ) : ZMod (p^e)) ↔ ¬ (p : ℤ) ∣ m := by
  haveI : NeZero (p^e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have key : IsUnit (((m.natAbs : ℕ)) : ZMod (p^e)) ↔ ¬ p ∣ m.natAbs :=
    ZMod.isUnit_natCast_iff_not_dvd_pow hp he
  have hnatabs : (p ∣ m.natAbs) ↔ ((p:ℤ) ∣ m) := by
    rw [← Int.natAbs_dvd_natAbs (a := (p:ℤ)) (b := m), Int.natAbs_natCast]
  rcases Int.natAbs_eq m with h | h
  · have h1 : ((m : ℤ) : ZMod (p^e)) = (((m.natAbs : ℕ)) : ZMod (p^e)) := by
      rw [h]; simp
    rw [h1, key, not_congr hnatabs]
  · have h1 : ((m : ℤ) : ZMod (p^e)) = -((((m.natAbs : ℕ)) : ZMod (p^e))) := by
      conv_lhs => rw [h]
      simp
    rw [h1, IsUnit.neg_iff, key, not_congr hnatabs]

lemma summand_eq {p e m : ℕ} [Fact p.Prime] {a b c d : ℕ} {h1 h0 : ℤ}
    (hh1 : (p:ℤ)^m * h1 = dif1 a b c d) (hh0 : (p:ℤ)^m * h0 = dif0 a b c d)
    (he0 : 0 < e) (χ : DirichletCharacter ℂ (p ^ e)) (x : ℤ)
    (hx : ¬ (p:ℤ) ∣ (Gpoly c d).eval x) :
    χ (((x : ZMod (p^e)) + (a : ZMod (p^e))) * ((x : ZMod (p^e)) + (b : ZMod (p^e))))
      * (starRingEnd ℂ) (χ (((x : ZMod (p^e)) + (c : ZMod (p^e)))
          * ((x : ZMod (p^e)) + (d : ZMod (p^e)))))
    = χ (1 + (p : ZMod (p^e))^m * (((Hpoly h1 h0).eval x : ℤ) : ZMod (p^e))
        * ((((Gpoly c d).eval x : ℤ) : ZMod (p^e)))⁻¹) := by
  haveI : NeZero (p^e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  have hunit : IsUnit (((Gpoly c d).eval x : ℤ) : ZMod (p^e)) :=
    (isUnit_intCast_iff (Fact.out : p.Prime) he0 _).mpr hx
  set Gx : ZMod (p^e) := (((Gpoly c d).eval x : ℤ) : ZMod (p^e)) with hGx
  have hGval : Gx = ((x : ZMod (p^e)) + (c : ZMod (p^e)))
      * ((x : ZMod (p^e)) + (d : ZMod (p^e))) := by
    rw [hGx, Gpoly_eval]; push_cast; ring
  have hGmul : Gx * Gx⁻¹ = 1 := ZMod.mul_inv_of_unit Gx hunit
  have hinv : χ Gx⁻¹ = (χ Gx)⁻¹ := by
    have h1 : χ Gx * χ Gx⁻¹ = 1 := by rw [← map_mul, hGmul, map_one]
    exact eq_inv_of_mul_eq_one_right h1
  have hconj : (starRingEnd ℂ) (χ (((x : ZMod (p^e)) + (c : ZMod (p^e)))
      * ((x : ZMod (p^e)) + (d : ZMod (p^e))))) = χ Gx⁻¹ := by
    rw [← hGval, Commons.NumberTheory.DirichletCharacter.conj_char_apply_eq_inv, hinv]
  have hfx : ((x + (a:ℤ)) * (x + (b:ℤ)) : ℤ) = (x + (c:ℤ)) * (x + (d:ℤ))
      + (p:ℤ)^m * (Hpoly h1 h0).eval x := by
    have hd : (x + (a:ℤ)) * (x + (b:ℤ))
        = (x + (c:ℤ)) * (x + (d:ℤ)) + dif1 a b c d * x + dif0 a b c d := by
      rw [dif1, dif0]; ring
    rw [hd, ← hh1, ← hh0, Hpoly_eval]
    ring
  have hfval : (((x + (a:ℤ)) * (x + (b:ℤ)) : ℤ) : ZMod (p^e))
      = Gx + (p : ZMod (p^e))^m * (((Hpoly h1 h0).eval x : ℤ) : ZMod (p^e)) := by
    have h2 : Gx = (((x + (c:ℤ)) * (x + (d:ℤ)) : ℤ) : ZMod (p^e)) := by
      rw [hGval]; push_cast; ring
    rw [hfx, h2]; push_cast; ring
  have harg1 : χ (((x : ZMod (p^e)) + (a : ZMod (p^e))) * ((x : ZMod (p^e)) + (b : ZMod (p^e))))
      = χ ((((x + (a:ℤ)) * (x + (b:ℤ)) : ℤ) : ZMod (p^e))) := by
    congr 1; push_cast; ring
  rw [harg1, hconj, ← map_mul, hfval]
  congr 1
  rw [add_mul, hGmul]

end CaseC
namespace CaseC

/-- The numerator `γ z - z^2 H(r) (G.coeff 2)` of the lifted phase. -/
noncomputable def N2poly (γ Hr g2 : ℤ) : Polynomial ℤ :=
  Polynomial.C γ * Polynomial.X - Polynomial.C (Hr * g2) * Polynomial.X ^ 2

lemma N2poly_eval (γ Hr g2 z : ℤ) : (N2poly γ Hr g2).eval z = γ * z - Hr * g2 * z ^ 2 := by
  simp only [N2poly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]

lemma N2poly_coeff2 (γ Hr g2 : ℤ) : (N2poly γ Hr g2).coeff 2 = -(Hr * g2) := by
  simp only [N2poly, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  norm_num

lemma N2poly_natDegree (γ Hr g2 : ℤ) : (N2poly γ Hr g2).natDegree ≤ 2 := by
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · simpa using (Polynomial.natDegree_C_mul_X_pow_le γ 1).trans (show (1:ℕ) ≤ 2 by norm_num)
  · exact Polynomial.natDegree_C_mul_X_pow_le (Hr*g2) 2

/-- The quadratic polynomial `G(r + p X)`. -/
noncomputable def Gzpoly (c d : ℕ) (r : ℤ) (p : ℕ) : Polynomial ℤ :=
  Polynomial.C ((Gpoly c d).eval r)
    + Polynomial.C ((p:ℤ) * ((Gpoly c d).derivative).eval r) * Polynomial.X
    + Polynomial.C ((p:ℤ)^2 * (Gpoly c d).coeff 2) * Polynomial.X ^ 2

lemma Gzpoly_eval (c d : ℕ) (r : ℤ) (p : ℕ) (z : ℤ) :
    (Gzpoly c d r p).eval z = (Gpoly c d).eval (r + (p:ℤ)*z) := by
  rw [eval_add_eq_deg2 (Gpoly c d) (Gpoly_natDegree c d) r ((p:ℤ)*z)]
  simp only [Gzpoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  rw [Gpoly_eval, deriv_eval_eq_coeff_deg2 (Gpoly c d) (Gpoly_natDegree c d) r,
    Gpoly_coeff1, Gpoly_coeff2]
  ring_nf

lemma Gzpoly_coeff (c d : ℕ) (r : ℤ) (p : ℕ) (i : ℕ) :
    (Gzpoly c d r p).coeff i
      = (if i = 0 then (Gpoly c d).eval r
         else if i = 1 then (p:ℤ) * ((Gpoly c d).derivative).eval r
         else if i = 2 then (p:ℤ)^2 * (Gpoly c d).coeff 2 else 0) := by
  simp only [Gzpoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X_pow]
  rcases i with _ | _ | _ | i <;> simp

/-- The denominator `G(r) * G(r + p X)` of the lifted phase. -/
noncomputable def G2poly (c d : ℕ) (r : ℤ) (p : ℕ) : Polynomial ℤ :=
  Polynomial.C ((Gpoly c d).eval r) * Gzpoly c d r p

lemma G2poly_eval (c d : ℕ) (r : ℤ) (p : ℕ) (z : ℤ) :
    (G2poly c d r p).eval z = (Gpoly c d).eval r * (Gpoly c d).eval (r + (p:ℤ)*z) := by
  rw [G2poly, Polynomial.eval_mul, Polynomial.eval_C, Gzpoly_eval]

lemma G2poly_coeff (c d : ℕ) (r : ℤ) (p : ℕ) (i : ℕ) :
    (G2poly c d r p).coeff i = (Gpoly c d).eval r * (Gzpoly c d r p).coeff i := by
  rw [G2poly, Polynomial.coeff_C_mul]

lemma G2poly_natDegree (c d : ℕ) (r : ℤ) (p : ℕ) : (G2poly c d r p).natDegree ≤ 2 := by
  refine (Polynomial.natDegree_mul_le (p := Polynomial.C ((Gpoly c d).eval r))
    (q := Gzpoly c d r p)).trans ?_
  have h1 : (Polynomial.C ((Gpoly c d).eval r)).natDegree = 0 := Polynomial.natDegree_C _
  have h2 : (Gzpoly c d r p).natDegree ≤ 2 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact (Polynomial.natDegree_C _).trans_le (by norm_num)
      · simpa using (Polynomial.natDegree_C_mul_X_pow_le ((p:ℤ) * ((Gpoly c d).derivative).eval r) 1).trans
          (show (1:ℕ) ≤ 2 by norm_num)
    · exact Polynomial.natDegree_C_mul_X_pow_le ((p:ℤ)^2 * (Gpoly c d).coeff 2) 2
  omega

lemma G2poly_coeff1 (c d : ℕ) (r : ℤ) (p : ℕ) :
    (G2poly c d r p).coeff 1 = (Gpoly c d).eval r * ((p:ℤ) * ((Gpoly c d).derivative).eval r) := by
  rw [G2poly_coeff, Gzpoly_coeff]; norm_num

lemma G2poly_coeff2 (c d : ℕ) (r : ℤ) (p : ℕ) :
    (G2poly c d r p).coeff 2 = (Gpoly c d).eval r * ((p:ℤ)^2 * (Gpoly c d).coeff 2) := by
  rw [G2poly_coeff, Gzpoly_coeff]; norm_num

lemma G2poly_coeff0 (c d : ℕ) (r : ℤ) (p : ℕ) :
    (G2poly c d r p).coeff 0 = (Gpoly c d).eval r * (Gpoly c d).eval r := by
  rw [G2poly_coeff, Gzpoly_coeff]; norm_num

end CaseC
namespace CaseC

/-- **Lifting the rational phase by one quadratic digit.** -/
lemma phase_expansion {p e m : ℕ} [Fact p.Prime] {c d : ℕ} {h1 h0 γ : ℤ} (r z : ℤ)
    (he0 : 0 < e)
    (hhγ : (Wpoly h1 h0 c d).eval r = (p:ℤ) * γ)
    (hr : ¬ (p:ℤ) ∣ (Gpoly c d).eval r) :
    (1 + (p : ZMod (p^e))^m * (((Hpoly h1 h0).eval (r + (p:ℤ)*z) : ℤ) : ZMod (p^e))
        * (((((Gpoly c d).eval (r + (p:ℤ)*z) : ℤ) : ZMod (p^e))))⁻¹)
      - (1 + (p : ZMod (p^e))^m * (((Hpoly h1 h0).eval r : ℤ) : ZMod (p^e))
        * (((((Gpoly c d).eval r : ℤ) : ZMod (p^e))))⁻¹)
      = (p : ZMod (p^e))^(m+2)
        * (((((N2poly γ ((Hpoly h1 h0).eval r) ((Gpoly c d).coeff 2)).eval z : ℤ) : ZMod (p^e))))
        * ((((((G2poly c d r p).eval z : ℤ) : ZMod (p^e)))))⁻¹ := by
  haveI : NeZero (p^e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  set P : ZMod (p^e) := (p : ZMod (p^e)) with hP
  set Av : ZMod (p^e) := (((Gpoly c d).eval (r + (p:ℤ)*z) : ℤ) : ZMod (p^e)) with hAv
  set Bv : ZMod (p^e) := (((Gpoly c d).eval r : ℤ) : ZMod (p^e)) with hBv
  set av : ZMod (p^e) := (((Hpoly h1 h0).eval (r + (p:ℤ)*z) : ℤ) : ZMod (p^e)) with hav
  set bv : ZMod (p^e) := (((Hpoly h1 h0).eval r : ℤ) : ZMod (p^e)) with hbv
  set Nv : ZMod (p^e) :=
    (((N2poly γ ((Hpoly h1 h0).eval r) ((Gpoly c d).coeff 2)).eval z : ℤ) : ZMod (p^e)) with hNv
  have hAval : ¬ (p:ℤ) ∣ (Gpoly c d).eval (r + (p:ℤ)*z) := by
    intro hc
    apply hr
    have hdiff : (Gpoly c d).eval (r + (p:ℤ)*z) - (Gpoly c d).eval r
        = (p:ℤ)*z * ((Gpoly c d).derivative).eval r + ((p:ℤ)*z)^2 * (Gpoly c d).coeff 2 := by
      rw [eval_add_eq_deg2 (Gpoly c d) (Gpoly_natDegree c d) r ((p:ℤ)*z)]; ring
    have hpd : (p:ℤ) ∣ (Gpoly c d).eval (r + (p:ℤ)*z) - (Gpoly c d).eval r := by
      rw [hdiff]
      refine dvd_add ?_ ?_
      · exact dvd_mul_of_dvd_left (dvd_mul_right (p:ℤ) z) _
      · rw [show ((p:ℤ)*z)^2 * (Gpoly c d).coeff 2
            = ((p:ℤ)*z) * (((p:ℤ)*z) * (Gpoly c d).coeff 2) by ring]
        exact dvd_mul_of_dvd_left (dvd_mul_right (p:ℤ) z) _
    have h3 := dvd_sub hc hpd
    rwa [show (Gpoly c d).eval (r + (p:ℤ)*z)
        - ((Gpoly c d).eval (r + (p:ℤ)*z) - (Gpoly c d).eval r)
        = (Gpoly c d).eval r by ring] at h3
  have hunitA : IsUnit Av := (isUnit_intCast_iff (Fact.out : p.Prime) he0 _).mpr hAval
  have hunitB : IsUnit Bv := (isUnit_intCast_iff (Fact.out : p.Prime) he0 _).mpr hr
  have hkeyZ : (Hpoly h1 h0).eval (r + (p:ℤ)*z) * (Gpoly c d).eval r
      - (Hpoly h1 h0).eval r * (Gpoly c d).eval (r + (p:ℤ)*z)
      = (p:ℤ)^2 * (N2poly γ ((Hpoly h1 h0).eval r) ((Gpoly c d).coeff 2)).eval z := by
    rw [linear_quadratic_expansion p _ _ (Hpoly_natDegree h1 h0) (Gpoly_natDegree c d) r z γ hhγ,
      N2poly_eval]
    ring
  have hkey : av * Bv - bv * Av = P^2 * Nv := by
    have h2 := congrArg (fun t : ℤ => (t : ZMod (p^e))) hkeyZ
    push_cast at h2
    rw [hP]
    simpa only [hav, hbv, hAv, hBv, hNv] using h2
  have hG2 : (((G2poly c d r p).eval z : ℤ) : ZMod (p^e)) = Bv * Av := by
    rw [G2poly_eval]; push_cast; ring
  have hAv1 : Av⁻¹ * Av = 1 := by rw [mul_comm, ZMod.mul_inv_of_unit Av hunitA]
  have hBv1 : Bv⁻¹ * Bv = 1 := by rw [mul_comm, ZMod.mul_inv_of_unit Bv hunitB]
  have hU : IsUnit (Bv * Av) := IsUnit.mul hunitB hunitA
  have hU1 : (Bv * Av)⁻¹ * (Bv * Av) = 1 := by rw [mul_comm, ZMod.mul_inv_of_unit _ hU]
  have step1 : av * Av⁻¹ - bv * Bv⁻¹ = (av * Bv - bv * Av) * (Bv * Av)⁻¹ := by
    refine IsUnit.mul_right_cancel hU ?_
    rw [mul_assoc, hU1, mul_one, sub_mul]
    have e1 : av * Av⁻¹ * (Bv * Av) = av * Bv := by
      rw [show av * Av⁻¹ * (Bv * Av) = av * (Av⁻¹ * Av) * Bv by ring, hAv1, mul_one]
    have e2 : bv * Bv⁻¹ * (Bv * Av) = bv * Av := by
      rw [show bv * Bv⁻¹ * (Bv * Av) = bv * (Bv⁻¹ * Bv) * Av by ring, hBv1, mul_one]
    rw [e1, e2]
  rw [show (1 + P^m * av * Av⁻¹) - (1 + P^m * bv * Bv⁻¹)
      = P^m * (av * Av⁻¹ - bv * Bv⁻¹) by ring, step1, hkey, hG2]
  ring

end CaseC
namespace CaseC

/-- The general shift identity for a linear numerator and quadratic denominator. -/
lemma linear_quadratic_shift (p : ℕ) (H G : Polynomial ℤ) (hH : H.natDegree ≤ 1)
    (hG : G.natDegree ≤ 2) (r z : ℤ) :
    H.eval (r + (p:ℤ) * z) * G.eval r - H.eval r * G.eval (r + (p:ℤ) * z)
      = (p:ℤ)*z * ((H.derivative * G - H * G.derivative).eval r)
        - ((p:ℤ)*z)^2 * H.eval r * G.coeff 2 := by
  have hG' : (Polynomial.derivative G).eval r = G.coeff 1 + 2 * G.coeff 2 * r :=
    deriv_eval_eq_coeff_deg2 G hG r
  have hH' : (Polynomial.derivative H).eval r = H.coeff 1 := by
    rw [deriv_eval_eq_coeff_deg2 H (by omega)]
    have h2 : H.coeff 2 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h2]; ring
  have hW : (H.derivative * G - H * G.derivative).eval r
      = H.coeff 1 * G.eval r - H.eval r * (G.coeff 1 + 2 * G.coeff 2 * r) := by
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, hH', hG']
  rw [eval_add_eq_deg1 H hH r ((p:ℤ)*z), eval_add_eq_deg2 G hG r ((p:ℤ)*z), hG', hW]
  ring

/-- Lifting the rational phase by one digit, in the "non-critical" normalization. -/
lemma phase_expansion_lin {p e m : ℕ} [Fact p.Prime] {c d : ℕ} {h1 h0 : ℤ} (r z : ℤ)
    (he0 : 0 < e) (hr : ¬ (p:ℤ) ∣ (Gpoly c d).eval r) :
    (1 + (p : ZMod (p^e))^m * (((Hpoly h1 h0).eval (r + (p:ℤ)*z) : ℤ) : ZMod (p^e))
        * (((((Gpoly c d).eval (r + (p:ℤ)*z) : ℤ) : ZMod (p^e))))⁻¹)
      - (1 + (p : ZMod (p^e))^m * (((Hpoly h1 h0).eval r : ℤ) : ZMod (p^e))
        * (((((Gpoly c d).eval r : ℤ) : ZMod (p^e))))⁻¹)
      = (p : ZMod (p^e))^(m+1)
        * (((N2poly ((Wpoly h1 h0 c d).eval r) ((Hpoly h1 h0).eval r)
              ((p:ℤ) * ((Gpoly c d).coeff 2))).eval z : ℤ) : ZMod (p^e))
        * ((((G2poly c d r p).eval z : ℤ) : ZMod (p^e)))⁻¹ := by
  haveI : NeZero (p^e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  set P : ZMod (p^e) := (p : ZMod (p^e)) with hP
  set Av : ZMod (p^e) := (((Gpoly c d).eval (r + (p:ℤ)*z) : ℤ) : ZMod (p^e)) with hAv
  set Bv : ZMod (p^e) := (((Gpoly c d).eval r : ℤ) : ZMod (p^e)) with hBv
  set av : ZMod (p^e) := (((Hpoly h1 h0).eval (r + (p:ℤ)*z) : ℤ) : ZMod (p^e)) with hav
  set bv : ZMod (p^e) := (((Hpoly h1 h0).eval r : ℤ) : ZMod (p^e)) with hbv
  set Nv : ZMod (p^e) :=
    (((N2poly ((Wpoly h1 h0 c d).eval r) ((Hpoly h1 h0).eval r)
      ((p:ℤ) * ((Gpoly c d).coeff 2))).eval z : ℤ) : ZMod (p^e)) with hNv
  have hAval : ¬ (p:ℤ) ∣ (Gpoly c d).eval (r + (p:ℤ)*z) := by
    intro hc
    apply hr
    have hdiff : (Gpoly c d).eval (r + (p:ℤ)*z) - (Gpoly c d).eval r
        = (p:ℤ)*z * ((Gpoly c d).derivative).eval r + ((p:ℤ)*z)^2 * (Gpoly c d).coeff 2 := by
      rw [eval_add_eq_deg2 (Gpoly c d) (Gpoly_natDegree c d) r ((p:ℤ)*z)]; ring
    have hpd : (p:ℤ) ∣ (Gpoly c d).eval (r + (p:ℤ)*z) - (Gpoly c d).eval r := by
      rw [hdiff]
      refine dvd_add ?_ ?_
      · exact dvd_mul_of_dvd_left (dvd_mul_right (p:ℤ) z) _
      · rw [show ((p:ℤ)*z)^2 * (Gpoly c d).coeff 2
            = ((p:ℤ)*z) * (((p:ℤ)*z) * (Gpoly c d).coeff 2) by ring]
        exact dvd_mul_of_dvd_left (dvd_mul_right (p:ℤ) z) _
    have h3 := dvd_sub hc hpd
    rwa [show (Gpoly c d).eval (r + (p:ℤ)*z)
        - ((Gpoly c d).eval (r + (p:ℤ)*z) - (Gpoly c d).eval r)
        = (Gpoly c d).eval r by ring] at h3
  have hunitA : IsUnit Av := (isUnit_intCast_iff (Fact.out : p.Prime) he0 _).mpr hAval
  have hunitB : IsUnit Bv := (isUnit_intCast_iff (Fact.out : p.Prime) he0 _).mpr hr
  have hkeyZ : (Hpoly h1 h0).eval (r + (p:ℤ)*z) * (Gpoly c d).eval r
      - (Hpoly h1 h0).eval r * (Gpoly c d).eval (r + (p:ℤ)*z)
      = (p:ℤ) * (N2poly ((Wpoly h1 h0 c d).eval r) ((Hpoly h1 h0).eval r)
          ((p:ℤ) * ((Gpoly c d).coeff 2))).eval z := by
    rw [linear_quadratic_shift p (Hpoly h1 h0) (Gpoly c d) (Hpoly_natDegree h1 h0)
      (Gpoly_natDegree c d) r z, N2poly_eval,
      show Wpoly h1 h0 c d = (Hpoly h1 h0).derivative * Gpoly c d
        - Hpoly h1 h0 * (Gpoly c d).derivative from rfl]
    ring
  have hkey : av * Bv - bv * Av = P * Nv := by
    have h2 := congrArg (fun t : ℤ => (t : ZMod (p^e))) hkeyZ
    push_cast at h2
    rw [hP]
    simpa only [hav, hbv, hAv, hBv, hNv] using h2
  have hG2 : (((G2poly c d r p).eval z : ℤ) : ZMod (p^e)) = Bv * Av := by
    rw [G2poly_eval]; push_cast; ring
  have hAv1 : Av⁻¹ * Av = 1 := by rw [mul_comm, ZMod.mul_inv_of_unit Av hunitA]
  have hBv1 : Bv⁻¹ * Bv = 1 := by rw [mul_comm, ZMod.mul_inv_of_unit Bv hunitB]
  have hU : IsUnit (Bv * Av) := IsUnit.mul hunitB hunitA
  have hU1 : (Bv * Av)⁻¹ * (Bv * Av) = 1 := by rw [mul_comm, ZMod.mul_inv_of_unit _ hU]
  have step1 : av * Av⁻¹ - bv * Bv⁻¹ = (av * Bv - bv * Av) * (Bv * Av)⁻¹ := by
    refine IsUnit.mul_right_cancel hU ?_
    rw [mul_assoc, hU1, mul_one, sub_mul]
    have e1 : av * Av⁻¹ * (Bv * Av) = av * Bv := by
      rw [show av * Av⁻¹ * (Bv * Av) = av * (Av⁻¹ * Av) * Bv by ring, hAv1, mul_one]
    have e2 : bv * Bv⁻¹ * (Bv * Av) = bv * Av := by
      rw [show bv * Bv⁻¹ * (Bv * Av) = bv * (Bv⁻¹ * Bv) * Av by ring, hBv1, mul_one]
    rw [e1, e2]
  rw [show (1 + P^m * av * Av⁻¹) - (1 + P^m * bv * Bv⁻¹)
      = P^m * (av * Av⁻¹ - bv * Bv⁻¹) by ring, step1, hkey, hG2]
  ring

end CaseC
namespace CaseC

/-- The point `r + p * i` of `ZMod (p^e)` attached to `r : ZMod p` and `i : ℕ`. -/
noncomputable def pt (p e : ℕ) (r : ZMod p) (i : ℕ) : ZMod (p ^ e) :=
  ((r.val + p * i : ℕ) : ZMod (p ^ e))

lemma pt_cast (p e : ℕ) (r : ZMod p) (i : ℕ) :
    pt p e r i = (((r.val : ℤ) + (p:ℤ) * (i:ℤ) : ℤ) : ZMod (p^e)) := by
  simp only [pt]; push_cast; ring

/-- For a bad `r` (where `G r ≡ 0 mod p`), every summand of the inner sum vanishes. -/
lemma bad_term_zero {p e : ℕ} [Fact p.Prime] {a b c d : ℕ} (χ : DirichletCharacter ℂ (p^e))
    (he0 : 0 < e) (r : ZMod p) (i : ℕ)
    (hr : (p:ℤ) ∣ (Gpoly c d).eval (r.val : ℤ)) :
    χ ((pt p e r i + (a : ZMod (p^e))) * (pt p e r i + (b : ZMod (p^e))))
      * (starRingEnd ℂ)
          (χ ((pt p e r i + (c : ZMod (p^e))) * (pt p e r i + (d : ZMod (p^e))))) = 0 := by
  haveI : NeZero (p^e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  have hdiv : (p:ℤ) ∣ (Gpoly c d).eval ((r.val : ℤ) + (p:ℤ)*(i:ℤ)) := by
    have hdiff : (Gpoly c d).eval ((r.val : ℤ) + (p:ℤ)*(i:ℤ))
        = (Gpoly c d).eval (r.val:ℤ) + (p:ℤ)*(i:ℤ) * ((Gpoly c d).derivative).eval (r.val:ℤ)
          + ((p:ℤ)*(i:ℤ))^2 * (Gpoly c d).coeff 2 := by
      rw [eval_add_eq_deg2 (Gpoly c d) (Gpoly_natDegree c d) (r.val:ℤ) ((p:ℤ)*(i:ℤ))]
    rw [hdiff]
    refine dvd_add (dvd_add hr ?_) ?_
    · exact dvd_mul_of_dvd_left (dvd_mul_right (p:ℤ) (i:ℤ)) _
    · rw [show ((p:ℤ)*(i:ℤ))^2 * (Gpoly c d).coeff 2
          = ((p:ℤ)*(i:ℤ)) * (((p:ℤ)*(i:ℤ)) * (Gpoly c d).coeff 2) by ring]
      exact dvd_mul_of_dvd_left (dvd_mul_right (p:ℤ) (i:ℤ)) _
  have hnonunit : ¬ IsUnit (((Gpoly c d).eval ((r.val : ℤ) + (p:ℤ)*(i:ℤ)) : ℤ) : ZMod (p^e)) :=
    fun h => ((isUnit_intCast_iff (Fact.out : p.Prime) he0 _).mp h) hdiv
  have hval : (pt p e r i + (c : ZMod (p^e))) * (pt p e r i + (d : ZMod (p^e)))
      = (((Gpoly c d).eval ((r.val : ℤ) + (p:ℤ)*(i:ℤ)) : ℤ) : ZMod (p^e)) := by
    rw [pt_cast, Gpoly_eval]; push_cast; ring
  rw [hval]
  have h0 : χ ((((Gpoly c d).eval ((r.val : ℤ) + (p:ℤ)*(i:ℤ)) : ℤ) : ZMod (p^e))) = 0 :=
    MulChar.map_nonunit χ hnonunit
  rw [h0, map_zero, mul_zero]

lemma G_add_ne_zero {p : ℕ} {c d : ℕ} (r z : ℤ)
    (hr : ¬ (p:ℤ) ∣ (Gpoly c d).eval r) :
    ¬ (p:ℤ) ∣ (Gpoly c d).eval (r + (p:ℤ)*z) := by
  intro hc
  apply hr
  have hdiff : (Gpoly c d).eval (r + (p:ℤ)*z) - (Gpoly c d).eval r
      = (p:ℤ)*z * ((Gpoly c d).derivative).eval r + ((p:ℤ)*z)^2 * (Gpoly c d).coeff 2 := by
    rw [eval_add_eq_deg2 (Gpoly c d) (Gpoly_natDegree c d) r ((p:ℤ)*z)]; ring
  have hpd : (p:ℤ) ∣ (Gpoly c d).eval (r + (p:ℤ)*z) - (Gpoly c d).eval r := by
    rw [hdiff]
    refine dvd_add ?_ ?_
    · exact dvd_mul_of_dvd_left (dvd_mul_right (p:ℤ) z) _
    · rw [show ((p:ℤ)*z)^2 * (Gpoly c d).coeff 2
          = ((p:ℤ)*z) * (((p:ℤ)*z) * (Gpoly c d).coeff 2) by ring]
      exact dvd_mul_of_dvd_left (dvd_mul_right (p:ℤ) z) _
  have h3 := dvd_sub hc hpd
  rwa [show (Gpoly c d).eval (r + (p:ℤ)*z)
      - ((Gpoly c d).eval (r + (p:ℤ)*z) - (Gpoly c d).eval r)
      = (Gpoly c d).eval r by ring] at h3

/-- If `r` is critical and good then `H r` is not divisible by `p`. -/
lemma not_dvd_H_of_crit {p : ℕ} [Fact p.Prime] {c d : ℕ} {h1 h0 : ℤ}
    (hhne : ¬ ((p:ℤ) ∣ h1 ∧ (p:ℤ) ∣ h0)) (r : ℤ)
    (hr : ¬ (p:ℤ) ∣ (Gpoly c d).eval r)
    (hcrit : (p:ℤ) ∣ (Wpoly h1 h0 c d).eval r) :
    ¬ (p:ℤ) ∣ (Hpoly h1 h0).eval r := by
  intro hH
  rw [Hpoly_eval] at hH
  have hp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hW : (p:ℤ) ∣ h1 * (Gpoly c d).eval r := by
    have hWs : (Wpoly h1 h0 c d).eval r
        = h1 * (Gpoly c d).eval r - (h1 * r + h0) * ((Gpoly c d).derivative).eval r := by
      rw [Wpoly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, Hpoly_deriv,
        Hpoly_eval, Polynomial.eval_C]
    rw [hWs] at hcrit
    have : (p:ℤ) ∣ (h1 * r + h0) * ((Gpoly c d).derivative).eval r :=
      dvd_mul_of_dvd_left hH _
    have h3 := dvd_add hcrit this
    rwa [show h1 * (Gpoly c d).eval r - (h1 * r + h0) * ((Gpoly c d).derivative).eval r
        + (h1 * r + h0) * ((Gpoly c d).derivative).eval r
        = h1 * (Gpoly c d).eval r by ring] at h3
  have h1dvd : (p:ℤ) ∣ h1 := (hp.dvd_mul.mp hW).resolve_right hr
  have h0dvd : (p:ℤ) ∣ h0 := by
    have : (p:ℤ) ∣ h1 * r := dvd_mul_of_dvd_left h1dvd r
    have h3 := dvd_sub hH this
    rwa [show h1 * r + h0 - h1 * r = h0 by ring] at h3
  exact hhne ⟨h1dvd, h0dvd⟩

end CaseC
namespace CaseC

lemma good_sum_crit {p e m : ℕ} [Fact p.Prime] (he : 2 ≤ e) {a b c d : ℕ} {h1 h0 γ : ℤ}
    (hh1 : (p:ℤ)^m * h1 = dif1 a b c d) (hh0 : (p:ℤ)^m * h0 = dif0 a b c d)
    (χ : DirichletCharacter ℂ (p^e)) (r : ZMod p)
    (hr : ¬ (p:ℤ) ∣ (Gpoly c d).eval (r.val : ℤ))
    (hhγ : (Wpoly h1 h0 c d).eval (r.val : ℤ) = (p:ℤ) * γ) :
    (∑ i ∈ Finset.range (p^(e-2)),
        χ ((pt p e r i + (a : ZMod (p^e))) * (pt p e r i + (b : ZMod (p^e))))
          * (starRingEnd ℂ)
              (χ ((pt p e r i + (c : ZMod (p^e))) * (pt p e r i + (d : ZMod (p^e))))))
      = ∑ i ∈ Finset.range (p^(e-2)),
          χ ((1 + (p : ZMod (p^e))^m
                * (((Hpoly h1 h0).eval (r.val : ℤ) : ℤ) : ZMod (p^e))
                * ((((Gpoly c d).eval (r.val : ℤ) : ℤ) : ZMod (p^e)))⁻¹)
            + (p : ZMod (p^e))^(m+2)
              * (((N2poly γ ((Hpoly h1 h0).eval (r.val : ℤ)) ((Gpoly c d).coeff 2)).eval (i : ℤ) : ℤ)
                  : ZMod (p^e))
              * ((((G2poly c d (r.val : ℤ) p).eval (i : ℤ) : ℤ) : ZMod (p^e)))⁻¹) := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hnd := G_add_ne_zero (c := c) (d := d) (r.val : ℤ) ((i:ℤ)) hr
  rw [pt_cast, summand_eq hh1 hh0 (by omega) χ ((r.val : ℤ) + (p:ℤ)*(i:ℤ)) hnd]
  congr 1
  have hph := phase_expansion (p := p) (e := e) (m := m) (c := c) (d := d)
    (h1 := h1) (h0 := h0) (γ := γ) (r.val : ℤ) (i : ℤ) (by omega) hhγ hr
  rw [← hph]
  ring

lemma good_sum_noncrit {p e m : ℕ} [Fact p.Prime] (he : 2 ≤ e) {a b c d : ℕ} {h1 h0 : ℤ}
    (hh1 : (p:ℤ)^m * h1 = dif1 a b c d) (hh0 : (p:ℤ)^m * h0 = dif0 a b c d)
    (χ : DirichletCharacter ℂ (p^e)) (r : ZMod p)
    (hr : ¬ (p:ℤ) ∣ (Gpoly c d).eval (r.val : ℤ)) :
    (∑ i ∈ Finset.range (p^(e-2)),
        χ ((pt p e r i + (a : ZMod (p^e))) * (pt p e r i + (b : ZMod (p^e))))
          * (starRingEnd ℂ)
              (χ ((pt p e r i + (c : ZMod (p^e))) * (pt p e r i + (d : ZMod (p^e))))))
      = ∑ i ∈ Finset.range (p^(e-2)),
          χ ((1 + (p : ZMod (p^e))^m
                * (((Hpoly h1 h0).eval (r.val : ℤ) : ℤ) : ZMod (p^e))
                * ((((Gpoly c d).eval (r.val : ℤ) : ℤ) : ZMod (p^e)))⁻¹)
            + (p : ZMod (p^e))^(m+1)
              * (((N2poly ((Wpoly h1 h0 c d).eval (r.val : ℤ)) ((Hpoly h1 h0).eval (r.val : ℤ))
                    ((p:ℤ) * ((Gpoly c d).coeff 2))).eval (i : ℤ) : ℤ) : ZMod (p^e))
              * ((((G2poly c d (r.val : ℤ) p).eval (i : ℤ) : ℤ) : ZMod (p^e)))⁻¹) := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hnd := G_add_ne_zero (c := c) (d := d) (r.val : ℤ) ((i:ℤ)) hr
  rw [pt_cast, summand_eq hh1 hh0 (by omega) χ ((r.val : ℤ) + (p:ℤ)*(i:ℤ)) hnd]
  congr 1
  have hph := phase_expansion_lin (p := p) (e := e) (m := m) (c := c) (d := d)
    (h1 := h1) (h0 := h0) (r.val : ℤ) (i : ℤ) (by omega) hr
  rw [← hph]
  ring

end CaseC
namespace CaseC

end CaseC
namespace CaseC

lemma crit_inner_bound {p e m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 2 ≤ e)
    (hm1 : 1 ≤ m) (hme : m ≤ e - 4)
    (χ : DirichletCharacter ℂ (p^e))
    (htop : χ ((((1 + p ^ (e - 1) : ℕ)) : ZMod (p ^ e))) ≠ 1)
    {c d : ℕ} {h1 h0 : ℤ}
    (hhne : ¬ ((p:ℤ) ∣ h1 ∧ (p:ℤ) ∣ h0))
    (r : ZMod p) (hr : ¬ (p:ℤ) ∣ (Gpoly c d).eval (r.val : ℤ))
    (γ : ℤ) (hhγ : (Wpoly h1 h0 c d).eval (r.val : ℤ) = (p:ℤ) * γ) :
    ‖∑ i ∈ Finset.range (p^(e-2)),
        χ ((1 + (p : ZMod (p^e))^m
              * (((Hpoly h1 h0).eval (r.val : ℤ) : ℤ) : ZMod (p^e))
              * ((((Gpoly c d).eval (r.val : ℤ) : ℤ) : ZMod (p^e)))⁻¹)
          + (p : ZMod (p^e))^(m+2)
            * (((N2poly γ ((Hpoly h1 h0).eval (r.val : ℤ)) ((Gpoly c d).coeff 2)).eval (i : ℤ) : ℤ)
                : ZMod (p^e))
            * ((((G2poly c d (r.val : ℤ) p).eval (i : ℤ) : ℤ) : ZMod (p^e)))⁻¹)‖
      ≤ (p : ℝ) ^ (((e + m - 1 : ℕ) : ℝ) / 2) := by
  set A : ZMod (p^e) := 1 + (p : ZMod (p^e))^m
      * (((Hpoly h1 h0).eval (r.val : ℤ) : ℤ) : ZMod (p^e))
      * ((((Gpoly c d).eval (r.val : ℤ) : ℤ) : ZMod (p^e)))⁻¹ with hAdef
  set N₂ : Polynomial ℤ := N2poly γ ((Hpoly h1 h0).eval (r.val : ℤ)) ((Gpoly c d).coeff 2) with hNdef
  set G₂ : Polynomial ℤ := G2poly c d (r.val : ℤ) p with hGdef
  have hA : (p : ZMod (p^e)) ∣ A - 1 := by
    refine ⟨(p : ZMod (p^e))^(m-1)
        * (((Hpoly h1 h0).eval (r.val : ℤ) : ℤ) : ZMod (p^e))
        * ((((Gpoly c d).eval (r.val : ℤ) : ℤ) : ZMod (p^e)))⁻¹, ?_⟩
    have hpm : (p : ZMod (p^e))^m = (p : ZMod (p^e))^(m-1) * (p : ZMod (p^e)) := by
      rw [← pow_succ]; congr 1; omega
    rw [hAdef, hpm]; ring
  have hN2 : ¬ (p : ℤ) ∣ N₂.coeff 2 := by
    rw [hNdef, N2poly_coeff2, Gpoly_coeff2, mul_one]
    intro hd
    exact not_dvd_H_of_crit hhne (r.val : ℤ) hr ⟨γ, hhγ⟩ (dvd_neg.mp hd)
  have hN : N₂.natDegree ≤ 2 := by rw [hNdef]; exact N2poly_natDegree _ _ _
  have hG : G₂.natDegree ≤ 2 := by rw [hGdef]; exact G2poly_natDegree c d (r.val : ℤ) p
  have hG1 : (p : ℤ) ∣ G₂.coeff 1 := by
    rw [hGdef, G2poly_coeff1]
    exact dvd_mul_of_dvd_right (dvd_mul_right (p:ℤ) _) _
  have hG2 : (p : ℤ) ∣ G₂.coeff 2 := by
    rw [hGdef, G2poly_coeff2, pow_two]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_right (p:ℤ) (p:ℤ)) _) _
  have hG0 : ¬ (p : ℤ) ∣ G₂.coeff 0 := by
    rw [hGdef, G2poly_coeff0]
    have hp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
    exact fun hd => hr ((hp.dvd_mul.mp hd).elim id id)
  have hb := Commons.NumberTheory.DirichletCharacter.rational_phase_sum_bound p e (m+2) (e-2)
    hp2 he χ htop (by omega) (by omega)
    (by omega) A hA N₂ G₂ hN hN2 hG hG1 hG2 hG0
  have hexp : ((2 * (e - 2) + (m + 2) - e : ℕ) : ℝ) / 2 + 1/2 = (((e + m - 1 : ℕ)) : ℝ) / 2 := by
    have h1 : 2 * (e - 2) + (m + 2) - e = e + m - 2 := by omega
    have h2 : e + m - 1 = (e + m - 2) + 1 := by omega
    rw [h1, h2]; push_cast; ring
  rw [hexp] at hb
  simpa only [hAdef, hNdef, hGdef] using hb

end CaseC
namespace CaseC

lemma noncrit_inner_zero {p e m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 2 ≤ e)
    (hm1 : 1 ≤ m) (hme : m ≤ e - 4)
    (χ : DirichletCharacter ℂ (p^e))
    (htop : χ ((((1 + p ^ (e - 1) : ℕ)) : ZMod (p ^ e))) ≠ 1)
    {c d : ℕ} {h1 h0 : ℤ}
    (r : ZMod p) (hr : ¬ (p:ℤ) ∣ (Gpoly c d).eval (r.val : ℤ))
    (hnc : ¬ (p:ℤ) ∣ (Wpoly h1 h0 c d).eval (r.val : ℤ)) :
    (∑ i ∈ Finset.range (p^(e-2)),
        χ ((1 + (p : ZMod (p^e))^m
              * (((Hpoly h1 h0).eval (r.val : ℤ) : ℤ) : ZMod (p^e))
              * ((((Gpoly c d).eval (r.val : ℤ) : ℤ) : ZMod (p^e)))⁻¹)
          + (p : ZMod (p^e))^(m+1)
            * (((N2poly ((Wpoly h1 h0 c d).eval (r.val : ℤ)) ((Hpoly h1 h0).eval (r.val : ℤ))
                  ((p:ℤ) * ((Gpoly c d).coeff 2))).eval (i : ℤ) : ℤ) : ZMod (p^e))
            * ((((G2poly c d (r.val : ℤ) p).eval (i : ℤ) : ℤ) : ZMod (p^e)))⁻¹)) = 0 := by
  set A : ZMod (p^e) := 1 + (p : ZMod (p^e))^m
      * (((Hpoly h1 h0).eval (r.val : ℤ) : ℤ) : ZMod (p^e))
      * ((((Gpoly c d).eval (r.val : ℤ) : ℤ) : ZMod (p^e)))⁻¹ with hAdef
  set N₂ : Polynomial ℤ := N2poly ((Wpoly h1 h0 c d).eval (r.val : ℤ))
      ((Hpoly h1 h0).eval (r.val : ℤ)) ((p:ℤ) * ((Gpoly c d).coeff 2)) with hNdef
  set G₂ : Polynomial ℤ := G2poly c d (r.val : ℤ) p with hGdef
  have hA : (p : ZMod (p^e)) ∣ A - 1 := by
    refine ⟨(p : ZMod (p^e))^(m-1)
        * (((Hpoly h1 h0).eval (r.val : ℤ) : ℤ) : ZMod (p^e))
        * ((((Gpoly c d).eval (r.val : ℤ) : ℤ) : ZMod (p^e)))⁻¹, ?_⟩
    have hpm : (p : ZMod (p^e))^m = (p : ZMod (p^e))^(m-1) * (p : ZMod (p^e)) := by
      rw [← pow_succ]; congr 1; omega
    rw [hAdef, hpm]; ring
  have hN : N₂.natDegree ≤ 2 := by rw [hNdef]; exact N2poly_natDegree _ _ _
  have hN2 : (p : ℤ) ∣ N₂.coeff 2 := by
    rw [hNdef, N2poly_coeff2]
    exact dvd_neg.mpr (dvd_mul_of_dvd_right (dvd_mul_right (p:ℤ) ((Gpoly c d).coeff 2)) _)
  have hN1 : ¬ (p : ℤ) ∣ N₂.coeff 1 := by
    rw [hNdef]
    have : (N2poly ((Wpoly h1 h0 c d).eval (r.val : ℤ)) ((Hpoly h1 h0).eval (r.val : ℤ))
        ((p:ℤ) * ((Gpoly c d).coeff 2))).coeff 1 = (Wpoly h1 h0 c d).eval (r.val : ℤ) := by
      simp only [N2poly, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X,
        Polynomial.coeff_C_mul_X_pow]
      norm_num
    rw [this]; exact hnc
  have hG : G₂.natDegree ≤ 2 := by rw [hGdef]; exact G2poly_natDegree c d (r.val : ℤ) p
  have hG1 : (p : ℤ) ∣ G₂.coeff 1 := by
    rw [hGdef, G2poly_coeff1]
    exact dvd_mul_of_dvd_right (dvd_mul_right (p:ℤ) _) _
  have hG2 : (p : ℤ) ∣ G₂.coeff 2 := by
    rw [hGdef, G2poly_coeff2, pow_two]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_right (p:ℤ) (p:ℤ)) _) _
  have hG0 : ¬ (p : ℤ) ∣ G₂.coeff 0 := by
    rw [hGdef, G2poly_coeff0]
    have hp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
    exact fun hd => hr ((hp.dvd_mul.mp hd).elim id id)
  have hb := Commons.NumberTheory.DirichletCharacter.rational_phase_sum_vanish p e (m+1) (e-2)
    hp2 he χ htop (by omega) (by omega) (by omega) A hA N₂ G₂ hN hN2 hN1 hG hG1 hG2 hG0
  simpa only [hAdef, hNdef, hGdef] using hb

end CaseC
namespace CaseC

lemma crit_card_le_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {c d : ℕ} {h1 h0 : ℤ}
    (hhne : ¬ ((p:ℤ) ∣ h1 ∧ (p:ℤ) ∣ h0)) :
    ((Finset.univ : Finset (ZMod p)).filter
      (fun r => (p:ℤ) ∣ (Wpoly h1 h0 c d).eval (r.val : ℤ))).card ≤ 2 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set Q : Polynomial (ZMod p) :=
      Polynomial.C (((h1*(c:ℤ)*(d:ℤ) - h0*((c:ℤ)+(d:ℤ)) : ℤ) : ZMod p))
      + Polynomial.C (((-2*h0 : ℤ) : ZMod p)) * Polynomial.X
      + Polynomial.C (((-h1 : ℤ) : ZMod p)) * Polynomial.X^2 with hQdef
  have hQcoeff2 : Q.coeff 2 = (((-h1 : ℤ) : ZMod p)) := by
    rw [hQdef]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow]
    norm_num
  have hQcoeff1 : Q.coeff 1 = (((-2*h0 : ℤ) : ZMod p)) := by
    rw [hQdef]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow]
    norm_num
  have hQ0 : Q ≠ 0 := by
    intro hzero
    have h2 : (((-h1 : ℤ) : ZMod p)) = 0 := by rw [← hQcoeff2, hzero]; simp
    have h1' : (((-2*h0 : ℤ) : ZMod p)) = 0 := by rw [← hQcoeff1, hzero]; simp
    have hd1 : (p:ℤ) ∣ h1 := by
      have : ((-h1 : ℤ) : ZMod p) = 0 := h2
      exact dvd_neg.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd (-h1) p).mp this)
    have hd2 : (p:ℤ) ∣ h0 := by
      have hc : ((-2*h0 : ℤ) : ZMod p) = 0 := h1'
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (-2*h0) p).mp hc
      have h2' : (p:ℤ) ∣ 2 * h0 := by
        rw [show ((-2*h0 : ℤ)) = -(2*h0) by ring] at this
        exact dvd_neg.mp this
      have hp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
      rcases hp.dvd_mul.mp h2' with h | h
      · have hnat : p ∣ 2 := by exact_mod_cast h
        rcases (Nat.dvd_prime Nat.prime_two).mp hnat with hh | hh
        · exact absurd hh (Fact.out : p.Prime).ne_one
        · exact absurd hh hp2
      · exact h
    exact hhne ⟨hd1, hd2⟩
  have hQeval : ∀ r : ZMod p, Q.eval r = (((Wpoly h1 h0 c d).eval (r.val : ℤ) : ℤ) : ZMod p) := by
    intro r
    conv_lhs => rw [← ZMod.natCast_zmod_val r]
    rw [hQdef, Wpoly_eval_eq]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_pow]
    push_cast
    ring
  have hQdeg : Q.natDegree ≤ 2 := by
    rw [hQdef]
    have hA : (Polynomial.C (((h1*(c:ℤ)*(d:ℤ) - h0*((c:ℤ)+(d:ℤ)) : ℤ) : ZMod p))
        + Polynomial.C (((-2*h0 : ℤ) : ZMod p)) * Polynomial.X).natDegree ≤ 2 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact (Polynomial.natDegree_C _).trans_le (by norm_num)
      · simpa using (Polynomial.natDegree_C_mul_X_pow_le (((-2*h0 : ℤ) : ZMod p)) 1).trans
          (show (1:ℕ) ≤ 2 by norm_num)
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le hA (Polynomial.natDegree_C_mul_X_pow_le _ 2))
  have hsub : ((Finset.univ : Finset (ZMod p)).filter
      (fun r => (p:ℤ) ∣ (Wpoly h1 h0 c d).eval (r.val : ℤ))) ⊆ Q.roots.toFinset := by
    intro r hr
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ0, Polynomial.IsRoot.def, hQeval,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact (Finset.mem_filter.mp hr).2
  calc ((Finset.univ : Finset (ZMod p)).filter
      (fun r => (p:ℤ) ∣ (Wpoly h1 h0 c d).eval (r.val : ℤ))).card
      ≤ Q.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Q.roots.card := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := Polynomial.card_roots' Q
    _ ≤ 2 := hQdeg

end CaseC
namespace CaseC

/-- The correlation summand at a point `x`. -/
noncomputable def csm (p e : ℕ) (χ : DirichletCharacter ℂ (p^e)) (a b c d : ℕ)
    (x : ZMod (p^e)) : ℂ :=
  χ ((x + (a : ZMod (p^e))) * (x + (b : ZMod (p^e))))
    * (starRingEnd ℂ) (χ ((x + (c : ZMod (p^e))) * (x + (d : ZMod (p^e)))))

lemma pt_eq (p e : ℕ) (r : ZMod p) (i : ℕ) :
    pt p e r i = (((r.val : ℕ)) : ZMod (p^e)) + (((p:ℕ)) : ZMod (p^e)) * (((i:ℕ)) : ZMod (p^e)) := by
  simp only [pt]; push_cast; ring

lemma inner_sum_reindex {p e : ℕ} [Fact p.Prime] (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p^e)) {a b c d : ℕ} (r : ZMod p) :
    (∑ z : ZMod (p^(e-2)),
        csm p e χ a b c d ((((r.val : ℕ)) : ZMod (p^e))
          + (((p:ℕ)) : ZMod (p^e)) * (((z.val : ℕ)) : ZMod (p^e))))
      = ∑ i ∈ Finset.range (p^(e-2)), csm p e χ a b c d (pt p e r i) := by
  haveI : NeZero (p^(e-2)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [zmod_sum_univ_eq_sum_range']
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hv : ((i : ZMod (p^(e-2))).val) = i := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
  rw [hv, pt_eq]

lemma correlation_bound_of_m {p e m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 2 ≤ e) (hm1 : 1 ≤ m)
    (hme : m ≤ e - 4) (χ : DirichletCharacter ℂ (p^e)) (hχ : χ.IsPrimitive)
    (htop : χ ((((1 + p ^ (e - 1) : ℕ)) : ZMod (p ^ e))) ≠ 1)
    {a b c d : ℕ} (hac : (a : ZMod p) = (c : ZMod p)) (hbd : (b : ZMod p) = (d : ZMod p))
    {h1 h0 : ℤ} (hh1 : (p:ℤ)^m * h1 = dif1 a b c d)
    (hh0 : (p:ℤ)^m * h0 = dif0 a b c d) (hhne : ¬ ((p:ℤ) ∣ h1 ∧ (p:ℤ) ∣ h0)) :
    ‖∑ x : ZMod (p^e), csm p e χ a b c d x‖ ≤ 2 * (p:ℝ)^(((e + m + 1 : ℕ) : ℝ)/2) := by
  have hcritall : ∀ r : ZMod p, (r + (a : ZMod p))⁻¹ + (r + (b : ZMod p))⁻¹
      - (r + (c : ZMod p))⁻¹ - (r + (d : ZMod p))⁻¹ = 0 := by
    intro r; rw [← hac, ← hbd]; ring
  have hcc' : (∑ x : ZMod (p^e), csm p e χ a b c d x)
      = (p : ℂ) * ∑ r : ZMod p,
          (if (r + (a : ZMod p))⁻¹ + (r + (b : ZMod p))⁻¹ - (r + (c : ZMod p))⁻¹
                - (r + (d : ZMod p))⁻¹ = 0
           then ∑ z : ZMod (p^(e-2)), csm p e χ a b c d ((((r.val : ℕ)) : ZMod (p^e))
                  + (((p:ℕ)) : ZMod (p^e)) * (((z.val : ℕ)) : ZMod (p^e)))
           else 0) := by
    simp only [csm]
    rw [Commons.NumberTheory.DirichletCharacter.charCorrelation_criticalClasses p e hp2 he χ hχ a b c d]
  have hcc2 : (∑ x : ZMod (p^e), csm p e χ a b c d x)
      = (p : ℂ) * ∑ r : ZMod p, ∑ i ∈ Finset.range (p^(e-2)), csm p e χ a b c d (pt p e r i) := by
    rw [hcc']
    congr 1
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [if_pos (hcritall r)]
    exact inner_sum_reindex he χ r
  have hT : ∀ r : ZMod p,
      ‖∑ i ∈ Finset.range (p^(e-2)), csm p e χ a b c d (pt p e r i)‖
        ≤ if (p:ℤ) ∣ (Wpoly h1 h0 c d).eval (r.val : ℤ)
            then (p:ℝ)^(((e+m-1:ℕ):ℝ)/2) else 0 := by
    intro r
    by_cases hbad : (p:ℤ) ∣ (Gpoly c d).eval (r.val : ℤ)
    · have hz : (∑ i ∈ Finset.range (p^(e-2)), csm p e χ a b c d (pt p e r i)) = 0 := by
        refine Finset.sum_eq_zero (fun i _ => ?_)
        simp only [csm]
        exact bad_term_zero χ (by omega) r i hbad
      rw [hz, norm_zero]
      split_ifs <;> positivity
    · by_cases hcrit : (p:ℤ) ∣ (Wpoly h1 h0 c d).eval (r.val : ℤ)
      · obtain ⟨γ, hγ⟩ := hcrit
        have hge : (∑ i ∈ Finset.range (p^(e-2)), csm p e χ a b c d (pt p e r i))
            = ∑ i ∈ Finset.range (p^(e-2)),
                χ ((1 + (p : ZMod (p^e))^m
                      * (((Hpoly h1 h0).eval (r.val : ℤ) : ℤ) : ZMod (p^e))
                      * ((((Gpoly c d).eval (r.val : ℤ) : ℤ) : ZMod (p^e)))⁻¹)
                  + (p : ZMod (p^e))^(m+2)
                    * (((N2poly γ ((Hpoly h1 h0).eval (r.val : ℤ)) ((Gpoly c d).coeff 2)).eval (i : ℤ) : ℤ)
                        : ZMod (p^e))
                    * ((((G2poly c d (r.val : ℤ) p).eval (i : ℤ) : ℤ) : ZMod (p^e)))⁻¹) := by
          simp only [csm]
          exact good_sum_crit he hh1 hh0 χ r hbad hγ
        rw [hge, if_pos ⟨γ, hγ⟩]
        exact crit_inner_bound hp2 he hm1 hme χ htop hhne r hbad γ hγ
      · have hge : (∑ i ∈ Finset.range (p^(e-2)), csm p e χ a b c d (pt p e r i))
            = ∑ i ∈ Finset.range (p^(e-2)),
                χ ((1 + (p : ZMod (p^e))^m
                      * (((Hpoly h1 h0).eval (r.val : ℤ) : ℤ) : ZMod (p^e))
                      * ((((Gpoly c d).eval (r.val : ℤ) : ℤ) : ZMod (p^e)))⁻¹)
                  + (p : ZMod (p^e))^(m+1)
                    * (((N2poly ((Wpoly h1 h0 c d).eval (r.val : ℤ)) ((Hpoly h1 h0).eval (r.val : ℤ))
                          ((p:ℤ) * ((Gpoly c d).coeff 2))).eval (i : ℤ) : ℤ) : ZMod (p^e))
                    * ((((G2poly c d (r.val : ℤ) p).eval (i : ℤ) : ℤ) : ZMod (p^e)))⁻¹) := by
          simp only [csm]
          exact good_sum_noncrit he hh1 hh0 χ r hbad
        rw [hge, noncrit_inner_zero hp2 he hm1 hme χ htop r hbad hcrit, norm_zero, if_neg hcrit]
  have hsum : ‖∑ r : ZMod p, ∑ i ∈ Finset.range (p^(e-2)), csm p e χ a b c d (pt p e r i)‖
      ≤ 2 * (p:ℝ)^(((e+m-1:ℕ):ℝ)/2) := by
    refine (norm_sum_le _ _).trans ?_
    set Crit := (Finset.univ.filter (fun r : ZMod p => (p:ℤ) ∣ (Wpoly h1 h0 c d).eval (r.val : ℤ)))
      with hCritdef
    calc ∑ r : ZMod p, ‖∑ i ∈ Finset.range (p^(e-2)), csm p e χ a b c d (pt p e r i)‖
        ≤ ∑ r : ZMod p, (if (p:ℤ) ∣ (Wpoly h1 h0 c d).eval (r.val : ℤ)
            then (p:ℝ)^(((e+m-1:ℕ):ℝ)/2) else 0) := Finset.sum_le_sum (fun r _ => hT r)
      _ = ∑ r ∈ Crit, (p:ℝ)^(((e+m-1:ℕ):ℝ)/2) := by
          rw [Finset.sum_filter]
      _ = (Crit.card : ℝ) * (p:ℝ)^(((e+m-1:ℕ):ℝ)/2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (p:ℝ)^(((e+m-1:ℕ):ℝ)/2) := by
          have h2 := crit_card_le_two (c := c) (d := d) hp2 hhne
          have hc : (Crit.card : ℝ) ≤ 2 := by
            rw [hCritdef]; exact_mod_cast h2
          have hpos : (0:ℝ) ≤ (p:ℝ)^(((e+m-1:ℕ):ℝ)/2) :=
            Real.rpow_nonneg (Nat.cast_nonneg _) _
          nlinarith
  rw [hcc2, norm_mul, Complex.norm_natCast]
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq ?_
  rw [show ((e+m+1:ℕ):ℝ)/2 = ((e+m-1:ℕ):ℝ)/2 + 1 by
    have h1 : e + m + 1 = (e + m - 1) + 2 := by omega
    rw [h1]; push_cast; ring]
  have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [Real.rpow_add hppos, Real.rpow_one]
  ring

end CaseC
namespace CaseC

lemma exp_ineq_small (q : ℝ) (hq : 2 ≤ q) (e : ℕ) (he : e ≤ 4) :
    q ^ e ≤ 8 * q ^ ((e:ℝ)/2) * q ^ ((min e 2 : ℕ) : ℝ) := by
  have hq1 : (1:ℝ) ≤ q := by linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hsplit : q ^ ((e:ℝ)) = q ^ ((e:ℝ)/2) * q ^ ((e:ℝ)/2) := by
    rw [← Real.rpow_add hq0]; ring_nf
  rw [← Real.rpow_natCast, hsplit]
  have he4' : (e:ℝ) ≤ 4 := by exact_mod_cast he
  have h1 : q ^ ((e:ℝ)/2) ≤ q ^ ((min e 2 : ℕ) : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le hq1 ?_
    rw [Nat.cast_min]
    refine le_min ?_ ?_
    · linarith
    · push_cast; linarith
  have h2 : (0:ℝ) ≤ q ^ ((e:ℝ)/2) := Real.rpow_nonneg (by linarith) _
  calc q ^ ((e:ℝ)/2) * q ^ ((e:ℝ)/2)
      ≤ q ^ ((e:ℝ)/2) * q ^ ((min e 2 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h1 h2
    _ ≤ 8 * q ^ ((e:ℝ)/2) * q ^ ((min e 2 : ℕ) : ℝ) := by nlinarith

lemma exp_ineq_main (q : ℝ) (hq : 2 ≤ q) (e m : ℕ) (h5 : 5 ≤ e) (hm1 : 1 ≤ m) (hme : m ≤ e - 4) :
    2 * q ^ (((e + m + 1 : ℕ) : ℝ)/2) ≤ 8 * q ^ ((e:ℝ)/2) * q ^ ((min e (2*m) : ℕ) : ℝ) := by
  have hq1 : (1:ℝ) ≤ q := by linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hexp : (((e + m + 1 : ℕ)) : ℝ)/2 = (e:ℝ)/2 + (((m+1:ℕ)) : ℝ)/2 := by push_cast; ring
  rw [hexp, Real.rpow_add hq0]
  have hle : ((((m+1:ℕ)) : ℝ)/2) ≤ ((min e (2*m) : ℕ) : ℝ) := by
    rw [Nat.cast_min]
    refine le_min ?_ ?_
    · have h3 : ((m+1:ℕ):ℝ) ≤ 2*(e:ℝ) := by
        have : m + 1 ≤ 2*e := by omega
        exact_mod_cast this
      linarith
    · have h3 : ((m+1:ℕ):ℝ) ≤ ((2*m:ℕ):ℝ) := by
        have : m + 1 ≤ 2*m := by omega
        exact_mod_cast this
      linarith
  have hA : q ^ ((((m+1:ℕ)) : ℝ)/2) ≤ q ^ ((min e (2*m) : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq1 hle
  have h2 : (0:ℝ) ≤ q ^ ((e:ℝ)/2) * q ^ ((min e (2*m) : ℕ) : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  calc 2 * (q ^ ((e:ℝ)/2) * q ^ ((((m+1:ℕ)) : ℝ)/2))
      ≤ 2 * (q ^ ((e:ℝ)/2) * q ^ ((min e (2*m) : ℕ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg (by linarith) _)
    _ ≤ 8 * q ^ ((e:ℝ)/2) * q ^ ((min e (2*m) : ℕ) : ℝ) := by nlinarith

lemma exp_ineq_triv (q : ℝ) (hq : 2 ≤ q) (e m : ℕ) (h5 : 5 ≤ e) (hm1 : 1 ≤ m) (hme : e - 3 ≤ m) :
    q ^ e ≤ 8 * q ^ ((e:ℝ)/2) * q ^ ((min e (2*m) : ℕ) : ℝ) := by
  have hq1 : (1:ℝ) ≤ q := by linarith
  have hq0 : (0:ℝ) < q := by linarith
  have h5' : (5:ℝ) ≤ (e:ℝ) := by exact_mod_cast h5
  have hsplit : q ^ ((e:ℝ)) = q ^ ((e:ℝ)/2) * q ^ ((e:ℝ)/2) := by
    rw [← Real.rpow_add hq0]; ring_nf
  rw [← Real.rpow_natCast, hsplit]
  have key : (e:ℝ)/2 ≤ ((min e (2*m) : ℕ) : ℝ) := by
    rw [Nat.cast_min]
    rcases le_total ((2*m:ℕ):ℝ) ((e:ℕ):ℝ) with h | h
    · rw [min_eq_right h]
      have h2 : 2*(e:ℝ) - 6 ≤ ((2*m:ℕ):ℝ) := by
        have h3 : 2 * (e - 3) ≤ 2 * m := by omega
        have h4 : ((2 * (e - 3) : ℕ) : ℝ) ≤ ((2*m:ℕ):ℝ) := by exact_mod_cast h3
        have h5'' : ((2 * (e - 3) : ℕ) : ℝ) = 2*(e:ℝ) - 6 := by
          rw [Nat.cast_mul, Nat.cast_sub (by omega : 3 ≤ e)]
          push_cast; ring
        linarith [h4, h5''.le, h5''.ge]
      linarith
    · rw [min_eq_left h]
      have he : ((e:ℕ):ℝ)/2 ≤ ((e:ℕ):ℝ) := by
        have := Nat.cast_nonneg (α := ℝ) e; linarith
      linarith
  have hA : q ^ ((e:ℝ)/2) ≤ q ^ ((min e (2*m) : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq1 key
  have h2 : (0:ℝ) ≤ q ^ ((e:ℝ)/2) * q ^ ((min e (2*m) : ℕ) : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  calc q ^ ((e:ℝ)/2) * q ^ ((e:ℝ)/2)
      ≤ q ^ ((e:ℝ)/2) * q ^ ((min e (2*m) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg (by linarith) _)
    _ ≤ 8 * q ^ ((e:ℝ)/2) * q ^ ((min e (2*m) : ℕ) : ℝ) := by nlinarith

end CaseC

/-- **The degenerate ("case C") prime-power correlation bound, with the full `gcd` factor.**

Let `p` be an odd prime, `e ≥ 1`, `χ` primitive modulo `p ^ e`, and suppose `a ≡ c` and
`b ≡ d` modulo `p` (so the two quadratic products agree mod `p` and no square-root
cancellation occurs).  Then the correlation is bounded by the target bound with the full
`gcd (p^e) Δ` factor, `Δ = ∏_{i<j} (v_i - v_j)`, `(v) = (a,b,c,d)`.

(When `p ∣ a - c` and `p ∣ b - d`, automatically `p^2 ∣ Δ`, which is what makes this
degenerate case consistent with the square-root-cancellation regime.) -/
theorem charCorrelation_caseC_gcd (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1) (a b c d : ℕ)
    (hac : (a : ZMod p) = (c : ZMod p)) (hbd : (b : ZMod p) = (d : ZMod p)) :
    ‖∑ x : ZMod (p^e), χ ((x + a) * (x + b)) * (starRingEnd ℂ) (χ ((x + c) * (x + d)))‖
      ≤ 8 * (p : ℝ) ^ ((e : ℝ) / 2) *
        ((Nat.gcd (p ^ e)
          ((((a : ℤ) - (b : ℤ)) * ((a : ℤ) - (c : ℤ)) * ((a : ℤ) - (d : ℤ))
            * ((b : ℤ) - (c : ℤ)) * ((b : ℤ) - (d : ℤ)) * ((c : ℤ) - (d : ℤ))).natAbs)) : ℝ) := by
  classical
  haveI : NeZero (p^e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  set Del : ℤ := ((a:ℤ) - (b:ℤ)) * ((a:ℤ) - (c:ℤ)) * ((a:ℤ) - (d:ℤ))
      * ((b:ℤ) - (c:ℤ)) * ((b:ℤ) - (d:ℤ)) * ((c:ℤ) - (d:ℤ)) with hDeldef
  set Dg : ℕ := Nat.gcd (p^e) Del.natAbs with hDgdef
  change ‖∑ x : ZMod (p^e), CaseC.csm p e χ a b c d x‖
      ≤ 8 * (p:ℝ)^((e:ℝ)/2) * ((Dg : ℕ) : ℝ)
  have hpos : 0 < Dg := by
    rw [hDgdef]; exact Nat.gcd_pos_of_pos_left _ (pow_pos (Fact.out : p.Prime).pos e)
  have htriv : ‖∑ x : ZMod (p^e), CaseC.csm p e χ a b c d x‖ ≤ (p:ℝ)^e := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ x : ZMod (p^e), ‖CaseC.csm p e χ a b c d x‖ ≤ 1 := by
      intro x
      simp only [CaseC.csm]
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_one₀ (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
        (DirichletCharacter.norm_le_one χ _)
    calc ∑ x : ZMod (p^e), ‖CaseC.csm p e χ a b c d x‖
        ≤ ∑ x : ZMod (p^e), (1:ℝ) := Finset.sum_le_sum (fun x _ => h1 x)
      _ = (Fintype.card (ZMod (p^e)) : ℝ) := by simp
      _ = (p:ℝ)^e := by rw [ZMod.card]; push_cast; ring
  have hDel2 : (p:ℤ)^2 ∣ Del := by
    have hacd : (p:ℤ) ∣ ((a:ℤ) - (c:ℤ)) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (by push_cast; rw [hac]; ring)
    have hbdd : (p:ℤ) ∣ ((b:ℤ) - (d:ℤ)) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (by push_cast; rw [hbd]; ring)
    have h2 : (p:ℤ)^2 ∣ ((a:ℤ) - (c:ℤ)) * ((b:ℤ) - (d:ℤ)) := by
      rw [pow_two]; exact mul_dvd_mul hacd hbdd
    refine h2.trans ⟨((a:ℤ) - (b:ℤ)) * ((a:ℤ) - (d:ℤ)) * ((b:ℤ) - (c:ℤ)) * ((c:ℤ) - (d:ℤ)), ?_⟩
    rw [hDeldef]; ring
  have hgp : p^(min e 2) ∣ Dg := by
    rw [hDgdef]
    refine Nat.dvd_gcd (pow_dvd_pow p (min_le_left e 2)) ?_
    exact (pow_dvd_pow p (min_le_right e 2)).trans (CaseC.int_pow_dvd_natAbs (m := 2) hDel2)
  have hDgmin : (p:ℝ)^((min e 2 : ℕ) : ℝ) ≤ (Dg:ℝ) := by
    have hle : p^(min e 2) ≤ Dg := Nat.le_of_dvd hpos hgp
    exact_mod_cast hle
  by_cases he4 : e ≤ 4
  · refine htriv.trans ?_
    have hq : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).two_le
    calc (p:ℝ)^e ≤ 8 * (p:ℝ)^((e:ℝ)/2) * (p:ℝ)^((min e 2 : ℕ) : ℝ) :=
          CaseC.exp_ineq_small _ hq e he4
      _ ≤ 8 * (p:ℝ)^((e:ℝ)/2) * (Dg:ℝ) := by
          have hqpos : (0:ℝ) ≤ 8 * (p:ℝ)^((e:ℝ)/2) := by positivity
          exact mul_le_mul_of_nonneg_left hDgmin hqpos
  · have he2 : 2 ≤ e := by omega
    have htop : χ ((((1 + p ^ (e - 1) : ℕ)) : ZMod (p ^ e))) ≠ 1 :=
      isPrimitive_top_ne_one p e hp2 he2 χ hχ
    obtain ⟨m, hme_le, hmd1, hmd0, hmmaxle, hmmax⟩ :=
      CaseC.exists_corrM p e (CaseC.dif1 a b c d) (CaseC.dif0 a b c d)
    have hm1 : 1 ≤ m := hmmaxle 1 (by omega)
      (by simpa [CaseC.dif1] using CaseC.p_dvd_dif1 hac hbd)
      (by simpa [CaseC.dif0] using CaseC.p_dvd_dif0 hac hbd)
    have hDg : (p:ℝ)^(((min e (2*m) : ℕ)) : ℝ) ≤ (Dg:ℝ) := by
      have h : p ^ min e (2*m) ∣ Dg := by
        rw [hDgdef, hDeldef]
        exact p_pow_min_dvd_gcd_discriminant (Fact.out : p.Prime) (m := m) (a := a) (b := b)
          (c := c) (d := d) hmd1 hmd0
      have hle : p ^ min e (2*m) ≤ Dg := Nat.le_of_dvd hpos h
      calc (p:ℝ)^(((min e (2*m) : ℕ)) : ℝ) = ((p ^ min e (2*m) : ℕ) : ℝ) := by
            rw [Real.rpow_natCast]; push_cast; ring
        _ ≤ (Dg : ℝ) := by exact_mod_cast hle
    by_cases hmain : m ≤ e - 4
    · obtain ⟨h1', hh1'⟩ := hmd1
      obtain ⟨h0', hh0'⟩ := hmd0
      have hh1'' : (p:ℤ)^m * h1' = CaseC.dif1 a b c d := hh1'.symm
      have hh0'' : (p:ℤ)^m * h0' = CaseC.dif0 a b c d := hh0'.symm
      have hhne : ¬ ((p:ℤ) ∣ h1' ∧ (p:ℤ) ∣ h0') := by
        rcases hmmax with hm | hm
        · exfalso; omega
        · intro hc
          refine hm ⟨?_, ?_⟩
          · rw [pow_succ, ← hh1'']; exact mul_dvd_mul_left _ hc.1
          · rw [pow_succ, ← hh0'']; exact mul_dvd_mul_left _ hc.2
      have hb := CaseC.correlation_bound_of_m hp2 he2 hm1 hmain χ hχ htop hac hbd hh1'' hh0'' hhne
      refine hb.trans ?_
      have hq : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).two_le
      refine (CaseC.exp_ineq_main _ hq e m (by omega) hm1 hmain).trans ?_
      have hqpos : (0:ℝ) ≤ 8 * (p:ℝ)^((e:ℝ)/2) := by positivity
      exact mul_le_mul_of_nonneg_left hDg hqpos
    · refine htriv.trans ?_
      have hq : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).two_le
      have hme' : e - 3 ≤ m := by omega
      calc (p:ℝ)^e ≤ 8 * (p:ℝ)^((e:ℝ)/2) * (p:ℝ)^((min e (2*m) : ℕ) : ℝ) :=
            CaseC.exp_ineq_triv _ hq e m (by omega) hm1 hme'
        _ ≤ 8 * (p:ℝ)^((e:ℝ)/2) * (Dg:ℝ) := by
            have hqpos : (0:ℝ) ≤ 8 * (p:ℝ)^((e:ℝ)/2) := by positivity
            exact mul_le_mul_of_nonneg_left hDg hqpos

end Commons.NumberTheory.DirichletCharacter
