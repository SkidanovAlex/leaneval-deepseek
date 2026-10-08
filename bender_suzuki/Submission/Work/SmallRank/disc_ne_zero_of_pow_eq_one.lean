import Mathlib
import Submission.Work.SmallRank.GL2Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Matrix

namespace Work.SmallRank

/-- Powers of `1 + n` when `n` is a square-zero element of a ring. -/
lemma one_add_pow_of_sq_eq_zero {R : Type*} [Ring R] (n : R) (hn : n ^ 2 = 0) (k : ℕ) :
    (1 + n) ^ k = 1 + k • n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_succ]
      simp only [add_mul, mul_add, one_mul, mul_one, mul_assoc]
      rw [show n * n = 0 from by rw [← pow_two]; exact hn]
      rw [mul_zero, add_zero]
      abel

/-- `r • (s • x) = (r * s) • x` in an algebra. -/
lemma algebra_smul_smul {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (r s : R) (x : A) : r • (s • x) = (r * s) • x := by
  rw [Algebra.smul_def r, Algebra.smul_def s, Algebra.smul_def (r * s), ← mul_assoc, ← map_mul]

/-- Natural-number smul is scalar multiplication by the cast, in an algebra. -/
lemma nsmul_eq_smul_of_algebra {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (m : ℕ) (x : A) : m • x = (m : R) • x := by
  rw [nsmul_eq_mul, ← map_natCast (algebraMap R A) m, Algebra.algebraMap_eq_smul_one,
    Algebra.smul_mul_assoc, one_mul]

/-- `(r • x) ^ n = r ^ n • x ^ n` in an algebra. -/
lemma algebra_smul_pow {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (r : R) (x : A) (n : ℕ) : (r • x) ^ n = r ^ n • x ^ n := by
  rw [Algebra.smul_def, Commute.mul_pow (Algebra.commutes r x) n, ← map_pow,
    Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul]

/-- A non-scalar matrix `a ∈ M₂(𝔽_p)` with `a ^ m = 1` where `m ≠ 0` in `𝔽_p` is semisimple: its
characteristic polynomial `X² - (tr a) X + det a` has non-vanishing discriminant. -/
theorem disc_ne_zero_of_pow_eq_one {p : ℕ} [Fact p.Prime] {a : M2 p} {m : ℕ}
    (ha : NonScalar a) (hm : (m : ZMod p) ≠ 0) (h : a ^ m = 1) :
    4 * a.det - (Matrix.trace a) ^ 2 ≠ 0 := by
  intro hΔ
  have hp : Nat.Prime p := Fact.out
  rcases hp.eq_two_or_odd with h2 | hodd
  · -- characteristic 2
    subst h2
    have ht2 : (Matrix.trace a) ^ 2 = 0 := by
      have hh := hΔ
      have h4 : (4 : ZMod 2) = 0 :=
        (CharP.cast_eq_zero_iff (ZMod 2) 2 4).mpr (by norm_num)
      rw [h4, zero_mul, zero_sub] at hh
      exact neg_eq_zero.mp hh
    have ht : Matrix.trace a = 0 := sq_eq_zero_iff.mp ht2
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
    have hdet : (a.det) ^ m = 1 := by
      have hh := congrArg Matrix.det h
      rwa [Matrix.det_pow, Matrix.det_one] at hh
    have hd_ne : a.det ≠ 0 := by
      intro hd0
      rw [hd0, zero_pow hm0] at hdet
      exact zero_ne_one hdet
    have ha2 : a ^ 2 = (-(a.det)) • (1 : M2 2) := by
      rw [sq_eq_trace_smul_sub_det_smul a, ht, zero_smul, zero_sub, neg_smul]
    have hodd_m : Odd m := by
      rw [← Nat.not_even_iff_odd, Nat.even_iff]
      intro hmod
      apply hm
      exact (ZMod.natCast_eq_zero_iff m 2).mpr (Nat.dvd_iff_mod_eq_zero.mpr hmod)
    obtain ⟨k, hk⟩ := hodd_m
    have hmain : ((-(a.det)) ^ k) • a = 1 := by
      have hh := h
      rw [hk, pow_succ, pow_mul, ha2, algebra_smul_pow, one_pow] at hh
      rwa [Algebra.smul_mul_assoc, one_mul] at hh
    have he_ne : (-(a.det)) ^ k ≠ 0 := pow_ne_zero k (neg_ne_zero.mpr hd_ne)
    refine ha ⟨((-(a.det)) ^ k)⁻¹, ?_⟩
    have h2 : ((-(a.det)) ^ k)⁻¹ • (((-(a.det)) ^ k) • a) = ((-(a.det)) ^ k)⁻¹ • 1 := by
      simp only [hmain]
    rw [algebra_smul_smul, inv_mul_cancel₀ he_ne, one_smul] at h2
    exact h2
  · -- odd characteristic
    have hp2 : (2 : ZMod p) ≠ 0 := by
      intro hc
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hc
      rw [Nat.dvd_prime (show Nat.Prime 2 from by norm_num)] at hdvd
      rcases hdvd with h1 | h2p
      · exact hp.ne_one h1
      · omega
    let t : ZMod p := Matrix.trace a
    let d : ZMod p := a.det
    have hΔ' : 4 * d - t ^ 2 = 0 := hΔ
    have ht2 : t ^ 2 = 4 * d := by linear_combination -hΔ'
    have hdet : d ^ m = 1 := by
      have hh := congrArg Matrix.det h
      rw [Matrix.det_pow, Matrix.det_one] at hh
      exact hh
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
    have hd_ne : d ≠ 0 := by
      intro hd0
      rw [hd0, zero_pow hm0] at hdet
      exact zero_ne_one hdet
    let b : M2 p := (2 : ZMod p) • a - t • 1
    have hb2 : b ^ 2 = 0 := by
      have key : b ^ 2 = (t ^ 2 - 4 * d) • (1 : M2 p) := by
        dsimp only [b, t, d]
        rw [pow_two]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
            Matrix.one_apply, Matrix.trace_fin_two, Matrix.det_fin_two]
        all_goals ring
      rw [key, show t ^ 2 - 4 * d = 0 from by linear_combination -hΔ', zero_smul]
    let c : ZMod p := (2 : ZMod p)⁻¹ * t
    have hc_sq : c ^ 2 = d := by
      have h4 : ((2 : ZMod p)⁻¹) ^ 2 * 4 = 1 := by
        have hh := inv_mul_cancel₀ hp2
        calc ((2 : ZMod p)⁻¹) ^ 2 * 4
            = ((2 : ZMod p)⁻¹ * 2) * ((2 : ZMod p)⁻¹ * 2) := by ring
          _ = 1 := by rw [hh, mul_one]
      dsimp only [c]
      rw [mul_pow, ht2, ← mul_assoc, h4, one_mul]
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hdz : d = 0 := by
        rw [← hc_sq, hc0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      exact hd_ne hdz
    let N : M2 p := (c⁻¹ * (2 : ZMod p)⁻¹) • b
    have hN2 : N ^ 2 = 0 := by
      dsimp only [N]
      rw [pow_two, smul_mul_smul_comm]
      rw [show b * b = 0 from by rw [← pow_two]; exact hb2, smul_zero]
    have ha_eq : a = c • 1 + (2 : ZMod p)⁻¹ • b := by
      dsimp only [b, c]
      rw [smul_sub, algebra_smul_smul, algebra_smul_smul, inv_mul_cancel₀ hp2, one_smul]
      module
    have hfac : a = c • (1 + N) := by
      rw [ha_eq, smul_add]
      congr 1
      dsimp only [N]
      rw [algebra_smul_smul, ← mul_assoc, mul_inv_cancel₀ hc_ne, one_mul]
    have hpow : a ^ m = c ^ m • 1 + (c ^ m * (m : ZMod p)) • N := by
      rw [hfac, algebra_smul_pow, one_add_pow_of_sq_eq_zero N hN2 m, smul_add]
      congr 1
      rw [nsmul_eq_smul_of_algebra (R := ZMod p) m N, algebra_smul_smul]
    have hsum : c ^ m • 1 + (c ^ m * (m : ZMod p)) • N = 1 := by rw [← hpow, h]
    have hcoef : c ^ m * (m : ZMod p) ≠ 0 := mul_ne_zero (pow_ne_zero m hc_ne) hm
    have hkey : (c ^ m * (m : ZMod p)) • N = (1 - c ^ m) • 1 := by
      calc (c ^ m * (m : ZMod p)) • N
          = c ^ m • 1 + (c ^ m * (m : ZMod p)) • N - c ^ m • 1 := by abel
        _ = 1 - c ^ m • 1 := by rw [hsum]
        _ = (1 - c ^ m) • 1 := by rw [sub_smul, one_smul]
    have hNexpr : N = ((c ^ m * (m : ZMod p))⁻¹ * (1 - c ^ m)) • 1 := by
      have h2 : (c ^ m * (m : ZMod p))⁻¹ • ((c ^ m * (m : ZMod p)) • N)
          = (c ^ m * (m : ZMod p))⁻¹ • ((1 - c ^ m) • 1) := by rw [hkey]
      rw [algebra_smul_smul, inv_mul_cancel₀ hcoef, one_smul, algebra_smul_smul] at h2
      exact h2
    have haS : a = (c * (1 + (c ^ m * (m : ZMod p))⁻¹ * (1 - c ^ m))) • 1 := by
      rw [hfac, hNexpr]
      rw [show (1 : M2 p) + ((c ^ m * (m : ZMod p))⁻¹ * (1 - c ^ m)) • 1
            = (1 + (c ^ m * (m : ZMod p))⁻¹ * (1 - c ^ m)) • 1 from by rw [add_smul, one_smul]]
      rw [algebra_smul_smul]
    exact ha ⟨c * (1 + (c ^ m * (m : ZMod p))⁻¹ * (1 - c ^ m)), haS⟩

end Work.SmallRank
