import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.irreducible_power_reduction
import Submission.Commons.FieldTheory.Polynomial.not_exists_pow_of_irreducible

namespace Commons.FieldTheory.Kummer

/-- If `2 ≤ d` and `X ^ d - C a` is irreducible over a field `K`, then `a ≠ 0`
(since otherwise `X ^ d = X · X ^ (d-1)` is a factorization into two non-units). -/
lemma ne_zero_of_irreducible_X_pow_sub_C {K : Type*} [Field K] {d : ℕ} {a : K}
    (hd : 2 ≤ d) (hirr : Irreducible (_root_.Polynomial.X ^ d - _root_.Polynomial.C a)) :
    a ≠ 0 := by
  intro ha
  rw [ha, map_zero, sub_zero] at hirr
  have hfac : (_root_.Polynomial.X : Polynomial K) ^ d
      = _root_.Polynomial.X * _root_.Polynomial.X ^ (d - 1) := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hX : ¬ IsUnit (_root_.Polynomial.X : Polynomial K) := _root_.Polynomial.not_isUnit_X
  have hXp : ¬ IsUnit ((_root_.Polynomial.X : Polynomial K) ^ (d - 1)) := by
    intro h
    have h0 := _root_.Polynomial.natDegree_eq_zero_of_isUnit h
    rw [_root_.Polynomial.natDegree_pow, _root_.Polynomial.natDegree_X, mul_one] at h0
    omega
  rcases hirr.isUnit_or_isUnit hfac with h | h
  · exact hX h
  · exact hXp h

/-- Given a primitive `d`-th root of unity with `4 ∣ d`, `-4 * b ^ 4` is a square. -/
lemma exists_sq_neg_four_mul_pow_four {K : Type*} [Field K] {d : ℕ} (hd : 0 < d)
    (hμ : (primitiveRoots d K).Nonempty) (h4 : 4 ∣ d) (b : K) :
    ∃ c : K, c ^ 2 = -4 * b ^ 4 := by
  obtain ⟨ζ, hζmem⟩ := hμ
  have hζ : IsPrimitiveRoot ζ d := (mem_primitiveRoots hd).mp hζmem
  set i : K := ζ ^ (d / 4) with hi_def
  have hi : IsPrimitiveRoot i 4 := hζ.pow hd (Nat.div_mul_cancel h4).symm
  have h2root : IsPrimitiveRoot (i ^ 2) 2 := hi.pow (by norm_num) (by norm_num : 4 = 2 * 2)
  have hi2 : i ^ 2 = -1 := IsPrimitiveRoot.eq_neg_one_of_two_right h2root
  refine ⟨2 * b ^ 2 * i, ?_⟩
  have key : (2 * b ^ 2 * i) ^ 2 = 4 * b ^ 4 * i ^ 2 := by ring
  rw [key, hi2]
  ring

theorem binomial_irreducible_iff_forall_prime {K : Type*} [Field K] {d : ℕ} (hd : 0 < d) (hμ : (primitiveRoots d K).Nonempty) {a : K} :
    Irreducible (Polynomial.X ^ d - Polynomial.C a) ↔ (∀ p : ℕ, p.Prime → p ∣ d → ∀ b : K, b ^ p ≠ a) := by
  constructor
  · intro hirr p hp hpd b hb
    have hd2 : 2 ≤ d := hp.two_le.trans (Nat.le_of_dvd hd hpd)
    have ha : a ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C hd2 hirr
    have h := Commons.FieldTheory.Polynomial.not_exists_pow_of_irreducible hp hpd hd.ne' ha hirr
    exact h ⟨b, hb⟩
  · intro h1
    refine Commons.NumberTheory.DirichletCharacter.capelli_irreducible hd h1 ?_
    intro h4 b hb
    have h2d : 2 ∣ d := dvd_trans (by norm_num : 2 ∣ 4) h4
    obtain ⟨c, hc⟩ := exists_sq_neg_four_mul_pow_four hd hμ h4 b
    exact h1 2 Nat.prime_two h2d c (hc.trans hb)

end Commons.FieldTheory.Kummer
