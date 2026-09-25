import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one
import Submission.Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow

open scoped NumberField WithZero

set_option linter.style.haveILetI false
open IsDedekindDomain.HeightOneSpectrum

namespace Commons.NumberTheory.NumberField.Completion

/-- In the value group `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`, the `n`-th power map is injective on
nonzero elements, for `n ≠ 0`. -/
private lemma withZero_pow_inj {a b : WithZero (Multiplicative ℤ)}
    (ha : a ≠ 0) (hb : b ≠ 0) {n : ℕ} (hn : n ≠ 0) (h : a ^ n = b ^ n) : a = b := by
  conv_lhs at h => rw [← WithZero.exp_log ha]
  conv_rhs at h => rw [← WithZero.exp_log hb]
  rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul] at h
  rw [WithZero.exp_inj] at h
  have h2 : (n : ℤ) * WithZero.log a = (n : ℤ) * WithZero.log b := by
    simpa [nsmul_eq_mul] using h
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have hl : WithZero.log a = WithZero.log b := mul_left_cancel₀ hnz h2
  rw [← WithZero.exp_log ha, ← WithZero.exp_log hb, hl]

theorem exists_norm_uniformizer_mul_unit_adicCompletion {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ u : (Q.adicCompletionIntegers K)ˣ, ∃ x : q.adicCompletion L,
      Algebra.norm (Q.adicCompletion K) x =
        (u : Q.adicCompletion K) *
          ((Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers K)
              (K := K) Q : Q.adicCompletionIntegers K) : Q.adicCompletion K) ^
            (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  -- Abbreviations.
  let ϖL : q.adicCompletionIntegers L :=
    Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers L) (K := L) q
  let ϖK : Q.adicCompletionIntegers K :=
    Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers K) (K := K) Q
  let x : q.adicCompletion L := ϖL
  let e : ℕ := q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)
  let f : ℕ := q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)
  let N : Q.adicCompletion K := Algebra.norm (Q.adicCompletion K) x
  -- The ramification index is nonzero.
  have he : e ≠ 0 := by
    have h := Ideal.ramificationIdx_pos (q := q.asIdeal) (R := NumberField.RingOfIntegers K)
    simp only [e]; omega
  -- Values of the uniformizers.
  have hvx : Valued.v x = WithZero.exp (-1 : ℤ) := by
    simp only [x, ϖL]
    exact Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one (K := L) q
  have hvK : Valued.v (ϖK : Q.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    simp only [ϖK]
    exact Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one (K := K) Q
  -- Value of the norm via the two local identities.
  have hnorm : Valued.v (algebraMap (Q.adicCompletion K) (q.adicCompletion L) N)
      = (Valued.v x) ^ (Module.finrank (Q.adicCompletion K) (q.adicCompletion L)) := by
    simp only [N]
    exact Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow Q q hq x
  have hmap : Valued.v (algebraMap (Q.adicCompletion K) (q.adicCompletion L) N)
      = (Valued.v N) ^ e := by
    change Valued.v ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq) N) = (Valued.v N) ^ e
    rw [Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq N]
  have hpow : (Valued.v N) ^ e = (WithZero.exp (-1 : ℤ)) ^ (e * f) := by
    rw [← hmap, hnorm, hvx]
    congr 1
    simp only [e, f]
    exact (Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      Q q hq).symm
  have hNne : Valued.v N ≠ 0 := by
    intro h0
    have hzero : (Valued.v N) ^ e = 0 := by rw [h0]; exact zero_pow he
    rw [hzero] at hpow
    exact (pow_ne_zero _ (WithZero.exp_ne_zero (a := (-1 : ℤ)))) hpow.symm
  have hpow2 : (Valued.v N) ^ e = ((WithZero.exp (-1 : ℤ)) ^ f) ^ e := by
    rw [hpow, ← pow_mul, Nat.mul_comm]
  have hvN : Valued.v N = (WithZero.exp (-1 : ℤ)) ^ f :=
    withZero_pow_inj hNne (pow_ne_zero _ (WithZero.exp_ne_zero (a := (-1 : ℤ)))) he hpow2
  -- The candidate unit is `N / ϖK ^ f`.
  have hKne : (ϖK : Q.adicCompletion K) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvK
    exact (WithZero.exp_ne_zero (a := (-1 : ℤ))) hvK.symm
  have hb : (ϖK : Q.adicCompletion K) ^ f ≠ 0 := pow_ne_zero _ hKne
  let z : Q.adicCompletion K := N * ((ϖK : Q.adicCompletion K) ^ f)⁻¹
  have hz : Valued.v z = 1 := by
    simp only [z]
    rw [map_mul, map_inv₀, map_pow, hvK, hvN]
    exact mul_inv_cancel₀ (pow_ne_zero _ (WithZero.exp_ne_zero (a := (-1 : ℤ))))
  let a : Q.adicCompletionIntegers K := ⟨z, by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]; exact le_of_eq hz⟩
  have ha : IsUnit a :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mpr
      (by simpa [a] using hz)
  have hzN : z * (ϖK : Q.adicCompletion K) ^ f = N := by
    simp only [z]
    rw [mul_assoc, inv_mul_cancel₀ hb, mul_one]
  refine ⟨ha.unit, x, ?_⟩
  have hunit : ((ha.unit : Q.adicCompletionIntegers K) : Q.adicCompletion K) = z := by
    rw [IsUnit.unit_spec]
  rw [hunit]
  show N = z * (ϖK : Q.adicCompletion K) ^ f
  rw [hzN]

end Commons.NumberTheory.NumberField.Completion
