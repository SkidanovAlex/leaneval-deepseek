import Mathlib.NumberTheory.NumberField.House
import Submission.Commons.NumberTheory.Height.NumberField.coeff_minpoly_map_le

namespace Commons.NumberTheory.NumberField

open Polynomial

theorem minpoly_coeff_le_pow_sub {K : Type*} [Field K] [NumberField K]
    (x : NumberField.RingOfIntegers K) (H : ℝ)
    (hH : NumberField.house ((x : NumberField.RingOfIntegers K) : K) ≤ H) (hH1 : 1 ≤ H) (k : ℕ) :
    ‖(((minpoly ℤ x).coeff k : ℤ) : ℝ)‖ ≤
      2 ^ Module.finrank ℚ K * H ^ (Module.finrank ℚ K - k) := by
  set n : ℕ := Module.finrank ℚ K with hn
  set q : ℚ[X] := minpoly ℚ ((x : NumberField.RingOfIntegers K) : K) with hqdef
  have hxint : IsIntegral ℤ x := IsIntegralClosure.isIntegral ℤ K x
  have hmonicq : q.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral _)
  have hmap : (minpoly ℤ x).map (algebraMap ℤ ℚ) = q := by
    rw [hqdef]
    exact (minpoly.isIntegrallyClosed_eq_field_fractions (R := ℤ) (K := ℚ)
      (S := NumberField.RingOfIntegers K) (L := K) hxint).symm
  have hcoeff_rel : ∀ k, ((minpoly ℤ x).coeff k : ℚ) = q.coeff k := by
    intro k
    have h2 := congrArg (fun (p : ℚ[X]) => p.coeff k) hmap
    simpa using h2
  set qc : ℂ[X] := q.map (algebraMap ℚ ℂ) with hqcdef
  have hmonicc : qc.Monic := hmonicq.map _
  have hsplit : qc.Splits := IsAlgClosed.splits _
  have hqc0 : qc ≠ 0 := hmonicc.ne_zero
  have hdqc : qc.natDegree = q.natDegree := by
    rw [hqcdef, Polynomial.natDegree_map]
  have hq_le : q.natDegree ≤ n := by
    rw [hqdef]
    exact minpoly.natDegree_le (A := ℚ) (B := K) (x := ((x : NumberField.RingOfIntegers K) : K))
  have hd_le : qc.natDegree ≤ n := by rw [hdqc]; exact hq_le
  have hB0 : 0 ≤ H := (NumberField.house_nonneg _).trans hH
  have hroots : ∀ r ∈ qc.roots, ‖r‖ ≤ H := by
    intro r hr
    rw [Polynomial.mem_roots hqc0, Polynomial.IsRoot.def] at hr
    have hr1 : Polynomial.aeval r ((minpoly ℚ ((x : NumberField.RingOfIntegers K) : K))) = 0 := by
      rw [← Polynomial.aeval_map_algebraMap (R := ℚ) (A := ℂ) (B := ℂ) r
        (minpoly ℚ ((x : NumberField.RingOfIntegers K) : K))]
      exact hr
    have hr' : r ∈ (minpoly ℚ ((x : NumberField.RingOfIntegers K) : K)).rootSet ℂ := by
      rw [Polynomial.mem_rootSet]
      exact ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral _), hr1⟩
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly (F := ℚ) ℂ
      ((x : NumberField.RingOfIntegers K) : K)] at hr'
    obtain ⟨ψ, rfl⟩ := hr'
    exact (NumberField.norm_embedding_le_house _ ψ.toRingHom).trans hH
  have hrel : ‖(((minpoly ℤ x).coeff k : ℤ) : ℝ)‖ = ‖qc.coeff k‖ := by
    have h1 : qc.coeff k = (((minpoly ℤ x).coeff k : ℤ) : ℂ) := by
      rw [hqcdef, Polynomial.coeff_map, ← hcoeff_rel k]
      simp
    rw [h1, Complex.norm_intCast, Real.norm_eq_abs]
  rw [hrel]
  by_cases hk : k ≤ qc.natDegree
  · have hcoeff := Polynomial.coeff_eq_esymm_roots_of_splits hsplit hk
    rw [hcoeff, hmonicc.leadingCoeff, one_mul, norm_mul]
    have h1 : ‖(-1 : ℂ) ^ (qc.natDegree - k)‖ = 1 := by simp
    rw [h1, one_mul]
    have hesymm := Commons.NumberTheory.Height.NumberField.norm_esymm_le hB0 hroots
      (qc.natDegree - k)
    rw [← hsplit.natDegree_eq_card_roots] at hesymm
    refine hesymm.trans ?_
    have hchoose : ((qc.natDegree.choose (qc.natDegree - k) : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
      have h1 : qc.natDegree.choose (qc.natDegree - k) ≤ 2 ^ qc.natDegree :=
        Nat.choose_le_two_pow _ _
      have h2 : 2 ^ qc.natDegree ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hd_le
      exact_mod_cast le_trans h1 h2
    have hkexp : qc.natDegree - k ≤ n - k := Nat.sub_le_sub_right hd_le k
    have hexp : H ^ (qc.natDegree - k) ≤ H ^ (n - k) := pow_le_pow_right₀ hH1 hkexp
    calc ((qc.natDegree.choose (qc.natDegree - k) : ℕ) : ℝ) * H ^ (qc.natDegree - k)
        ≤ (2 : ℝ) ^ n * H ^ (n - k) :=
          mul_le_mul hchoose hexp (pow_nonneg hB0 _) (pow_nonneg (by norm_num) _)
      _ = 2 ^ n * H ^ (n - k) := rfl
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hk), norm_zero]
    exact mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hB0 _)

end Commons.NumberTheory.NumberField