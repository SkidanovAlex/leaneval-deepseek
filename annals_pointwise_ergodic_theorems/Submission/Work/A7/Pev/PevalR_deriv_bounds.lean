import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

/-!
# Growth bounds for `PevalR P` and its first two derivatives

`PevalR P : ℝ → ℝ` is the real evaluation of the integer polynomial `P`, `PevalR P x =
(P.map (Int.castRingHom ℝ)).eval x` (`Work.KMTAreas.A7.PevalR`).  This file proves the crude
polynomial-growth bound needed by the model-operator estimates of §6--§8:

there is `C > 0` such that for every `N ≥ 1` and every `t ∈ [0,N]`,

* `|PevalR P t| ≤ C N ^ P.natDegree`,
* `|deriv (PevalR P) t| ≤ C N ^ P.natDegree / N`,
* `|iteratedDeriv 2 (PevalR P) t| ≤ C N ^ P.natDegree / N ^ 2`.

The three statements are the same coefficient-sum estimate applied to `P`, `P'`, `P''`: for any
real polynomial `Q`, `|Q.eval x| ≤ (∑ᵢ |Q.coeff i|) (max 1 |x|)^{Q.natDegree}`; the degree drops
by one under differentiation (`Polynomial.natDegree_derivative_le`) and the differentiation of
`PevalR` is the evaluation of the derivative polynomial
(`Polynomial.deriv`, `Polynomial.derivative_map`).
-/

namespace Work.A7.Pev

open Polynomial

/-- Coefficient-sum bound for the value of a real polynomial: the value at `x` is dominated by
the `ℓ¹`-norm of the coefficient vector times `(max 1 |x|) ^ natDegree`. -/
lemma abs_eval_le_coeff_sum_mul_max (Q : Polynomial ℝ) (x : ℝ) :
    |Q.eval x| ≤
      (∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i|) * (max 1 |x|) ^ Q.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  have hM : (1 : ℝ) ≤ max 1 |x| := le_max_left _ _
  calc
    |∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * x ^ i|
        ≤ ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i * x ^ i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i| * |x| ^ i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [abs_mul, abs_pow]
    _ ≤ ∑ i ∈ Finset.range (Q.natDegree + 1),
          |Q.coeff i| * (max 1 |x|) ^ Q.natDegree := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi_le : i ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          exact mul_le_mul_of_nonneg_left
            ((pow_le_pow_left₀ (abs_nonneg x) (le_max_right 1 |x|) i).trans
              (pow_le_pow_right₀ hM hi_le)) (abs_nonneg _)
    _ = (∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i|) * (max 1 |x|) ^ Q.natDegree :=
          (Finset.sum_mul _ _ _).symm

/-- The derivative of `PevalR P` is the evaluation of the derivative polynomial. -/
lemma deriv_PevalR (P : Polynomial ℤ) (t : ℝ) :
    deriv (Work.KMTAreas.A7.PevalR P) t
      = (P.derivative.map (Int.castRingHom ℝ)).eval t := by
  unfold Work.KMTAreas.A7.PevalR
  simp [Polynomial.derivative_map]

/-- The second derivative of `PevalR P` is the evaluation of the second derivative polynomial. -/
lemma iteratedDeriv_two_PevalR (P : Polynomial ℤ) (t : ℝ) :
    iteratedDeriv 2 (Work.KMTAreas.A7.PevalR P) t
      = (P.derivative.derivative.map (Int.castRingHom ℝ)).eval t := by
  have hfun : deriv (Work.KMTAreas.A7.PevalR P)
      = fun x => (P.derivative.map (Int.castRingHom ℝ)).eval x := by
    funext x; exact deriv_PevalR P x
  rw [show iteratedDeriv 2 (Work.KMTAreas.A7.PevalR P)
        = deriv (deriv (Work.KMTAreas.A7.PevalR P)) by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one],
      hfun]
  simp [Polynomial.derivative_map]

theorem PevalR_deriv_bounds (P : Polynomial ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |Work.KMTAreas.A7.PevalR P t| ≤ C * (N : ℝ) ^ P.natDegree ∧
      |deriv (Work.KMTAreas.A7.PevalR P) t| ≤ C * (N : ℝ) ^ P.natDegree / (N : ℝ) ∧
      |iteratedDeriv 2 (Work.KMTAreas.A7.PevalR P) t|
        ≤ C * (N : ℝ) ^ P.natDegree / (N : ℝ) ^ 2 := by
  classical
  -- the three real polynomials attached to `P`
  set Q : Polynomial ℝ := P.map (Int.castRingHom ℝ) with hQ
  set Q1 : Polynomial ℝ := P.derivative.map (Int.castRingHom ℝ) with hQ1
  set Q2 : Polynomial ℝ := P.derivative.derivative.map (Int.castRingHom ℝ) with hQ2
  -- the `ℓ¹`-norms of their coefficient vectors
  set A0 : ℝ := ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i| with hA0
  set A1 : ℝ := ∑ i ∈ Finset.range (Q1.natDegree + 1), |Q1.coeff i| with hA1
  set A2 : ℝ := ∑ i ∈ Finset.range (Q2.natDegree + 1), |Q2.coeff i| with hA2
  have hA0nn : 0 ≤ A0 := by rw [hA0]; exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hA1nn : 0 ≤ A1 := by rw [hA1]; exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hA2nn : 0 ≤ A2 := by rw [hA2]; exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hCpos : 0 < A0 + A1 + A2 + 1 := by linarith
  have hA0C : A0 ≤ A0 + A1 + A2 + 1 := by linarith
  have hA1C : A1 ≤ A0 + A1 + A2 + 1 := by linarith
  have hA2C : A2 ≤ A0 + A1 + A2 + 1 := by linarith
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  have hQd : Q.natDegree = P.natDegree := by
    rw [hQ]; exact Polynomial.natDegree_map_eq_of_injective hinj P
  refine ⟨A0 + A1 + A2 + 1, hCpos, ?_⟩
  intro N hN t ht
  obtain ⟨ht0, htN⟩ := ht
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := le_trans zero_le_one hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have ht_abs : |t| ≤ (N : ℝ) := by rw [abs_of_nonneg ht0]; exact htN
  have hMN : max 1 |t| ≤ (N : ℝ) := max_le hN1 ht_abs
  have hpowM : ∀ k : ℕ, (max 1 |t|) ^ k ≤ (N : ℝ) ^ k := fun k =>
    pow_le_pow_left₀ (le_trans zero_le_one (le_max_left 1 |t|)) hMN k
  -- the identification of `PevalR P` and of its first two derivatives
  have hP1 : Work.KMTAreas.A7.PevalR P t = Q.eval t := by
    simp only [Work.KMTAreas.A7.PevalR, ← hQ]
  have hP2 : deriv (Work.KMTAreas.A7.PevalR P) t = Q1.eval t := by
    rw [deriv_PevalR P t, ← hQ1]
  have hP3 : iteratedDeriv 2 (Work.KMTAreas.A7.PevalR P) t = Q2.eval t := by
    rw [iteratedDeriv_two_PevalR P t, ← hQ2]
  -- the degrees of the derivative polynomials
  have he1 : Q1.natDegree ≤ P.natDegree - 1 := by
    rw [hQ1]
    exact (Polynomial.natDegree_map_le (p := P.derivative) (f := Int.castRingHom ℝ)).trans
      (Polynomial.natDegree_derivative_le P)
  have he2 : Q2.natDegree ≤ P.natDegree - 2 := by
    rw [hQ2]
    have h1 : (P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree
        ≤ (P.derivative.derivative).natDegree := Polynomial.natDegree_map_le
    have h2 : (P.derivative.derivative).natDegree ≤ P.derivative.natDegree - 1 :=
      Polynomial.natDegree_derivative_le P.derivative
    have h3 : P.derivative.natDegree ≤ P.natDegree - 1 := Polynomial.natDegree_derivative_le P
    calc (P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree
        ≤ (P.derivative.derivative).natDegree := h1
      _ ≤ P.derivative.natDegree - 1 := h2
      _ ≤ (P.natDegree - 1) - 1 := Nat.sub_le_sub_right h3 1
      _ = P.natDegree - 2 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hP1]
    calc |Q.eval t| ≤ A0 * (max 1 |t|) ^ Q.natDegree := by
          rw [hA0]; exact abs_eval_le_coeff_sum_mul_max Q t
      _ ≤ A0 * (N : ℝ) ^ Q.natDegree := mul_le_mul_of_nonneg_left (hpowM _) hA0nn
      _ = A0 * (N : ℝ) ^ P.natDegree := by rw [hQd]
      _ ≤ (A0 + A1 + A2 + 1) * (N : ℝ) ^ P.natDegree :=
          mul_le_mul_of_nonneg_right hA0C (pow_nonneg hNnn _)
  · rw [hP2]
    calc |Q1.eval t| ≤ A1 * (max 1 |t|) ^ Q1.natDegree := by
          rw [hA1]; exact abs_eval_le_coeff_sum_mul_max Q1 t
      _ ≤ A1 * (N : ℝ) ^ Q1.natDegree := mul_le_mul_of_nonneg_left (hpowM _) hA1nn
      _ ≤ (A0 + A1 + A2 + 1) * (N : ℝ) ^ P.natDegree / (N : ℝ) := by
          by_cases hd0 : P.natDegree = 0
          · -- `P` is constant, so `P' = 0`
            have hder : P.derivative = 0 := Polynomial.derivative_of_natDegree_zero hd0
            have hQ1z : Q1 = 0 := by rw [hQ1, hder]; simp
            have hA1z : A1 = 0 := by rw [hA1, hQ1z]; simp
            have hzero : A1 * (N : ℝ) ^ Q1.natDegree = 0 := by rw [hA1z, zero_mul]
            rw [hzero]
            exact div_nonneg (mul_nonneg (le_of_lt hCpos) (pow_nonneg hNnn _)) hNnn
          · have hd1 : 1 ≤ P.natDegree := Nat.one_le_iff_ne_zero.mpr hd0
            have he1' : Q1.natDegree + 1 ≤ P.natDegree := by omega
            have hpowle : (N : ℝ) ^ (Q1.natDegree + 1) ≤ (N : ℝ) ^ P.natDegree :=
              pow_le_pow_right₀ hN1 he1'
            rw [le_div_iff₀ hNpos]
            calc A1 * (N : ℝ) ^ Q1.natDegree * (N : ℝ)
                = A1 * (N : ℝ) ^ (Q1.natDegree + 1) := by rw [pow_succ]; ring
              _ ≤ (A0 + A1 + A2 + 1) * (N : ℝ) ^ P.natDegree :=
                  mul_le_mul hA1C hpowle (pow_nonneg hNnn _) (le_of_lt hCpos)
  · rw [hP3]
    calc |Q2.eval t| ≤ A2 * (max 1 |t|) ^ Q2.natDegree := by
          rw [hA2]; exact abs_eval_le_coeff_sum_mul_max Q2 t
      _ ≤ A2 * (N : ℝ) ^ Q2.natDegree := mul_le_mul_of_nonneg_left (hpowM _) hA2nn
      _ ≤ (A0 + A1 + A2 + 1) * (N : ℝ) ^ P.natDegree / (N : ℝ) ^ 2 := by
          by_cases hd2 : P.natDegree < 2
          · -- `P` has degree ≤ 1, so `P'' = 0`
            have hder1 : P.derivative.natDegree = 0 := by
              have := Polynomial.natDegree_derivative_le P
              omega
            have hder2 : P.derivative.derivative = 0 :=
              Polynomial.derivative_of_natDegree_zero hder1
            have hQ2z : Q2 = 0 := by rw [hQ2, hder2]; simp
            have hA2z : A2 = 0 := by rw [hA2, hQ2z]; simp
            have hzero : A2 * (N : ℝ) ^ Q2.natDegree = 0 := by rw [hA2z, zero_mul]
            rw [hzero]
            exact div_nonneg (mul_nonneg (le_of_lt hCpos) (pow_nonneg hNnn _))
              (pow_nonneg hNnn 2)
          · have hd2' : 2 ≤ P.natDegree := not_lt.mp hd2
            have he2' : Q2.natDegree + 2 ≤ P.natDegree := by omega
            have hpowle : (N : ℝ) ^ (Q2.natDegree + 2) ≤ (N : ℝ) ^ P.natDegree :=
              pow_le_pow_right₀ hN1 he2'
            rw [le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ 2)]
            calc A2 * (N : ℝ) ^ Q2.natDegree * (N : ℝ) ^ 2
                = A2 * (N : ℝ) ^ (Q2.natDegree + 2) := by rw [pow_add]; ring
              _ ≤ (A0 + A1 + A2 + 1) * (N : ℝ) ^ P.natDegree :=
                  mul_le_mul hA2C hpowle (pow_nonneg hNnn _) (le_of_lt hCpos)

end Work.A7.Pev
