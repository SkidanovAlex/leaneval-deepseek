import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

namespace Commons.Algebra.MvPolynomial

noncomputable section

open scoped BigOperators

private abbrev P (n : ℕ) := MvPolynomial (Fin n) ℝ

private lemma pderiv_X_pow {n : ℕ} (i j : Fin n) (k : ℕ) :
    MvPolynomial.pderiv i ((MvPolynomial.X j : P n) ^ k)
      = (if i = j then (k : ℝ) else 0) • (MvPolynomial.X j : P n) ^ (k - 1) := by
  by_cases h : i = j
  · subst i
    rw [MvPolynomial.pderiv_pow]
    simp
    rw [Algebra.smul_def]
    simp
  · rw [MvPolynomial.pderiv_pow]
    simp [h]

private lemma pderiv_smul {n : ℕ} (i : Fin n) (c : ℝ) (f : P n) :
    MvPolynomial.pderiv i (c • f) = c • MvPolynomial.pderiv i f := by
  rw [← MvPolynomial.C_mul']
  rw [MvPolynomial.pderiv_C_mul]
  rw [MvPolynomial.C_mul']

private lemma pderiv_two_X_pow {n : ℕ} (i j : Fin n) (k : ℕ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv i ((MvPolynomial.X j : P n) ^ k))
      = (if i = j then (((k * (k - 1)) : ℕ) : ℝ) else 0) • (MvPolynomial.X j : P n) ^ (k - 2) := by
  by_cases h : i = j
  · subst j
    rw [pderiv_X_pow i i k]
    simp only [↓reduceIte]
    rw [pderiv_smul]
    rw [pderiv_X_pow i i (k - 1)]
    simp only [↓reduceIte]
    rw [smul_smul]
    have hsub : (k - 1) - 1 = k - 2 := by omega
    rw [hsub]
    congr 1
    rw [← Nat.cast_mul]
  · rw [pderiv_X_pow i j k]
    simp only [h, ↓reduceIte]
    simp

private lemma pderiv_pderiv_mul {n : ℕ} (i : Fin n) (f g : P n) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv i (f * g)) =
      (MvPolynomial.pderiv i (MvPolynomial.pderiv i f)) * g
        + (2 : ℝ) • ((MvPolynomial.pderiv i f) * (MvPolynomial.pderiv i g))
        + f * MvPolynomial.pderiv i (MvPolynomial.pderiv i g) := by
  rw [MvPolynomial.pderiv_mul]
  rw [map_add]
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul]
  rw [two_smul ℝ ((MvPolynomial.pderiv i f) * (MvPolynomial.pderiv i g))]
  ring

private lemma sum_if_smul {n : ℕ} (e : Fin n) (c : ℝ) (p : P n) :
    (∑ i : Fin n, (if i = e then c else 0) • p) = c • p := by
  classical
  rw [Finset.sum_eq_single e]
  · simp
  · intro i hi hie
    simp [hie]
  · intro h
    exact False.elim (h (Finset.mem_univ e))

private lemma cross_zero {n : ℕ} (a b : ℕ) (e0 e1 : Fin n) (hne : e0 ≠ e1) :
    (∑ i : Fin n, MvPolynomial.pderiv i ((MvPolynomial.X e0 : P n) ^ a)
        * MvPolynomial.pderiv i ((MvPolynomial.X e1 : P n) ^ b)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  by_cases h0 : i = e0
  · subst i
    rw [pderiv_X_pow e0 e0 a, pderiv_X_pow e0 e1 b]
    simp [hne]
  · by_cases h1 : i = e1
    · subst i
      rw [pderiv_X_pow e1 e0 a, pderiv_X_pow e1 e1 b]
      simp [Ne.symm hne]
    · rw [pderiv_X_pow i e0 a, pderiv_X_pow i e1 b]
      simp [h0, h1]

theorem lap_monomial_two {n : ℕ} (a b : ℕ) (e0 e1 : Fin n) (hne : e0 ≠ e1) :
    (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i
        (((MvPolynomial.X e0 : MvPolynomial (Fin n) ℝ) ^ a) *
          ((MvPolynomial.X e1 : MvPolynomial (Fin n) ℝ) ^ b)))) =
      (((a * (a - 1)) : ℕ) : ℝ) •
        (((MvPolynomial.X e0 : MvPolynomial (Fin n) ℝ) ^ (a - 2)) *
          ((MvPolynomial.X e1 : MvPolynomial (Fin n) ℝ) ^ b))
        + (((b * (b - 1)) : ℕ) : ℝ) •
        (((MvPolynomial.X e0 : MvPolynomial (Fin n) ℝ) ^ a) *
          ((MvPolynomial.X e1 : MvPolynomial (Fin n) ℝ) ^ (b - 2))) := by
  classical
  let x0 : P n := MvPolynomial.X e0
  let x1 : P n := MvPolynomial.X e1
  let cA : ℝ := ((a * (a - 1)) : ℕ)
  let cB : ℝ := ((b * (b - 1)) : ℕ)
  have hF : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (x0 ^ a * x1 ^ b))) =
        (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (x0 ^ a))) * (x1 ^ b)
        + (2 : ℝ) • (∑ i : Fin n, MvPolynomial.pderiv i (x0 ^ a) * MvPolynomial.pderiv i (x1 ^ b))
        + (x0 ^ a) * (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (x1 ^ b))) := by
    trans (∑ i : Fin n, ((MvPolynomial.pderiv i (MvPolynomial.pderiv i (x0 ^ a))) * (x1 ^ b)
        + (2 : ℝ) • (MvPolynomial.pderiv i (x0 ^ a) * MvPolynomial.pderiv i (x1 ^ b))
        + (x0 ^ a) * (MvPolynomial.pderiv i (MvPolynomial.pderiv i (x1 ^ b)))))
    · apply Finset.sum_congr rfl
      intro i hi
      exact pderiv_pderiv_mul i (x0 ^ a) (x1 ^ b)
    · rw [Finset.sum_add_distrib]
      rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul]
      rw [← Finset.smul_sum]
      rw [← Finset.mul_sum]
  have hA : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (x0 ^ a)))
        = cA • (x0 ^ (a - 2)) := by
    trans (∑ i : Fin n, (if i = e0 then cA else 0) • (x0 ^ (a - 2)))
    · apply Finset.sum_congr rfl
      intro i hi
      rw [pderiv_two_X_pow i e0 a]
    · exact sum_if_smul e0 cA (x0 ^ (a - 2))
  have hB : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (x1 ^ b)))
        = cB • (x1 ^ (b - 2)) := by
    trans (∑ i : Fin n, (if i = e1 then cB else 0) • (x1 ^ (b - 2)))
    · apply Finset.sum_congr rfl
      intro i hi
      rw [pderiv_two_X_pow i e1 b]
    · exact sum_if_smul e1 cB (x1 ^ (b - 2))
  have hCross : (∑ i : Fin n, MvPolynomial.pderiv i (x0 ^ a) * MvPolynomial.pderiv i (x1 ^ b)) = 0 := by
    simpa [x0, x1] using cross_zero a b e0 e1 hne
  calc
    (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i
        (((MvPolynomial.X e0 : MvPolynomial (Fin n) ℝ) ^ a) * ((MvPolynomial.X e1 : MvPolynomial (Fin n) ℝ) ^ b))))
      = (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (x0 ^ a * x1 ^ b))) := by
          simp [x0, x1]
    _ = (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (x0 ^ a))) * (x1 ^ b)
          + (2 : ℝ) • (∑ i : Fin n, MvPolynomial.pderiv i (x0 ^ a) * MvPolynomial.pderiv i (x1 ^ b))
          + (x0 ^ a) * (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (x1 ^ b))) := hF
    _ = (cA • x0 ^ (a - 2)) * x1 ^ b + (2 : ℝ) • 0 + x0 ^ a * (cB • x1 ^ (b - 2)) := by
          rw [hA, hB, hCross]
    _ = cA • (x0 ^ (a - 2) * x1 ^ b) + cB • (x0 ^ a * x1 ^ (b - 2)) := by
          simp
    _ = (((a * (a - 1)) : ℕ) : ℝ) •
          (((MvPolynomial.X e0 : MvPolynomial (Fin n) ℝ) ^ (a - 2)) * ((MvPolynomial.X e1 : MvPolynomial (Fin n) ℝ) ^ b))
          + (((b * (b - 1)) : ℕ) : ℝ) •
          (((MvPolynomial.X e0 : MvPolynomial (Fin n) ℝ) ^ a) * ((MvPolynomial.X e1 : MvPolynomial (Fin n) ℝ) ^ (b - 2))) := by
          simp [x0, x1, cA, cB]

end

end Commons.Algebra.MvPolynomial