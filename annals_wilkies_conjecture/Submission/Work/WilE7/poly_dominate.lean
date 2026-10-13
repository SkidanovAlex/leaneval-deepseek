import Mathlib
import Submission.Work.WilE7.poly_bound
import Submission.Work.WilE7.poly_le_pow
import Submission.Work.WilE7.poly_embed

namespace Work.WilE7

/-- A univariate polynomial with coefficients in `ℕ` is bounded by `C * (1+D)^N`. -/
theorem poly_eval_le (q : Polynomial ℕ) :
    ∃ (C N : ℕ), ∀ D : ℕ, q.eval D ≤ C * (1 + D) ^ N := by
  refine ⟨∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i, q.natDegree, fun D => ?_⟩
  rw [Polynomial.eval_eq_sum_range]
  calc ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * D ^ i
      ≤ ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (1 + D) ^ q.natDegree := by
        refine Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
        have hi' : i ≤ q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact (Nat.pow_le_pow_left (by omega : D ≤ 1 + D) i).trans
          (Nat.pow_le_pow_right (by omega : 0 < 1 + D) hi')
    _ = (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i) * (1 + D) ^ q.natDegree :=
        (Finset.sum_mul _ _ _).symm

/-- Substituting a polynomial `q.eval D` for the first variable and a quantity `K D k` bounded
by `M (1+D)^N (1+k)^N` for the second variable keeps a bivariate polynomial with coefficients
in `ℕ` inside the same class. -/
theorem poly_dominate (b : MvPolynomial (Fin 2) ℕ) (q : Polynomial ℕ) (K : ℕ → ℕ → ℕ)
    (hK : ∃ M N : ℕ, ∀ D k : ℕ, K D k ≤ M * (1 + D) ^ N * (1 + k) ^ N) :
    ∃ b' : MvPolynomial (Fin 2) ℕ, ∀ D k : ℕ, b.eval ![q.eval D, K D k] ≤ b'.eval ![D, k] := by
  obtain ⟨M, N, hM⟩ := hK
  obtain ⟨Cq, Nq, hq⟩ := poly_eval_le q
  obtain ⟨Mb, Nb, hb⟩ := poly_le_pow b
  refine ⟨MvPolynomial.C (Mb * (Cq + 1) ^ Nb * (M + 1) ^ Nb) *
      (MvPolynomial.X (0 : Fin 2) + 1) ^ (Nq * Nb + N * Nb) *
      (MvPolynomial.X (1 : Fin 2) + 1) ^ (N * Nb), fun D k => ?_⟩
  have hb'eval : (MvPolynomial.C (Mb * (Cq + 1) ^ Nb * (M + 1) ^ Nb) *
      (MvPolynomial.X (0 : Fin 2) + 1) ^ (Nq * Nb + N * Nb) *
      (MvPolynomial.X (1 : Fin 2) + 1) ^ (N * Nb)).eval ![D, k]
      = Mb * (Cq + 1) ^ Nb * (M + 1) ^ Nb * (D + 1) ^ (Nq * Nb + N * Nb)
        * (k + 1) ^ (N * Nb) := by
    simp [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_X]
  rw [hb'eval]
  have hqD : 1 + q.eval D ≤ (Cq + 1) * (1 + D) ^ Nq := by
    have h1 : 1 ≤ (1 + D) ^ Nq := Nat.one_le_pow Nq (1 + D) (by omega)
    calc 1 + q.eval D ≤ 1 + Cq * (1 + D) ^ Nq := Nat.add_le_add_left (hq D) 1
      _ ≤ (1 + D) ^ Nq + Cq * (1 + D) ^ Nq := Nat.add_le_add_right h1 _
      _ = (Cq + 1) * (1 + D) ^ Nq := by ring
  have hKD : 1 + K D k ≤ (M + 1) * ((1 + D) ^ N * (1 + k) ^ N) := by
    have h1 : 1 ≤ (1 + D) ^ N * (1 + k) ^ N := by
      rw [← mul_pow]
      exact Nat.one_le_pow N ((1 + D) * (1 + k)) (by positivity)
    have hK' : K D k ≤ M * ((1 + D) ^ N * (1 + k) ^ N) := by
      simpa only [Nat.mul_assoc] using hM D k
    calc 1 + K D k ≤ 1 + M * ((1 + D) ^ N * (1 + k) ^ N) := Nat.add_le_add_left hK' 1
      _ ≤ ((1 + D) ^ N * (1 + k) ^ N) + M * ((1 + D) ^ N * (1 + k) ^ N) :=
          Nat.add_le_add_right h1 _
      _ = (M + 1) * ((1 + D) ^ N * (1 + k) ^ N) := by ring
  have hA : ((Cq + 1) * (1 + D) ^ Nq) ^ Nb = (Cq + 1) ^ Nb * (1 + D) ^ (Nq * Nb) := by
    rw [mul_pow, ← pow_mul]
  have hB : ((M + 1) * ((1 + D) ^ N * (1 + k) ^ N)) ^ Nb
      = (M + 1) ^ Nb * (1 + D) ^ (N * Nb) * (1 + k) ^ (N * Nb) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    ring
  calc b.eval ![q.eval D, K D k]
      ≤ Mb * (1 + q.eval D) ^ Nb * (1 + K D k) ^ Nb := hb (q.eval D) (K D k)
    _ ≤ Mb * ((Cq + 1) * (1 + D) ^ Nq) ^ Nb
          * ((M + 1) * ((1 + D) ^ N * (1 + k) ^ N)) ^ Nb :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqD Nb))
          (Nat.pow_le_pow_left hKD Nb)
    _ = Mb * (Cq + 1) ^ Nb * (M + 1) ^ Nb * (D + 1) ^ (Nq * Nb + N * Nb)
          * (k + 1) ^ (N * Nb) := by
        rw [hA, hB]
        have hflat : Mb * ((Cq + 1) ^ Nb * (1 + D) ^ (Nq * Nb))
            * ((M + 1) ^ Nb * (1 + D) ^ (N * Nb) * (1 + k) ^ (N * Nb))
            = Mb * (Cq + 1) ^ Nb * (M + 1) ^ Nb
              * ((1 + D) ^ (Nq * Nb) * (1 + D) ^ (N * Nb)) * (1 + k) ^ (N * Nb) := by
          ring
        rw [hflat, ← pow_add, Nat.add_comm (1 : ℕ) D, Nat.add_comm (1 : ℕ) k]

end Work.WilE7
