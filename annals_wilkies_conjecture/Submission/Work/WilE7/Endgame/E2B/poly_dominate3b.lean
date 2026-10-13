import Mathlib
import Submission.Work.WilE7.poly_dominate3

set_option autoImplicit false
noncomputable section

namespace Work.WilE7.Endgame.E2B

/-- **Two-bounded-function three-variable domination.**  Substituting `q.eval D` for the first
variable and two families `K1 D k`, `K2 D k` (each bounded by `M (1+D)^N (1+k)^N`) for the second
and third variables keeps a three-variable polynomial with coefficients in `ℕ` inside the
two-variable class in `(D, k)`. -/
theorem poly_dominate3b (b : MvPolynomial (Fin 3) ℕ) (q : Polynomial ℕ) (K1 K2 : ℕ → ℕ → ℕ)
    (hK1 : ∃ M N : ℕ, ∀ D k : ℕ, K1 D k ≤ M * (1 + D) ^ N * (1 + k) ^ N)
    (hK2 : ∃ M N : ℕ, ∀ D k : ℕ, K2 D k ≤ M * (1 + D) ^ N * (1 + k) ^ N) :
    ∃ b' : MvPolynomial (Fin 2) ℕ, ∀ D k : ℕ,
      MvPolynomial.eval ![q.eval D, K1 D k, K2 D k] b ≤ MvPolynomial.eval ![D, k] b' := by
  obtain ⟨M1, N1, hM1⟩ := hK1
  obtain ⟨M2, N2, hM2⟩ := hK2
  obtain ⟨Cq, Nq, hq⟩ := Work.WilE7.poly_eval_le q
  obtain ⟨Mb, Nb, hb⟩ := Work.WilE7.poly_le_pow3 b
  refine ⟨MvPolynomial.C (Mb * (Cq + 1) ^ Nb * (M1 + 1) ^ Nb * (M2 + 1) ^ Nb) *
      (MvPolynomial.X (0 : Fin 2) + 1) ^ (Nq * Nb + N1 * Nb + N2 * Nb) *
      (MvPolynomial.X (1 : Fin 2) + 1) ^ (N1 * Nb + N2 * Nb), fun D k => ?_⟩
  have hb'eval : (MvPolynomial.C (Mb * (Cq + 1) ^ Nb * (M1 + 1) ^ Nb * (M2 + 1) ^ Nb) *
      (MvPolynomial.X (0 : Fin 2) + 1) ^ (Nq * Nb + N1 * Nb + N2 * Nb) *
      (MvPolynomial.X (1 : Fin 2) + 1) ^ (N1 * Nb + N2 * Nb)).eval ![D, k]
      = Mb * (Cq + 1) ^ Nb * (M1 + 1) ^ Nb * (M2 + 1) ^ Nb
        * (D + 1) ^ (Nq * Nb + N1 * Nb + N2 * Nb)
        * (k + 1) ^ (N1 * Nb + N2 * Nb) := by
    simp [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_X]
  rw [hb'eval]
  have hqD : 1 + q.eval D ≤ (Cq + 1) * (1 + D) ^ Nq := by
    have h1 : 1 ≤ (1 + D) ^ Nq := Nat.one_le_pow Nq (1 + D) (by omega)
    calc 1 + q.eval D ≤ 1 + Cq * (1 + D) ^ Nq := Nat.add_le_add_left (hq D) 1
      _ ≤ (1 + D) ^ Nq + Cq * (1 + D) ^ Nq := Nat.add_le_add_right h1 _
      _ = (Cq + 1) * (1 + D) ^ Nq := by ring
  have hK1D : 1 + K1 D k ≤ (M1 + 1) * ((1 + D) ^ N1 * (1 + k) ^ N1) := by
    have h1 : 1 ≤ (1 + D) ^ N1 * (1 + k) ^ N1 := by
      rw [← mul_pow]
      exact Nat.one_le_pow N1 ((1 + D) * (1 + k)) (by positivity)
    have hK' : K1 D k ≤ M1 * ((1 + D) ^ N1 * (1 + k) ^ N1) := by
      simpa only [Nat.mul_assoc] using hM1 D k
    calc 1 + K1 D k ≤ 1 + M1 * ((1 + D) ^ N1 * (1 + k) ^ N1) := Nat.add_le_add_left hK' 1
      _ ≤ ((1 + D) ^ N1 * (1 + k) ^ N1) + M1 * ((1 + D) ^ N1 * (1 + k) ^ N1) :=
          Nat.add_le_add_right h1 _
      _ = (M1 + 1) * ((1 + D) ^ N1 * (1 + k) ^ N1) := by ring
  have hK2D : 1 + K2 D k ≤ (M2 + 1) * ((1 + D) ^ N2 * (1 + k) ^ N2) := by
    have h1 : 1 ≤ (1 + D) ^ N2 * (1 + k) ^ N2 := by
      rw [← mul_pow]
      exact Nat.one_le_pow N2 ((1 + D) * (1 + k)) (by positivity)
    have hK' : K2 D k ≤ M2 * ((1 + D) ^ N2 * (1 + k) ^ N2) := by
      simpa only [Nat.mul_assoc] using hM2 D k
    calc 1 + K2 D k ≤ 1 + M2 * ((1 + D) ^ N2 * (1 + k) ^ N2) := Nat.add_le_add_left hK' 1
      _ ≤ ((1 + D) ^ N2 * (1 + k) ^ N2) + M2 * ((1 + D) ^ N2 * (1 + k) ^ N2) :=
          Nat.add_le_add_right h1 _
      _ = (M2 + 1) * ((1 + D) ^ N2 * (1 + k) ^ N2) := by ring
  have hA : ((Cq + 1) * (1 + D) ^ Nq) ^ Nb = (Cq + 1) ^ Nb * (1 + D) ^ (Nq * Nb) := by
    rw [mul_pow, ← pow_mul]
  have hB1 : ((M1 + 1) * ((1 + D) ^ N1 * (1 + k) ^ N1)) ^ Nb
      = (M1 + 1) ^ Nb * (1 + D) ^ (N1 * Nb) * (1 + k) ^ (N1 * Nb) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    ring
  have hB2 : ((M2 + 1) * ((1 + D) ^ N2 * (1 + k) ^ N2)) ^ Nb
      = (M2 + 1) ^ Nb * (1 + D) ^ (N2 * Nb) * (1 + k) ^ (N2 * Nb) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    ring
  calc MvPolynomial.eval ![q.eval D, K1 D k, K2 D k] b
      ≤ Mb * (1 + q.eval D) ^ Nb * (1 + K1 D k) ^ Nb * (1 + K2 D k) ^ Nb :=
        hb ![q.eval D, K1 D k, K2 D k]
    _ ≤ Mb * ((Cq + 1) * (1 + D) ^ Nq) ^ Nb
          * ((M1 + 1) * ((1 + D) ^ N1 * (1 + k) ^ N1)) ^ Nb
          * ((M2 + 1) * ((1 + D) ^ N2 * (1 + k) ^ N2)) ^ Nb := by
        refine Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqD Nb))
          (Nat.pow_le_pow_left hK1D Nb)) (Nat.pow_le_pow_left hK2D Nb)
    _ = Mb * (Cq + 1) ^ Nb * (M1 + 1) ^ Nb * (M2 + 1) ^ Nb
          * (D + 1) ^ (Nq * Nb + N1 * Nb + N2 * Nb)
          * (k + 1) ^ (N1 * Nb + N2 * Nb) := by
        rw [hA, hB1, hB2]
        have hflat : Mb * ((Cq + 1) ^ Nb * (1 + D) ^ (Nq * Nb))
              * ((M1 + 1) ^ Nb * (1 + D) ^ (N1 * Nb) * (1 + k) ^ (N1 * Nb))
              * ((M2 + 1) ^ Nb * (1 + D) ^ (N2 * Nb) * (1 + k) ^ (N2 * Nb))
            = Mb * (Cq + 1) ^ Nb * (M1 + 1) ^ Nb * (M2 + 1) ^ Nb
              * ((1 + D) ^ (Nq * Nb) * (1 + D) ^ (N1 * Nb) * (1 + D) ^ (N2 * Nb))
              * ((1 + k) ^ (N1 * Nb) * (1 + k) ^ (N2 * Nb)) := by ring
        rw [hflat, ← pow_add, ← pow_add, ← pow_add,
          Nat.add_comm (1 : ℕ) D, Nat.add_comm (1 : ℕ) k]

end Work.WilE7.Endgame.E2B
