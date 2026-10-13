/-
  Area E7 / `CoreLT_succ`: the polynomial bookkeeping for the **final cardinality bound**.

  The `(n+1,K+1)` step calls the inner statement `CoreLT n K` at a degree bound `D_in` that is a
  polynomial in the outer `D`, and the inner statement returns a cell bound of the form
  `MvPolynomial.eval ![D_in, k, l] b` — where `l` is the length of the `Y`-family handed to it, and
  `Yl.length ≤ K₀ D k` for a `K₀` bounded by `M (1+D)^N (1+k)^N` (the length bounds produced by
  `yFamily_withCutters`/`fiberCut_len` are of exactly this shape).  The outer conclusion must then be
  a *two*-variable polynomial bound `MvPolynomial.eval ![D,k] b'`, i.e. one must be able to

  * substitute `q.eval D` for the first variable (for `D_in`),
  * substitute a bounded family `K D k` for the third variable (for `l`),

  while keeping the second variable `k` (the number of input sets).  `Work.WilE7.poly_dominate`
  handles the two-variable case; this file supplies the three-variable version, together with the
  three-variable `poly_le_pow`.
-/
import Mathlib
import Submission.Work.WilE7.poly_le_pow
import Submission.Work.WilE7.poly_embed
import Submission.Work.WilE7.poly_dominate

set_option autoImplicit false
noncomputable section
namespace Work.WilE7

/-- A polynomial in three variables with coefficients in `ℕ` is bounded by
`M * (1+e 0)^N * (1+e 1)^N * (1+e 2)^N` (sum of the coefficients and the total degree). -/
theorem poly_le_pow3 (b : MvPolynomial (Fin 3) ℕ) :
    ∃ (M N : ℕ), ∀ e : Fin 3 → ℕ,
      b.eval e ≤ M * (1 + e 0) ^ N * (1 + e 1) ^ N * (1 + e 2) ^ N := by
  refine ⟨∑ d ∈ b.support, b.coeff d, b.totalDegree, fun e => ?_⟩
  have hkey : ∀ d ∈ b.support,
      b.coeff d * (e 0 ^ d 0 * e 1 ^ d 1 * e 2 ^ d 2)
        ≤ b.coeff d * ((1 + e 0) ^ b.totalDegree * (1 + e 1) ^ b.totalDegree
            * (1 + e 2) ^ b.totalDegree) := by
    intro d hd
    have h0 : d 0 ≤ b.totalDegree :=
      (MvPolynomial.le_degreeOf_of_mem_support 0 hd).trans
        (MvPolynomial.degreeOf_le_totalDegree b 0)
    have h1 : d 1 ≤ b.totalDegree :=
      (MvPolynomial.le_degreeOf_of_mem_support 1 hd).trans
        (MvPolynomial.degreeOf_le_totalDegree b 1)
    have h2 : d 2 ≤ b.totalDegree :=
      (MvPolynomial.le_degreeOf_of_mem_support 2 hd).trans
        (MvPolynomial.degreeOf_le_totalDegree b 2)
    have hD0 : e 0 ^ d 0 ≤ (1 + e 0) ^ b.totalDegree :=
      (Nat.pow_le_pow_left (by omega) (d 0)).trans (Nat.pow_le_pow_right (by omega) h0)
    have hD1 : e 1 ^ d 1 ≤ (1 + e 1) ^ b.totalDegree :=
      (Nat.pow_le_pow_left (by omega) (d 1)).trans (Nat.pow_le_pow_right (by omega) h1)
    have hD2 : e 2 ^ d 2 ≤ (1 + e 2) ^ b.totalDegree :=
      (Nat.pow_le_pow_left (by omega) (d 2)).trans (Nat.pow_le_pow_right (by omega) h2)
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul hD0 hD1) hD2)
  calc b.eval e
      = ∑ d ∈ b.support, b.coeff d * (e 0 ^ d 0 * e 1 ^ d 1 * e 2 ^ d 2) := by
        rw [MvPolynomial.eval_eq']
        apply Finset.sum_congr rfl
        intro d _
        congr 1
        simp [Fin.prod_univ_three]
    _ ≤ ∑ d ∈ b.support, b.coeff d * ((1 + e 0) ^ b.totalDegree * (1 + e 1) ^ b.totalDegree
          * (1 + e 2) ^ b.totalDegree) := Finset.sum_le_sum hkey
    _ = (∑ d ∈ b.support, b.coeff d) * (1 + e 0) ^ b.totalDegree * (1 + e 1) ^ b.totalDegree
          * (1 + e 2) ^ b.totalDegree := by
        rw [← Finset.sum_mul]
        ring

/-- **Three-variable domination.**  Substituting `q.eval D` for the first variable, keeping the
second, and substituting a family `K D k ≤ M (1+D)^N (1+k)^N` for the third keeps a three-variable
polynomial with coefficients in `ℕ` inside the two-variable class in `(D, k)`. -/
theorem poly_dominate3 (b : MvPolynomial (Fin 3) ℕ) (q : Polynomial ℕ) (K : ℕ → ℕ → ℕ)
    (hK : ∃ M N : ℕ, ∀ D k : ℕ, K D k ≤ M * (1 + D) ^ N * (1 + k) ^ N) :
    ∃ b' : MvPolynomial (Fin 2) ℕ, ∀ D k : ℕ,
      MvPolynomial.eval ![q.eval D, k, K D k] b ≤ MvPolynomial.eval ![D, k] b' := by
  obtain ⟨M, N, hM⟩ := hK
  obtain ⟨Cq, Nq, hq⟩ := poly_eval_le q
  obtain ⟨Mb, Nb, hb⟩ := poly_le_pow3 b
  refine ⟨MvPolynomial.C (Mb * (Cq + 1) ^ Nb * (M + 1) ^ Nb) *
      (MvPolynomial.X (0 : Fin 2) + 1) ^ (Nq * Nb + N * Nb) *
      (MvPolynomial.X (1 : Fin 2) + 1) ^ (Nb + N * Nb), fun D k => ?_⟩
  have hb'eval : (MvPolynomial.C (Mb * (Cq + 1) ^ Nb * (M + 1) ^ Nb) *
      (MvPolynomial.X (0 : Fin 2) + 1) ^ (Nq * Nb + N * Nb) *
      (MvPolynomial.X (1 : Fin 2) + 1) ^ (Nb + N * Nb)).eval ![D, k]
      = Mb * (Cq + 1) ^ Nb * (M + 1) ^ Nb * (D + 1) ^ (Nq * Nb + N * Nb)
        * (k + 1) ^ (Nb + N * Nb) := by
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
  calc b.eval ![q.eval D, k, K D k]
      ≤ Mb * (1 + q.eval D) ^ Nb * (1 + k) ^ Nb * (1 + K D k) ^ Nb := hb ![q.eval D, k, K D k]
    _ ≤ Mb * ((Cq + 1) * (1 + D) ^ Nq) ^ Nb * (1 + k) ^ Nb
          * ((M + 1) * ((1 + D) ^ N * (1 + k) ^ N)) ^ Nb := by
        refine Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqD Nb))
          (le_refl _)) (Nat.pow_le_pow_left hKD Nb)
    _ = Mb * (Cq + 1) ^ Nb * (M + 1) ^ Nb * (D + 1) ^ (Nq * Nb + N * Nb)
          * (k + 1) ^ (Nb + N * Nb) := by
        rw [hA, hB]
        have hflat : Mb * ((Cq + 1) ^ Nb * (1 + D) ^ (Nq * Nb)) * (1 + k) ^ Nb
            * ((M + 1) ^ Nb * (1 + D) ^ (N * Nb) * (1 + k) ^ (N * Nb))
            = Mb * (Cq + 1) ^ Nb * (M + 1) ^ Nb
              * ((1 + D) ^ (Nq * Nb) * (1 + D) ^ (N * Nb))
              * ((1 + k) ^ Nb * (1 + k) ^ (N * Nb)) := by ring
        rw [hflat, ← pow_add, ← pow_add, Nat.add_comm (1 : ℕ) D, Nat.add_comm (1 : ℕ) k]

end Work.WilE7
