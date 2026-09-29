import Mathlib
import Submission.Work.TMC14Core.AdjBase

/-!
# `Work.TMC14Core.AdjTrace`

For a matrix `B` over `ℂ`, if `trace (B^n * W) = 0` for all `n + 1 < q`, then

  `trace (adjugate (z * 1 - B) * W) = trace (B^(q-1) * W)`.

The mathematical content is the expansion
`adjugate (z * 1 - B) = ∑_{i=0}^{q} (charpoly B).coeff i • geomZ B z i`,
whose `B^(q-1)`-coefficient is `(charpoly B).coeff q = 1`; all lower powers
pair to zero with `W` by the hypothesis.
-/

open Polynomial Matrix Finset
open scoped BigOperators

namespace Work.TMC14Core

theorem AdjTrace (q : ℕ) (B W : Matrix (Fin q) (Fin q) ℂ)
    (h : ∀ n : ℕ, n + 1 < q → ((B ^ n) * W).trace = 0) (z : ℂ) :
    (Matrix.adjugate (z • (1 : Matrix (Fin q) (Fin q) ℂ) - B) * W).trace =
      (B ^ (q - 1) * W).trace := by
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · -- `q = 0`: both sides vanish.
    subst hq0
    simp only [Matrix.adjugate_fin_zero, Matrix.zero_mul, Matrix.trace_zero]
    simp [Matrix.trace, Finset.univ_eq_empty]
  -- The adjugate expansion, pushed through `Polynomial.eval z`.
  have hgen : (B.charmatrix).adjugate
      = ∑ i ∈ Finset.range (q + 1), Polynomial.C (B.charpoly.coeff i) • geom B i :=
    adjugate_charmatrix_eq B
  have hmapadj : (B.charmatrix).adjugate.map (Polynomial.eval z)
      = Matrix.adjugate (z • (1 : Matrix (Fin q) (Fin q) ℂ) - B) := by
    have h1 : (B.charmatrix).adjugate.map (Polynomial.eval z)
        = (B.charmatrix.map (Polynomial.eval z)).adjugate := by
      have := RingHom.map_adjugate (Polynomial.evalRingHom z) B.charmatrix
      simpa [RingHom.mapMatrix_apply] using this
    rw [h1, map_charmatrix]
  have hmap : (B.charmatrix).adjugate.map (Polynomial.eval z)
      = ∑ i ∈ Finset.range (q + 1), (B.charpoly.coeff i) • geomZ B z i := by
    rw [hgen]
    exact map_geomsum B z
  have hadj : Matrix.adjugate (z • (1 : Matrix (Fin q) (Fin q) ℂ) - B)
      = ∑ i ∈ Finset.range (q + 1), (B.charpoly.coeff i) • geomZ B z i := by
    rw [← hmapadj, hmap]
  -- Trace of `geomZ B z i * W`.
  have hinner : ∀ i, (geomZ B z i * W).trace
      = ∑ k ∈ Finset.range i, z ^ (i - 1 - k) * (B ^ k * W).trace := by
    intro i
    rw [geomZ, Matrix.sum_mul, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [hadj, Matrix.sum_mul, Matrix.trace_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hinner]
  -- Now evaluate the collapsed double sum.
  have hcoeff : B.charpoly.coeff q = 1 := by
    have hnd : B.charpoly.natDegree = q := by simpa using Matrix.charpoly_natDegree_eq_dim B
    simpa [hnd] using (Matrix.charpoly_monic B).coeff_natDegree
  have hsum1 : (∑ i ∈ Finset.range (q + 1), B.charpoly.coeff i *
        (∑ k ∈ Finset.range i, z ^ (i - 1 - k) * (B ^ k * W).trace))
      = B.charpoly.coeff q * (∑ k ∈ Finset.range q, z ^ (q - 1 - k) * (B ^ k * W).trace) := by
    refine Finset.sum_eq_single q ?_ ?_
    · intro i hi hiq
      have hi' : i < q := by
        have : i < q + 1 := Finset.mem_range.mp hi
        omega
      have hz : (∑ k ∈ Finset.range i, z ^ (i - 1 - k) * (B ^ k * W).trace) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hk' : k < i := Finset.mem_range.mp hk
        have hkq : k + 1 < q := by omega
        rw [h k hkq, mul_zero]
      rw [hz, mul_zero]
    · intro hc
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self q)) hc
  rw [hsum1, hcoeff, one_mul]
  have hsum2 : (∑ k ∈ Finset.range q, z ^ (q - 1 - k) * (B ^ k * W).trace)
      = z ^ (q - 1 - (q - 1)) * (B ^ (q - 1) * W).trace := by
    refine Finset.sum_eq_single (q - 1) ?_ ?_
    · intro k hk hkq
      have hk' : k < q := Finset.mem_range.mp hk
      have hkq' : k + 1 < q := by omega
      rw [h k hkq', mul_zero]
    · intro hc
      exact absurd (Finset.mem_range.mpr (by omega)) hc
  rw [hsum2, show q - 1 - (q - 1) = 0 by omega, pow_zero, one_mul]

end Work.TMC14Core
