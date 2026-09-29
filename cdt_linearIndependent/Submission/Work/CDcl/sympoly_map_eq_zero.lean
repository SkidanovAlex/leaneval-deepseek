import Mathlib
import Submission.Work.CDcl.invsum

/-!
# `Work.CDcl.sympoly_map_eq_zero`

The polynomials `symPoly n ∈ ℚ[y]` of `Work.CDcl.invsum` represent `x^n + φ(x)^n`
(`φ(x) = x/(x-1)`) as polynomials in `y = x²/(x-1)`.  They form a "triangular" family with
`natDegree (symPoly n) = n` and non-vanishing top coefficient, hence the symmetrisation map

`P ↦ P.sum (fun j a => Polynomial.C a * symPoly j) = Σ_j (coeff j P) • symPoly j`

is injective: the coefficient of `y^N` (`N = natDegree P`) only receives contributions from the
indices `j ≥ N`, and since `j ∈ P.support` forces `j ≤ N`, precisely the top term `symPoly N`
contributes, with coefficient `coeff N P * 1 ≠ 0`.

This is the lemma `Work.CDcl.sympoly_map_eq_zero`.
-/

noncomputable section

namespace Work.CDcl

open Polynomial

/-- `symPoly n` has degree exactly `n` (it is monic of degree `n` for `n ≥ 1`, and
`symPoly 0 = 2`). -/
private theorem symPoly_natDegree (n : ℕ) : (symPoly n).natDegree = n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [symPoly, Polynomial.natDegree_ofNat]
  | one => simp [symPoly]
  | more n ih1 ih2 =>
      rw [symPoly_succ_succ]
      have hlt : (symPoly n).natDegree < (symPoly (n + 1)).natDegree := by
        rw [ih1, ih2]; omega
      have hdeg : (symPoly (n + 1) - symPoly n).natDegree = n + 1 := by
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, ih2]
      have hd : symPoly (n + 1) - symPoly n ≠ 0 := by
        intro h
        rw [h] at hdeg
        simp at hdeg
      rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hd, Polynomial.natDegree_X, hdeg]
      omega

/-- The top coefficient of `symPoly n` (the coefficient of `y^n`) does not vanish. -/
private theorem symPoly_coeff_self (n : ℕ) : (symPoly n).coeff n ≠ 0 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [symPoly]
  | one => simp [symPoly]
  | more n _ih1 ih2 =>
      rw [symPoly_succ_succ, Polynomial.coeff_X_mul, Polynomial.coeff_sub]
      have hzero : (symPoly n).coeff (n + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [symPoly_natDegree n]; omega)
      rw [hzero, sub_zero]
      exact ih2

/-- The `N`-th coefficient of the symmetrisation `Σ_j (coeff j P) • symPoly j`. -/
private lemma sum_C_symPoly_coeff (P : Polynomial ℚ) (N : ℕ) :
    (P.sum (fun j a => Polynomial.C a * symPoly j)).coeff N
      = ∑ j ∈ P.support, P.coeff j * (symPoly j).coeff N := by
  rw [Polynomial.coeff_sum, Polynomial.sum_def]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp

/-- Only the index `j = natDegree P` contributes to the coefficient of `y ^ natDegree P`
of the symmetrisation of `P`. -/
private lemma sum_C_symPoly_coeff_natDegree (P : Polynomial ℚ) :
    (P.sum (fun j a => Polynomial.C a * symPoly j)).coeff P.natDegree
      = P.coeff P.natDegree * (symPoly P.natDegree).coeff P.natDegree := by
  rw [sum_C_symPoly_coeff]
  refine Finset.sum_eq_single P.natDegree ?_ ?_
  · intro b hb hbne
    have hbN : b < P.natDegree :=
      lt_of_le_of_ne (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hb)) hbne
    have hdeg : (symPoly b).natDegree < P.natDegree := by
      rw [symPoly_natDegree]; exact hbN
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]
  · intro hnot
    rw [Polynomial.notMem_support_iff.mp hnot, zero_mul]

/-- **`Work.CDcl.sympoly_map_eq_zero`**: the map `P ↦ Σ_j (coeff j P) • symPoly j` (which sends
`P` to the polynomial `p` with `p(y) = P(x) + P(φ(x))`) is injective. -/
theorem sympoly_map_eq_zero {P : Polynomial ℚ} :
    P.sum (fun j a => Polynomial.C a * Work.CDcl.symPoly j) = 0 ↔ P = 0 := by
  constructor
  · intro h
    by_contra hP
    have hc := sum_C_symPoly_coeff_natDegree P
    rw [h, Polynomial.coeff_zero] at hc
    have h1 : P.coeff P.natDegree ≠ 0 :=
      Polynomial.mem_support_iff.mp (Polynomial.natDegree_mem_support_of_nonzero hP)
    exact (mul_ne_zero h1 (symPoly_coeff_self P.natDegree)) hc.symm
  · intro h
    rw [h]
    exact Polynomial.sum_zero_index _

end Work.CDcl
