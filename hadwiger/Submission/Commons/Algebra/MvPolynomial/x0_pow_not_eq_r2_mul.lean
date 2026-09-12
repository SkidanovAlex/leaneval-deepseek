import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open scoped BigOperators
open Complex

namespace Commons.Algebra.MvPolynomial

noncomputable section

/-- evaluation point in `ℂ`: `X 0 ↦ 1`, `X 1 ↦ I`, all other variables ↦ 0 -/
private def g {n : ℕ} [NeZero n] (_hn2 : 2 ≤ n) : Fin n → ℂ :=
  fun j => if j = (0 : Fin n) then (1 : ℂ) else if j = (1 : Fin n) then Complex.I else 0

private lemma one_ne_zero_fin {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) :
    (1 : Fin n) ≠ (0 : Fin n) := by
  intro h
  have _ := hn2
  have hv := congrArg Fin.val h
  norm_num at hv
  omega

private lemma g_zero {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) :
    (g hn2 (0 : Fin n)) = 1 := by
  simp [g]

private lemma g_one {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) :
    (g hn2 (1 : Fin n)) = Complex.I := by
  simp [g, one_ne_zero_fin hn2]

private lemma g_other {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) {j : Fin n}
    (hj0 : j ≠ (0 : Fin n)) (hj1 : j ≠ (1 : Fin n)) : g hn2 j = 0 := by
  simp [g, hj0, hj1]

private lemma sum_g_sq {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) :
    (∑ j : Fin n, (g hn2 j)^2) = 0 := by
  classical
  have hmain : (∑ j : Fin n, (g hn2 j)^2)
      = (g hn2 (0 : Fin n))^2 + (g hn2 (1 : Fin n))^2 := by
    let s : Finset (Fin n) := (Finset.univ.erase (1 : Fin n))
    calc
      (∑ j : Fin n, (g hn2 j)^2)
          = (∑ j ∈ s, (g hn2 j)^2) + (g hn2 (1 : Fin n))^2 := by
              dsimp [s]
              rw [Finset.sum_erase_add (Finset.univ : Finset (Fin n))
                (fun j => (g hn2 j)^2) (by simp)]
      _ = (g hn2 (0 : Fin n))^2 + (g hn2 (1 : Fin n))^2 := by
              congr 1
              refine Finset.sum_eq_single (0 : Fin n) ?h0 ?h1
              · intro b hb hb0
                have hb1 : b ≠ (1 : Fin n) := (Finset.mem_erase.mp hb).1
                simp [g_other hn2 hb0 hb1]
              · intro h0not
                exact False.elim (h0not (by
                  rw [Finset.mem_erase]
                  exact ⟨(one_ne_zero_fin hn2).symm, by simp⟩))
  calc
    (∑ j : Fin n, (g hn2 j)^2) = (g hn2 (0 : Fin n))^2 + (g hn2 (1 : Fin n))^2 := hmain
    _ = 1 + Complex.I^2 := by rw [g_zero, g_one]; norm_num
    _ = 0 := by rw [pow_two, Complex.I_mul_I]; norm_num

theorem x0_pow_not_eq_r2_mul {n : ℕ} {k : ℕ} [NeZero n] (hn2 : 2 ≤ n) (hk : 1 ≤ k)
    (R : MvPolynomial (Fin n) ℝ)
    (hR : R ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2)) :
    (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ k ≠
      (∑ j : Fin n, (MvPolynomial.X j)^2) * R := by
  have _ := hk
  have _ := hR
  intro h
  let e : MvPolynomial (Fin n) ℝ →ₐ[ℝ] ℂ := MvPolynomial.aeval (g hn2)
  have hh := congrArg (fun p : MvPolynomial (Fin n) ℝ => e p) h
  have hL : e ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ)^k) = 1 := by
    dsimp [e]
    rw [map_pow]
    rw [MvPolynomial.aeval_X]
    rw [g_zero hn2]
    simp
  have hsum' : e (∑ j : Fin n, (MvPolynomial.X j)^2) = 0 := by
    calc
      e (∑ j : Fin n, (MvPolynomial.X j)^2)
          = ∑ j : Fin n, (g hn2 j)^2 := by
              dsimp [e]
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [map_pow, MvPolynomial.aeval_X]
      _ = 0 := sum_g_sq hn2
  have hR2 : e ((∑ j : Fin n, (MvPolynomial.X j)^2) * R) = 0 := by
    rw [map_mul, hsum']
    ring
  have h01 : (1 : ℂ) = 0 := by
    calc
      (1 : ℂ) = e ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ)^k) := hL.symm
      _ = e (((∑ j : Fin n, (MvPolynomial.X j)^2)) * R) := hh
      _ = 0 := hR2
  norm_num at h01

end

end Commons.Algebra.MvPolynomial