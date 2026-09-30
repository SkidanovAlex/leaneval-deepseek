import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.phi_prod_zpow_exp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Linearity of `lamP` in the coefficient matrix: replacing `L` by a `ℤ`-combination `Q` of
its rows multiplies the linear form by the corresponding coefficients. -/
theorem lamP_sum {K : Type*} [Field K] {n r ρ : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (v : ℕ) (L : Fin r → Fin n → ℤ) (A : Fin ρ → Fin r → ℤ) (Q : Fin ρ → Fin n → ℤ)
    (hQ : ∀ j i, Q j i = ∑ a, A j a * L a i) (j : Fin ρ) :
    lamP φ α v Q j = ∑ a, (A j a : ℂ) * lamP φ α v L a := by
  have hQc : ∀ i, (Q j i : ℂ) = ∑ a, (A j a : ℂ) * (L a i : ℂ) := by
    intro i
    rw [hQ j i, Int.cast_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    push_cast
    ring
  have h1 : ∑ i, (Q j i : ℂ) * Complex.log (φ (α i)) =
      ∑ a, (A j a : ℂ) * ∑ i, (L a i : ℂ) * Complex.log (φ (α i)) := by
    calc ∑ i, (Q j i : ℂ) * Complex.log (φ (α i))
        = ∑ i, (∑ a, (A j a : ℂ) * (L a i : ℂ)) * Complex.log (φ (α i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hQc i]
      _ = ∑ i, ∑ a, (A j a : ℂ) * (L a i : ℂ) * Complex.log (φ (α i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ a, ∑ i, (A j a : ℂ) * (L a i : ℂ) * Complex.log (φ (α i)) := by
          rw [Finset.sum_comm]
      _ = ∑ a, (A j a : ℂ) * ∑ i, (L a i : ℂ) * Complex.log (φ (α i)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
  simp only [lamP]
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => by ring

/-- If `exp (lamP φ α v L a) = φ (α' a)` for all `a` and `Q_j i = ∑_a A_ja L_a i`, then
`exp (lamP φ α v Q j) = φ (∏_a (α'_a)^{A_ja})` and that product is nonzero.

*Proof:* `lamP φ α v Q j = ∑_a (A_ja : ℂ) * lamP φ α v L a` (linearity in the matrix, via
`Finset.sum_comm` and `Int.cast_sum`/`Int.cast_mul`), then `Complex.exp_sum`,
`Complex.exp_int_mul`, `map_prod`, `map_zpow₀` (as in
`Submission.Work.BW.phi_prod_zpow_exp`), and `Finset.prod_ne_zero_iff`/`zpow_ne_zero`. -/
theorem exp_lamP_prod {K : Type*} [Field K] {n r ρ : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (v : ℕ) (L : Fin r → Fin n → ℤ) (A : Fin ρ → Fin r → ℤ) (Q : Fin ρ → Fin n → ℤ)
    (α' : Fin r → K) (hQ : ∀ j i, Q j i = ∑ a, A j a * L a i)
    (hα' : ∀ a, α' a ≠ 0) (h : ∀ a, Complex.exp (lamP φ α v L a) = φ (α' a)) :
    ∀ j, Complex.exp (lamP φ α v Q j) = φ (∏ a, α' a ^ (A j a)) ∧
      (∏ a, α' a ^ (A j a)) ≠ 0 := by
  intro j
  have hlin := lamP_sum φ α v L A Q hQ j
  constructor
  · rw [hlin]
    exact (phi_prod_zpow_exp φ α' hα' (fun a => lamP φ α v L a) h (A j)).symm
  · exact Finset.prod_ne_zero_iff.mpr fun a _ => zpow_ne_zero _ (hα' a)

end Work.BW
