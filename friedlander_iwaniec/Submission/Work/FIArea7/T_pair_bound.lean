import Mathlib
import Submission.Work.FIArea7.sum_xiC_gBox_exact
import Submission.Work.FIArea7.dirichletSym_eq_xiC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-- **The per-pair inner sum of *FI* Lemma 21.2, in the form the Cauchy–Schwarz step consumes.**
With `q = |w₁|²|w₂|²` and `A = ⌊(2Rz+1)/q⌋`, the box sum of the product of the two Dirichlet symbols
is the complete character sum (scaled by `A²`) plus an explicit error:

  `‖Σ_{z ∈ gBox Rz} ξ_{w₁}(z)ξ_{w₂}(z)‖ ≤ A²·‖Σ_{p ∈ (Z/q)²} ξ_{w₁}(p)ξ_{w₂}(p)‖ + 2((2Rz+1)q + q²)`.

This is `Work.FIArea7.sum_xiC_gBox_exact` (the "elementary counting" display of *FI* Lemma 21.2)
with the box sum of `DirichletSym` identified with the `xiC` sum through
`Work.FIArea7.dirichletSym_eq_xiC` (using `|wᵢ|² ∣ q`).  The complete sum on the right is the exact
orthogonality value given by the corrected Lemma 21.1 (`Work.FIArea7.sum_xiC_general`); in the
trivial case it is bounded by `q²`. -/
theorem T_pair_bound (Rz : ℤ) (N1 N2 : ℕ) [NeZero N1] [NeZero N2] (w1 w2 : GaussianInt)
    (hN1 : Work.FIPlan.gnorm w1 = N1) (hN2 : Work.FIPlan.gnorm w2 = N2) :
    ‖∑ z ∈ Work.FIPlan.gBox Rz,
        (DirichletSym w1 z : ℂ) * (DirichletSym w2 z : ℂ)‖
      ≤ ((((2 * Rz + 1).toNat / (N1 * N2) : ℕ) : ℝ))^2
          * ‖∑ p : ZMod (N1 * N2) × ZMod (N1 * N2),
              xiC (N1 * N2) w1 p * xiC (N1 * N2) w2 p‖
        + 2 * (((2 * Rz + 1).toNat : ℝ) * ((N1 * N2 : ℕ) : ℝ) + ((N1 * N2 : ℕ) : ℝ)^2) := by
  classical
  haveI : NeZero (N1 * N2) := ⟨mul_ne_zero (NeZero.ne N1) (NeZero.ne N2)⟩
  -- `|wᵢ|² = Nᵢ` divides `q = N₁N₂`.
  have hdvd1 : Work.FIPlan.gnorm w1 ∣ N1 * N2 := by rw [hN1]; exact dvd_mul_right N1 N2
  have hdvd2 : Work.FIPlan.gnorm w2 ∣ N1 * N2 := by rw [hN2]; exact dvd_mul_left N2 N1
  -- Step 1: identify the box sum of the two Dirichlet symbols with the `xiC` box sum.
  have hbox : (∑ z ∈ Work.FIPlan.gBox Rz,
        (DirichletSym w1 z : ℂ) * (DirichletSym w2 z : ℂ))
      = ∑ z ∈ Work.FIPlan.gBox Rz,
          xiC (N1 * N2) w1 ((z.re : ZMod (N1*N2)), (z.im : ZMod (N1*N2)))
            * xiC (N1 * N2) w2 ((z.re : ZMod (N1*N2)), (z.im : ZMod (N1*N2))) := by
    apply Finset.sum_congr rfl
    intro z _
    rw [← dirichletSym_eq_xiC (N1*N2) w1 z hdvd1, ← dirichletSym_eq_xiC (N1*N2) w2 z hdvd2]
  -- Step 2: apply the elementary counting of `sum_xiC_gBox_exact`.
  obtain ⟨E, hE, hsum⟩ := sum_xiC_gBox_exact N1 N2 w1 w2 Rz hN1 hN2
  rw [hbox, hsum]
  -- Step 3: triangle inequality and `‖E‖` bound.
  calc ‖(((2 * Rz + 1).toNat / (N1 * N2) : ℕ) : ℂ) ^ 2
        * (∑ p : ZMod (N1 * N2) × ZMod (N1 * N2),
            xiC (N1 * N2) w1 p * xiC (N1 * N2) w2 p) + E‖
      ≤ ‖(((2 * Rz + 1).toNat / (N1 * N2) : ℕ) : ℂ) ^ 2
        * (∑ p : ZMod (N1 * N2) × ZMod (N1 * N2),
            xiC (N1 * N2) w1 p * xiC (N1 * N2) w2 p)‖ + ‖E‖ := norm_add_le _ _
    _ = ((((2 * Rz + 1).toNat / (N1 * N2) : ℕ) : ℝ)) ^ 2
        * ‖∑ p : ZMod (N1 * N2) × ZMod (N1 * N2),
            xiC (N1 * N2) w1 p * xiC (N1 * N2) w2 p‖ + ‖E‖ := by
        rw [norm_mul, norm_pow, Complex.norm_natCast]
    _ ≤ ((((2 * Rz + 1).toNat / (N1 * N2) : ℕ) : ℝ)) ^ 2
        * ‖∑ p : ZMod (N1 * N2) × ZMod (N1 * N2),
            xiC (N1 * N2) w1 p * xiC (N1 * N2) w2 p‖
        + 2 * (((2 * Rz + 1).toNat : ℝ) * ((N1 * N2 : ℕ) : ℝ) + ((N1 * N2 : ℕ) : ℝ)^2) := by
        linarith [hE]

end Work.FIArea7
