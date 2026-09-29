import Mathlib
import Submission.Work.Haupt.defs
import Submission.Work.Haupt.qp_defs
import Submission.Work.Haupt.theta_spec
import Submission.Work.Haupt.euler_qexp
import Submission.Work.Haupt.semifinite
import Submission.Work.Haupt.semifinite_split
import Submission.Work.Haupt.semifinite_limit
import Submission.Work.Haupt.semifinite_rhs_limit

/-!
# `θ₄` as a product (Jacobi triple product, semi-finite proof)

We assemble the semi-finite proof of the Jacobi triple product

`∑_{n∈ℤ} q^{n(n-1)/2} z^n = (q;q)_∞ (-q/z;q)_∞ (-z;q)_∞   (‖q‖ < 1, z ≠ 0)`

from the pieces in this directory, and specialise it to `q = x²`, `z = -x`, which gives
`T4 x = T4prod x`.
-/

open scoped BigOperators
open Filter Topology

namespace Work.Haupt

/-- The Jacobi triple product, in the normalisation of `qhalfInt`/`qpInf`. -/
theorem triple_product {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    (∑' n : ℤ, qhalfInt q n * z ^ n) = qpInf q q * qpInf (-q/z) q * qpInf (-z) q := by
  have hE : ∀ w : ℂ, ∏' n : ℕ, (1 + w * q ^ n)
      = ∑' n : ℕ, qhalf q n * w ^ n / qpNat q q n := fun w => euler_qexp hq w
  have hsplit : ∀ m : ℕ, (∑' n : ℤ, sfTerm q z m n) = Afun q z m + Bfun q z m :=
    fun m => semifinite_split hq hz m
  have h1 : Tendsto (fun m : ℕ => (∑' n : ℤ, sfTerm q z m n)) atTop
      (𝓝 (∑' n : ℤ, qhalfInt q n * z ^ n)) := semifinite_limit hq hz hsplit
  have h2 : Tendsto (fun m : ℕ => (∑' n : ℤ, sfTerm q z m n)) atTop
      (𝓝 (qpInf q q * qpInf (-q/z) q * qpInf (-z) q)) := by
    have h3 : Tendsto (fun m : ℕ => qpNat q q m * qpNat (-q/z) q m * qpInf (-z) q) atTop
        (𝓝 (qpInf q q * qpInf (-q/z) q * qpInf (-z) q)) := semifinite_rhs_limit hq
    have heq : (fun m : ℕ => (∑' n : ℤ, sfTerm q z m n))
        = (fun m : ℕ => qpNat q q m * qpNat (-q/z) q m * qpInf (-z) q) := by
      funext m
      exact semifinite hq hz m hE
    rw [heq]
    exact h3
  exact tendsto_nhds_unique h1 h2

theorem theta_four_product (x : ℂ) (hx : ‖x‖ < 1) : T4 x = T4prod x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [T4_zero, T4prod_zero]
  · have hx2 : ‖x ^ 2‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
    have hz : -x ≠ 0 := neg_ne_zero.mpr hx0
    have htp := triple_product hx2 hz
    rw [qhalfInt_tsum_eq_T4 x hx0] at htp
    have hfac : -(x ^ 2) / (-x) = x := by
      rw [neg_div_neg_eq, sq, mul_div_cancel_left₀ x hx0]
    rw [hfac, neg_neg] at htp
    rw [← T4prod_eq_qpInf x hx] at htp
    exact htp

end Work.Haupt
