import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.yc_defs
import Submission.Work.BW.applyDer_Qpoly_span

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

/-- At a degenerate level `J` (every `D_j < 2^J`) every exponent `λ_j / 2^J` in `Qdesc` is `0`,
so the torus monomials of `Q^{(J)}` are trivial and the curve value `fAt ℓ (Q^{(J)}_μ(·;t0,0))`
is the value of the univariate shadow `ycQ` of `yc_defs`. -/
theorem yc_main_identity {K : Type*} [Field K] {n r : ℕ} (ℓ : Fin r → ℂ) (φ : K →+* ℂ)
    (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n)
    (h D0 : ℕ) (Dj : Fin r → ℕ) (p : AuxIdx r h D0 Dj → K) (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ)
    (hDj : ∀ j, (Dj j : ℝ) < 2 ^ J) (z : ℂ) :
    fAt ℓ (Qdesc φ b k L ι h D0 Dj p J μ t0 0) z = (ycQ φ h D0 Dj p J μ t0).eval z := by
  have hnat : ∀ j : Fin r, Dj j < 2 ^ J := fun j => by exact_mod_cast hDj j
  rw [fAt, Qdesc, ycQ]
  rw [MvPolynomial.eval_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun lm _ => ?_)
  by_cases hc : (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j)
  · rw [ite_eq_left hc, ite_eq_left hc]
    have hzero : ∀ j : Fin r, (lm.2.2 j : ℕ) / 2 ^ J = 0 := by
      intro j
      apply Nat.div_eq_of_lt
      have h1 := (lm.2.2 j).isLt
      have h2 := hnat j
      omega
    have hΔ : (∏ m : Fin (r - 1),
        Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) ((0 : Fin (r - 1) → ℕ) m)) = 1 := by
      refine Finset.prod_eq_one (fun m _ => ?_)
      exact Delta_zero _
    have hX : (∏ j : Fin r,
        (MvPolynomial.X j.succ : MvPolynomial (Fin (r + 1)) ℂ) ^ ((lm.2.2 j : ℕ) / 2 ^ J)) = 1 := by
      refine Finset.prod_eq_one (fun j _ => ?_)
      rw [hzero j, pow_zero]
    rw [hΔ, hX, mul_one]
    simp only [mul_one]
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, yc_eval_aeval]
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    simp [ycY0, ycP]
  · rw [ite_eq_right hc, ite_eq_right hc]
    simp

end Work.BW
