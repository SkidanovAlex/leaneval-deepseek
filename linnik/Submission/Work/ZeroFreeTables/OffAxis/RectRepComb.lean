import Mathlib
import Submission.Work.ZeroFreeTables.Rep9.combination_diag

namespace Work.ZeroFreeTables.OffAxis

open DirichletCharacter Complex
open scoped Classical BigOperators

/-- **The repeated-zero diagonal combination of HB (9.1).**

This is the general-height form of `Work.ZeroFreeTables.Rep9.combination_diag`: the hypothesis
`|γ| ≤ H` on the common imaginary part `γ` is *not* used, because the diagonal combination
reduces (term by term, `dRawSum_eq_hbSummandL`) to the pointwise (in `n`) non-negative kernel
`hbSummandL_nonneg`, which holds for arbitrary `γ₀ = γ₁ = γ`.  We therefore reproduce the
`combination_diag` argument verbatim with the height bound dropped. -/
theorem RectRepComb {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) {a lam₁ γ K H : ℝ}
    (hq : 2 ≤ q) (ha : 0 < a) (hK : 0 < K) (hγ : |γ| ≤ H) (hlam : 0 ≤ lam₁) (hχ₁ : χ₁ ≠ 1) :
    0 ≤ (K^2 + K + 1/2) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) 1
          (((1 + a / Real.log q : ℝ)) : ℂ) a lam₁
      + (K^2 + 2*K + 3/4) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ₁
          ((((1 + a / Real.log q : ℝ)) : ℂ) + ((γ : ℝ) : ℂ) * Complex.I) a lam₁
      + (K + 1/2) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) (χ₁^2)
          ((((1 + a / Real.log q : ℝ)) : ℂ) + (((2*γ : ℝ)) : ℂ) * Complex.I) a lam₁
      + (1/4) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) (χ₁^3)
          ((((1 + a / Real.log q : ℝ)) : ℂ) + (((3*γ : ℝ)) : ℂ) * Complex.I) a lam₁ := by
  have hlogq_pos : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hσ : 1 < (1 + a / Real.log q : ℝ) := by
    have : 0 < a / Real.log q := div_pos ha hlogq_pos
    linarith
  have hlogq_inv : 0 ≤ (Real.log q)⁻¹ := le_of_lt (inv_pos.mpr hlogq_pos)
  have key :
      (K^2 + K + 1/2) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) 1
            (((1 + a / Real.log q : ℝ)) : ℂ) a lam₁
        + (K^2 + 2*K + 3/4) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ₁
            ((((1 + a / Real.log q : ℝ)) : ℂ) + ((γ : ℝ) : ℂ) * Complex.I) a lam₁
        + (K + 1/2) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) (χ₁^2)
            ((((1 + a / Real.log q : ℝ)) : ℂ) + (((2*γ : ℝ)) : ℂ) * Complex.I) a lam₁
        + (1/4) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) (χ₁^3)
            ((((1 + a / Real.log q : ℝ)) : ℂ) + (((3*γ : ℝ)) : ℂ) * Complex.I) a lam₁
      = (Real.log q)⁻¹
        * ∑' n, Work.ZeroFreeTables.P3.hbSummandL q χ₁ K (1 + a / Real.log q) γ γ a lam₁ n := by
    rw [Work.ZeroFreeTables.Rep9.combination_diag_eq_finsum (χ := χ₁) (K := K)
      (σ := 1 + a / Real.log q) (γ := γ) (a := a) (lam₁ := lam₁)]
    rw [← Work.ZeroFreeTables.Rep9.tsum_dRawSum_eq (q := q) hq χ₁
      (σ := 1 + a / Real.log q) hσ K γ a lam₁]
    congr 1
    exact tsum_congr
      (fun n => Work.ZeroFreeTables.Rep9.dRawSum_eq_hbSummandL χ₁ K (1 + a / Real.log q) γ a lam₁ n)
  rw [key]
  exact mul_nonneg hlogq_inv
    (tsum_nonneg (fun n => Work.ZeroFreeTables.P9.hbSummandL_nonneg χ₁ hq hσ ha hlam n))

end Work.ZeroFreeTables.OffAxis
