import Mathlib
import Submission.Work.BMF.Tkeraux.Basic
import Submission.Work.BMF.tsum_pi_prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.Tkeraux

/-- The Fourier series of the tent factorises over a product of frequencies.  For any scales
`K : Fin k → ℕ` and any `θ : Fin k → ℝ`, the family `c ↦ ∏_j kern (K j) (c j) · e(c_j θ_j)` on
`Fin k → ℤ` is summable in norm, with sum `∏_j (π² K_j/2) · tent (1/(2K_j)) θ_j`.  No positivity
hypothesis on the scales `K j` is needed: the degenerate case `K j = 0` is handled by
`Work.BMF.kern_hasSum_all` / `Work.BMF.kern_summable_norm_all` (module
`Submission.Work.BMF.Tkeraux.Basic`, which this file should import; you will also need
`Submission.Work.BMF.tsum_pi_prod`).
Suggested route: `Work.BMF.tsum_pi_prod` with `φ j c = (kern (K j) c : ℂ) * eZ ((c:ℝ) * θ j)`
and `A j = ((π²(K j : ℝ)/2) * tent (1/(2 (K j : ℝ))) (θ j) : ℝ) : ℂ`; the two hypotheses are
`Work.BMF.kern_hasSum_all` and `Work.BMF.kern_summable_norm_all` (with `‖eZ t‖ = 1`, which is
`Work.BMF.eZ_norm`). -/
theorem tsum_prod_kern (k : ℕ) (K : Fin k → ℕ) (θ : Fin k → ℝ) :
    Summable (fun c : Fin k → ℤ =>
        ∏ j : Fin k, ‖(kern (K j) (c j) : ℂ) * eZ (((c j : ℤ) : ℝ) * θ j)‖) ∧
      (∑' c : Fin k → ℤ,
          ∏ j : Fin k, ((kern (K j) (c j) : ℂ) * eZ (((c j : ℤ) : ℝ) * θ j)))
        = ∏ j : Fin k,
            (((Real.pi ^ 2 * (K j : ℝ) / 2) * tent (1 / (2 * (K j : ℝ))) (θ j) : ℝ) : ℂ) := by
  -- Each factor `φ j` is the Fourier series of the tent of width `1/(2 K j)`, absolutely
  -- summable because `‖eZ _‖ = 1`.  `Work.BMF.tsum_pi_prod` then factorises the sum.
  have h := Work.BMF.tsum_pi_prod (k := k)
    (φ := fun j c => (kern (K j) c : ℂ) * eZ ((c : ℝ) * θ j))
    (A := fun j => (((Real.pi ^ 2 * (K j : ℝ) / 2) * tent (1 / (2 * (K j : ℝ))) (θ j) : ℝ) : ℂ))
    (fun j => Work.BMF.kern_hasSum_all (K j) (θ j))
    (fun j => (Work.BMF.kern_summable_norm_all (K j)).congr (fun c => by
        rw [norm_mul, Work.BMF.eZ_norm, mul_one, Complex.norm_real]))
  exact h

end Work.BMF.Tkeraux
