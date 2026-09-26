import Mathlib
import Submission.Work.Modular.Basic

/-!
# The `q`-expansion of the weight-four Eisenstein series `E₄`

We compute the coefficients of the `q`-expansion of the normalized weight-four
Eisenstein series
`E₄(τ) = 1 + 240 ∑_{n ≥ 1} σ₃(n) qⁿ`,  `q = exp (2 π i τ)`:

`(qExpansion 1 E₄).coeff n = 1` for `n = 0` and `240 σ₃(n)` for `n ≥ 1`.

The proof is a direct application of Mathlib's `EisensteinSeries.E_qExpansion_coeff`
for the normalized level-one Eisenstein series of even weight `k ≥ 3`.  For `k = 4` the
coefficient `-(2 * 4 / bernoulli 4) = -(8 / (-1/30)) = 240`, using `bernoulli 4 = -1/30`.
-/

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

theorem E4_qExpansion_coeff (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 E4).coeff n =
      if n = 0 then 1 else 240 * ((ArithmeticFunction.sigma 3 n : ℕ) : ℂ) := by
  have h := EisensteinSeries.E_qExpansion_coeff (k := 4) (by norm_num) (by norm_num) n
  rw [h]
  have hb : bernoulli 4 = -1 / 30 := by decide +kernel
  rw [hb]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte]
    norm_num

end Work.Modular
