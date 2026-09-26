import Mathlib
import Submission.Work.Modular.Basic

/-!
# The `q`-expansion of the weight-six Eisenstein series `E₆`

We compute the coefficients of the `q`-expansion of Mathlib's normalized weight-six
Eisenstein series
`E₆(τ) = 1 - 504 ∑_{n ≥ 1} σ₅(n) qⁿ`,  `q = exp (2 π i τ)`:

`(qExpansion 1 E₆).coeff n = 1` for `n = 0` and `-504 σ₅(n)` for `n ≥ 1`.

`E₆` is by definition the normalized level-one Eisenstein series `E (hk : 3 ≤ 6)` of
Mathlib, whose `q`-expansion coefficients are given by
`EisensteinSeries.E_qExpansion_coeff`:
`-(2 k / B_k) σ_{k-1}(m)` for `m ≥ 1`, where `B_k` is the `k`-th Bernoulli number.
The only numerical input is `B_6 = 1/42`, giving `-2·6/(1/42) = -504`.
-/

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

/-- The sixth Bernoulli number: `B₆ = 1/42`.  With this, the Eisenstein-series
normalization constant `-2·6/B₆` of weight six equals `-504`. -/
lemma bernoulli_six : bernoulli 6 = 1 / 42 := by decide +kernel

theorem E6_qExpansion_coeff (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 E6).coeff n =
      if n = 0 then 1 else -504 * ((ArithmeticFunction.sigma 5 n : ℕ) : ℂ) := by
  have h := EisensteinSeries.E_qExpansion_coeff (k := 6) (by norm_num) (by norm_num) n
  rw [h]
  split_ifs with hn
  · rfl
  · rw [bernoulli_six]
    norm_num

end Work.Modular
