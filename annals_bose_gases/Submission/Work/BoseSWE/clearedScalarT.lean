import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseSWE.clearedScalarT` — the cleared ledger arithmetic of the small-window row

This is the pure-real scalar inequality that the `BoseSWE` design (`BRIEF.md`, and
`sources/boseSWE/bose_smallwinholepd.md` §2.3) records as the *ledger* row of the small-window
branch.  The design's normalised ledger is

    f(λ) = ¼(λ−1)² − ½ − ν(λ+½) − ν²/4 − [(δ+κΓ)λ² + 3λν]/(2(1−δ)) − bλ − λ/18 ,

whose claimed minimum over the admissible range is `f(4) ≈ 1.187`.  Clearing denominators
(`δ = 1/50`, so `1/(2(1−δ)) = 49/25`; the slack coefficient `δ + γ` with `0 ≤ γ ≤ 1/50`;
`T` and `n` the cleared `ν⁻¹`-scale and count) gives the inequality below, which is what the
downstream files need: with `T = μV ≥ 1000` (the `Regular` gate) and `n ≥ 4T` (the count range
`λ ∈ [4, 400]` at the bottom end, where the ledger is tight).

## Why it is true

Write `E n` for the left-hand side.  Expanding in `n`,

    E n = (47/100 − γ)·n² − (24941·T/22500 + 124/25)·n − 49·T²/100 − 49·T/50 − 49/100 .

So `E` is a quadratic in `n` with leading coefficient `47/100 − γ ≥ 47/100 − 1/50 = 9/20 > 0`.
Moreover the increment factors exactly:

    E n − E (4T) = −(n − 4T)·(90000·T·γ − 17359·T + 22500·γ·n − 10575·n + 111600)/22500 ,

and for `γ ≤ 1/50`, `T ≥ 1000`, `n ≥ 4T` the bracket is

    90000·T·γ + 22500·γ·n − 17359·T − 10575·n + 111600
      ≤ 1800·T + 450·n − 17359·T − 10575·n + 111600
      = −15559·T − 10125·n + 111600 < 0 ,

while `n − 4T ≥ 0`; hence `E n ≥ E (4T)` — the minimum on the region is attained at the corner
`n = 4T`.  At that corner

    E (4T) = (58411/22500 − 16γ)·T² − 1041·T/50 − 49/100
           ≥ (51211/22500)·T² − 1041·T/50 − 49/100 ,

which is already `≈ 2.28·10⁶` at `T = 1000` and grows quadratically, so it is nonnegative
throughout `T ≥ 1000`.

The proof below performs exactly this reduction: expand (`ring`), factor the increment (`ring`),
bound the bracket and the corner value (`nlinarith`).
-/

namespace Work.BoseSWE

set_option linter.unusedVariables false

theorem clearedScalarT {n T γ : ℝ} (hT : 1000 ≤ T) (hn : 4 * T ≤ n)
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 50) :
    0 ≤ (49 / 25) * ((1 / 4) * (n - T) ^ 2 - (1 / 2) * T ^ 2 - n - T / 2 - (1 / 4)
          - (1 / 100) * n * T - n * T / 18)
        - ((1 / 50 + γ) * n ^ 2 + 3 * n) := by
  -- Expand the left-hand side as a quadratic in `n`
  -- (`E n = (47/100 − γ)·n² − (24941·T/22500 + 124/25)·n − 49·T²/100 − 49·T/50 − 49/100`).
  have hexp : (49 / 25) * ((1 / 4) * (n - T) ^ 2 - (1 / 2) * T ^ 2 - n - T / 2 - (1 / 4)
          - (1 / 100) * n * T - n * T / 18)
        - ((1 / 50 + γ) * n ^ 2 + 3 * n)
      = (47/100 - γ) * n^2 - (24941 * T / 22500 + 124/25) * n
        - (49/100) * T^2 - (49/50) * T - 49/100 := by ring
  rw [hexp]
  -- Exact factorisation of the increment `E n − E (4T)`.
  have hfac : ((47/100 - γ) * n^2 - (24941 * T / 22500 + 124/25) * n
        - (49/100) * T^2 - (49/50) * T - 49/100)
      - ((47/100 - γ) * (4*T)^2 - (24941 * T / 22500 + 124/25) * (4*T)
        - (49/100) * T^2 - (49/50) * T - 49/100)
      = -((n - 4*T) * (90000*T*γ - 17359*T + 22500*γ*n - 10575*n + 111600)) / 22500 := by ring
  -- The bracket is negative on the region, so `E` is increasing in `n` there.
  have hB : 90000*T*γ - 17359*T + 22500*γ*n - 10575*n + 111600 ≤ 0 := by
    nlinarith [hT, hn, hγ,
      mul_le_mul_of_nonneg_right hγ (by linarith : (0:ℝ) ≤ T),
      mul_le_mul_of_nonneg_right hγ (by linarith : (0:ℝ) ≤ n)]
  have hB' : (0:ℝ) ≤ -(90000*T*γ - 17359*T + 22500*γ*n - 10575*n + 111600) := by linarith
  have hprod : (0:ℝ) ≤ (n - 4*T) * -(90000*T*γ - 17359*T + 22500*γ*n - 10575*n + 111600) :=
    mul_nonneg (by linarith) hB'
  -- The corner value `E (4T)` is nonnegative.
  have h2 : 0 ≤ (47/100 - γ) * (4*T)^2 - (24941 * T / 22500 + 124/25) * (4*T)
        - (49/100) * T^2 - (49/50) * T - 49/100 := by
    nlinarith [hT, hγ, hγ0, sq_nonneg (T - 1000)]
  nlinarith [hfac, hprod, h2]

end Work.BoseSWE
