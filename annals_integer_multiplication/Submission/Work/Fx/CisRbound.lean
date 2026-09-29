import Mathlib
import Submission.Work.Fx.scaleCommon
import Submission.Work.Fx.abs_mul_sub_mul_div_le

/-!
# `CisRbound`: error of the truncated approximation of `2^{p+60} · 2π j'/k`

Requested lemma of the `Fx` area (an input to `FxLib.cis`, paper Lemma 2.12).  Let `P₁ = p + 60`,
let `r = Int.fmod j k ∈ [0,k)` (the *nonnegative* remainder, so that `j ≡ r (mod k)`) and let
`u : ℤ` satisfy `|u − 2^{P₁} π| ≤ 1`.  Then the truncating quotient

  `R = Int.tdiv (2 · u · r) k`

approximates `2^{P₁} · (2π r / k)` to within `3`.

The two error terms are:
* truncation: `|R − 2ur/k| < 1` (`tdiv_sub_div_lt_one_x1`);
* perturbation: `|2ur/k − 2^{P₁}·2πr/k| = (2r/k)·|u − 2^{P₁}π| ≤ 2·1 = 2`, because `0 ≤ r < k`
  (`Work.Fx.abs_mul_sub_mul_div_le`).

So `|R − 2^{P₁}·2πr/k| < 1 + 2 = 3`.
-/

set_option autoImplicit false

namespace Work.Fx

theorem CisRbound (p : ℕ) (j : ℤ) (k : ℕ) (hk : 1 ≤ k) (u : ℤ)
    (hu : |(u : ℝ) - 2 ^ (p + 60) * Real.pi| ≤ 1) :
    |(((Int.tdiv (2 * u * Int.fmod j k) k : ℤ)) : ℝ)
      - 2 ^ (p + 60) * (2 * Real.pi * (Int.fmod j k : ℝ) / (k : ℝ))| ≤ 3 := by
  have hkpos : 0 < k := hk
  have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hkpos
  -- range of the nonnegative remainder `r = Int.fmod j k`
  have hr0 : (0 : ℤ) ≤ Int.fmod j k := by
    rw [Int.fmod_eq_emod_of_nonneg j (le_of_lt hkZ)]
    exact Int.emod_nonneg j (ne_of_gt hkZ)
  have hrk : Int.fmod j k < (k : ℤ) := by
    rw [Int.fmod_eq_emod_of_nonneg j (le_of_lt hkZ)]
    exact Int.emod_lt_of_pos j hkZ
  -- (i) truncation error `< 1`
  have h1 : |(((Int.tdiv (2 * u * Int.fmod j k) (k : ℤ) : ℤ)) : ℝ)
      - (((2 * u * Int.fmod j k : ℤ)) : ℝ) / (k : ℝ)| < 1 :=
    tdiv_sub_div_lt_one _ hkZ
  -- (ii) perturbation error `≤ 2`
  have h2 : |(((2 * u * Int.fmod j k : ℤ)) : ℝ) / (k : ℝ)
      - 2 ^ (p + 60) * (2 * Real.pi * (Int.fmod j k : ℝ) / (k : ℝ))| ≤ 2 := by
    have h := abs_mul_sub_mul_div_le hk hr0 hrk (M := 2 ^ (p + 60) * Real.pi) hu
    have heq : (2 * (u : ℝ) * ((Int.fmod j k : ℤ) : ℝ)) / (k : ℝ)
          - (2 * ((Int.fmod j k : ℤ) : ℝ) / (k : ℝ)) * (2 ^ (p + 60) * Real.pi)
        = (((2 * u * Int.fmod j k : ℤ)) : ℝ) / (k : ℝ)
          - 2 ^ (p + 60) * (2 * Real.pi * (Int.fmod j k : ℝ) / (k : ℝ)) := by
      push_cast
      ring
    rw [← heq]
    exact h
  -- combine the two errors
  have htri := dist_triangle (((Int.tdiv (2 * u * Int.fmod j k) (k : ℤ) : ℤ)) : ℝ)
      ((((2 * u * Int.fmod j k : ℤ)) : ℝ) / (k : ℝ))
      (2 ^ (p + 60) * (2 * Real.pi * (Int.fmod j k : ℝ) / (k : ℝ)))
  rw [Real.dist_eq, Real.dist_eq, Real.dist_eq] at htri
  linarith

end Work.Fx
