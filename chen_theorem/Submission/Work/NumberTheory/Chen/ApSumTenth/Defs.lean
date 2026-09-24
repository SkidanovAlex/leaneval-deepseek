/-
# The switched AP-sum at the sift limit `x^{1/10}`: profiles and interfaces

This module fixes the vocabulary used by the assembly of

```
Work.NumberTheory.Chen.ap_sum_tenth :
  ∀ᶠ x, Σ_{q ∈ winPrimes (chenSiftLimitTenth x) (chenWindowTop x)} apMass x (chenSiftLimitTenth x) q
        ≤ (8/5)·x·VsieveOdd (chenSiftLimitTenth x)
```

The switched sum is controlled per residue class `q` by the **`β = 2` (cube) chain main term**
`MpSum2 D M` (Rosser–Iwaniec `λ⁺`, whose chain barrier is `q' ^ 3 ≤ D` at the odd positions and
`q' ≤ D` at the even ones): see `APSwitchUpper.apMassD_le_main_add_bv_beta2`.  At the sifting
ratio `σ = log D / log M` the cube family is the *sharp* chain of the linear sieve, with the
classical delay-difference upper-bound profile

  `F(σ) = 2 e^γ / σ`                                    for `1 ≤ σ ≤ 3`,
  `F(σ) = (2 e^γ / σ)·(1 + ∫_2^{σ - 1} log (t - 1) / t dt)`   for `3 ≤ σ ≤ 4`,

(Bordignon–Johnston–Starichkova, arXiv:2207.09452, (approx-F34); equivalently Rosser–Iwaniec
`F(s) = 1 + Σ_{n odd} f_n(s)` with the `f_n` family of Nathanson Ch. 9).  `Fprof` below is
this `F`, and `Gprof` is the elementary majorant of `F` used to evaluate the window sum
`Σ_{q ∈ W} Gprof(s_q)/(q-1) ≤ 1599/1000` (whose true value, with `F` in place of `Gprof`,
is `≈ 1.522`).
-/
import Mathlib

open scoped BigOperators

namespace Work.NumberTheory.Chen.ApSumTenth

noncomputable section

/-- `2 e^γ`, the constant of the sharp linear-sieve upper-bound profile. -/
noncomputable def twoExpGamma : ℝ := 2 * Real.exp Real.eulerMascheroniConstant

/-- The sharp `λ⁺` delay-difference profile `F` of the linear sieve, on `1 ≤ σ ≤ 4`:
`2e^γ/σ` for `σ ≤ 3` and the exact integral correction for `3 ≤ σ ≤ 4`
(`F(s) = (2e^γ/s)(1 + ∫_2^{s-1} log(t-1)/t dt)`). -/
noncomputable def Fprof (σ : ℝ) : ℝ :=
  if σ ≤ 3 then twoExpGamma / σ
  else (twoExpGamma / σ) * (1 + ∫ t in (2:ℝ)..(σ - 1), Real.log (t - 1) / t)

/-- An elementary majorant of the sharp profile on `3 ≤ σ ≤ 4`:
since `log (t-1)/t` increases on `[2,3]` with `max = log 2/3 ≤ 0.232`, the integral is at most
`0.232·(σ - 3)`.  Hence `Fprof σ ≤ Gprof σ` on `[3,4]`. -/
noncomputable def Gprof (σ : ℝ) : ℝ :=
  if σ ≤ 3 then twoExpGamma / σ
  else (twoExpGamma / σ) * (1 + (232 / 1000 : ℝ) * (σ - 3))

end

end Work.NumberTheory.Chen.ApSumTenth
