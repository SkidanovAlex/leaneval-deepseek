import Mathlib
import Submission.Work.ZeroFreeTables.P9.zetaDiffExplicit_gen
import Submission.Work.ZeroFreeTables.P9.tsum_inv_add_two_shift

namespace Work.ZeroFreeTables.P9

open scoped BigOperators

/-- **Explicit formula for the second derivative of `ζ'/ζ`, real form.**

For `1 < Re s`,

`Re ((logDeriv ζ)''(s)) = 2 * (∑'_u ord_u(Λ)·Re((s-u)^{-3})
   + ∑'_n Re((s+2(n+1))^{-3}) - Re((s-1)^{-3}))`.

This is the real part of the complex identity `zetaDiffExplicit_gen` at `k = 2`:
`∑'_u ord_u(Λ)·(s-u)^{-3} + ∑'_n (s+2(n+1))^{-3}
   = (1/2)·(logDeriv ζ)''(s) + (s-1)^{-3}`. -/
theorem zetaDiffExplicit_re_two {s : ℂ} (hs : 1 < s.re) :
    (iteratedDeriv 2 (logDeriv riemannZeta) s).re
      = 2 * ((∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 3).re)
             + (∑' n : ℕ, ((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3).re)
             - ((1 / (s - 1)) ^ 3).re) := by
  -- the complex identity at `k = 2` (whose leading coefficient is `1/2`)
  obtain ⟨hsumZ, hgen⟩ := zetaDiffExplicit_gen 2 (by norm_num) hs
  -- summability of the (shifted) trivial-zero series
  have hsum_main : Summable (fun n : ℕ => (1 / (s + ((2 * n : ℕ) : ℂ))) ^ 3) :=
    (tsum_inv_add_two_shift 2 (by norm_num) hs).1
  have hsumST : Summable (fun n : ℕ => (1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3) := by
    have h := (summable_nat_add_iff
      (f := fun n : ℕ => (1 / (s + ((2 * n : ℕ) : ℂ))) ^ 3) 1).mpr hsum_main
    simpa using h
  -- real part of the zero sum: pull `Re` inside and use that the multiplicity is real
  have hSZ : (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ 3).re
      = ∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 3).re := by
    rw [Complex.re_tsum hsumZ]
    refine tsum_congr fun u => ?_
    rw [show (analyticOrderNatAt completedRiemannZeta u : ℂ)
          = (((analyticOrderNatAt completedRiemannZeta u : ℝ)) : ℂ) from
        (Complex.ofReal_natCast _).symm, Complex.re_ofReal_mul]
  -- real part of the trivial-zero sum
  have hST : (∑' n : ℕ, (1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3).re
      = ∑' n : ℕ, ((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3).re :=
    Complex.re_tsum hsumST
  -- clean form of the complex identity
  have hgen2 : (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ 3)
        + (∑' n : ℕ, (1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3)
      = (1 / 2 : ℂ) * iteratedDeriv 2 (logDeriv riemannZeta) s + 1 / (s - 1) ^ 3 := by
    have h1 : ((-1 : ℂ) ^ 2) = 1 := by norm_num
    have h2 : ((2 : ℕ).factorial : ℂ) = 2 := by norm_num
    have h3 : (1 / 2 : ℂ) = ((-1 : ℂ) ^ 2) * (1 / ((2 : ℕ).factorial : ℂ)) := by
      rw [h1, h2]; norm_num
    rw [h3]
    exact hgen
  -- take real parts of the identity
  have hre := congrArg Complex.re hgen2
  rw [Complex.add_re, Complex.add_re] at hre
  have hhalf : ((1 / 2 : ℂ) * iteratedDeriv 2 (logDeriv riemannZeta) s).re
      = (1 / 2 : ℝ) * (iteratedDeriv 2 (logDeriv riemannZeta) s).re := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
  have hQ : (1 / (s - 1) ^ 3).re = ((1 / (s - 1)) ^ 3).re := by rw [one_div_pow]
  rw [hhalf, hQ] at hre
  rw [hSZ, hST] at hre
  -- `hre : TZ + TT = (1/2) * D.re + TQ`, and the goal is `D.re = 2 * (TZ + TT - TQ)`
  linarith [hre]

end Work.ZeroFreeTables.P9
