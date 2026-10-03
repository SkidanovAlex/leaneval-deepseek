/-
# `Submission.Work.FIChain.s3InnerInt_eq_split` — the `(1.7)`-split *inside* the `λ⁺` level
integral

Starting point: the PROVED `Work.FIChain.Work.FIChain.s3InnerInt_eq_dsum`

    s3InnerInt atilc x ℓ Cm z sz
      = ∫_1^U (du/u) Σ_{d ≤ ⌊u⌋₊} μ d ·
          (Ad atilc (ℓ d) (min (ℓ sz) x) − Ad atilc (ℓ d) (max (ℓ z) (ℓ Cm u))),   U = min …

(the divisor form of the `λ⁺` inner sum, obtained from
`S3plusInnerC_eq_s3InnerInt` + `innerC_u_eq`).  Applying the PROVED `(1.7)`-split
`Work.FIChain.Ad_atilc_split_real`,
`Ad atilc d X = FIgtil d · Ã(⌊X⌋₊) + r̃(ℓd, ⌊X⌋₊)`, at the two `Ad`'s splits the integrand into
the paper's **main term** (the density `FIgtil(ℓd)` times the counting-function difference) and
the **remainder** `r̃`, exactly as in the companion's (8.2):

    s3InnerInt atilc x ℓ Cm z sz
      = ∫_1^U (du/u) Σ_{d ≤ ⌊u⌋₊} μ d ·
          ( FIgtil (ℓ d) · (Ã(⌊min (ℓ sz) x⌋₊) − Ã(⌊max (ℓ z) (ℓ Cm u)⌋₊))
            + r̃(ℓ d, ⌊min (ℓ sz) x⌋₊) − r̃(ℓ d, ⌊max (ℓ z) (ℓ Cm u)⌋₊) ).

This is the input of the two surviving estimates (MAIN by `(2.4)` + the `n`-swap; REM by `(R′)`
and the fibre grouping `ζ = ebd`); see `NOTES_S3plusC_route.md` SESSION 8 and
`NOTES_S3plusC_session9.md`.
-/
import Mathlib
import Submission.Work.FIChain.Ad_atilc_split_real
import Submission.Work.FIChain.s3InnerInt_eq_dsum

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The `(1.7)`-split inside the `λ⁺` level integral** (see the module docstring). -/
theorem s3InnerInt_eq_split (x ℓ Cm : ℕ) (z sz : ℝ)
    (hℓ : 1 ≤ ℓ) (hCm : 1 ≤ Cm) (hsz1 : 1 ≤ sz) (hzsz : z ≤ sz)
    (hzN : (ℓ : ℝ) * z ≤ (x : ℝ)) (hCmz : (Cm : ℝ) ≤ z) (hT : 1 ≤ sz / (Cm : ℝ)) :
    s3InnerInt atilc x ℓ Cm z sz
      = ∫ u in (1 : ℝ)..(min (sz / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
          (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
            (Submission.ASP.FIgtil (ℓ * d)
                * AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
              + Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
                  Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
                  ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
              - (Submission.ASP.FIgtil (ℓ * d)
                  * AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊
                + Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
                    Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
                    ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊))) / u := by
  rw [Work.FIChain.Work.FIChain.s3InnerInt_eq_dsum atilc x ℓ Cm z sz
    hℓ hCm hsz1 hzsz hzN hCmz hT]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Ad_atilc_split_real (ℓ * d) (min ((ℓ : ℝ) * sz) ((x : ℝ))),
    Ad_atilc_split_real (ℓ * d) (max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u))]

end

end Work.FIChain
