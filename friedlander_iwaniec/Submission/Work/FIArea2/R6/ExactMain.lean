/-
# `FIArea2/R6/ExactMain.lean` — the exact (6.13)/(9.11) main term `D₀^exact`

*FI* (9.10) is stated at `D₀` of (9.11) whose `C₀` is (6.13) with the **exact** Fourier integral
`F₀(z₁,z₂)` of (6.11).  This module fixes that object (`C0ex`, `D0ex`) — the `h = 0` term of the
Poisson expansion (6.9), i.e. `|z₁z₂|^{-1/2}·Re(Fint F γ_{z₁z₂} 0 0 · Gsum z₁ z₂ 0 0)` — together
with the pair-sum reduction of `D* − D₀^exact`, so that

* the route to (9.10) (`R6/sec9_error_of_pair_H_gen`, the per-pair (9.1) bound with the weight
  `Haver` kept and a general derivative constant) can be summed against `C0ex`, and
* the replacement error `D₀^exact − D₀` (the (7.10)+(8.6) step of §10) can be estimated per pair.

`D0ex` is *real by construction* (`re` is taken inside `C0ex`), so no symmetry of the kernel is
needed in the reduction below.
-/
import Mathlib
import Submission.Work.FIArea2.sec9_error_Hweight
import Submission.Work.FITop4.Defs6

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The exact (6.13) kernel**: `|z₁z₂|^{-1/2}·Re(Fint F γ_{z₁z₂} 0 0 · Gsum z₁ z₂ 0 0)`.
The `h = 0` term of the Poisson expansion (6.9) (whose `Gsum z₁ z₂ 0 0` is the count (6.12) by
`Gsum_zero_zero`), with the elliptic integral `Fint F γ 0 0 = F₀(z₁,z₂)` of (6.11). -/
def C0ex (F : ℝ → ℝ) (z1 z2 : GaussianInt) : ℝ :=
  (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
    * (Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
        * Work.FIArea2.Gsum z1 z2 0 0).re

/-- **(9.11) with the exact (6.13)**: `D₀^exact = Σ_{(z₁,z₂)=1} Re(β_{z₁}β̄_{z₂})C₀^{exact}(z₁,z₂)`,
a real number. -/
def D0ex (Rz : ℤ) (F : ℝ → ℝ) (β : GaussianInt → ℂ) : ℝ :=
  ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
    (if Work.FIPlan.GaussCoprime z1 z2 then
      (β z1 * star (β z2)).re * C0ex F z1 z2
    else 0)

/-- `D0ex` against the pair sum over the round-6 box. -/
theorem D0ex_eq (Pa : Work.FITop.Params) (F : ℝ → ℝ) (β : GaussianInt → ℂ) :
    D0ex (Work.FITop.radN Pa) F β
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * star (β z2)).re * C0ex F z1 z2
          else 0) := rfl

/-- **(5.26) minus (9.11) at the exact main term**: `D* − D₀^exact` is the
`Re(β_{z₁}β̄_{z₂})`-weighted sum of the per-pair errors of (9.1). -/
theorem Dstar_sub_D0ex (Pa : Work.FITop.Params) (f : ℤ → ℝ) (F : ℝ → ℝ)
    (β : GaussianInt → ℂ) (hFint : ∀ n : ℤ, F (n : ℝ) = f n) :
    Work.FITop3.Dstar Pa f β - D0ex (Work.FITop.radN Pa) F β
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * star (β z2)).re
              * (Work.FIArea2.Ccount Pa f z1 z2 - C0ex F z1 z2)
          else 0) := by
  have hC : ∀ z1 z2 : GaussianInt,
      Work.FIArea2.Ccount Pa f z1 z2 = Work.FIArea2.Ccount Pa (fun n : ℤ => F n) z1 z2 := by
    intro z1 z2
    unfold Work.FIArea2.Ccount
    exact Finset.sum_congr rfl fun w _ => by rw [← hFint]
  rw [Work.FIArea2.Dstar_eq_pairSum Pa f β, D0ex_eq]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z1 _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z2 _ => ?_
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2 <;> simp [hc, mul_sub]

/-- The **norm bound**: `|D* − D₀^exact|` is at most the `‖β_{z₁}‖‖β_{z₂}‖`-weighted sum of the
per-pair (9.1) errors (`Ccount` complexified against the exact `h = 0` Poisson term, i.e. the
complex quantity whose real part is `Ccount − C0ex`). -/
theorem abs_Dstar_sub_D0ex_le (Pa : Work.FITop.Params) (f : ℤ → ℝ) (F : ℝ → ℝ)
    (β : GaussianInt → ℂ) (hFint : ∀ n : ℤ, F (n : ℝ) = f n) :
    |Work.FITop3.Dstar Pa f β - D0ex (Work.FITop.radN Pa) F β|
      ≤ ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            ‖β z1‖ * ‖β z2‖
              * ‖((Work.FIArea2.Ccount Pa (fun n : ℤ => F n) z1 z2 : ℝ) : ℂ)
                  - (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ)
                      * (Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
                          * Work.FIArea2.Gsum z1 z2 0 0)‖
          else 0) := by
  rw [Dstar_sub_D0ex Pa f F β hFint]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun z1 _ => ?_
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun z2 _ => ?_
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2
  · rw [if_pos hc, if_pos hc]
    set c : ℝ := ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
    set Z : ℂ := Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
        * Work.FIArea2.Gsum z1 z2 0 0 with hZdef
    set W : ℂ := ((Work.FIArea2.Ccount Pa (fun n : ℤ => F n) z1 z2 : ℝ) : ℂ)
        - ((c : ℝ) : ℂ) * Z with hWdef
    have hC : Work.FIArea2.Ccount Pa f z1 z2
        = Work.FIArea2.Ccount Pa (fun n : ℤ => F n) z1 z2 := by
      unfold Work.FIArea2.Ccount
      exact Finset.sum_congr rfl fun w _ => by rw [← hFint]
    have hre : W.re = Work.FIArea2.Ccount Pa f z1 z2 - C0ex F z1 z2 := by
      rw [hWdef]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      rw [hC]
      unfold C0ex
      rw [hZdef, hcdef]
    have h3 : |(β z1 * star (β z2)).re| ≤ ‖β z1‖ * ‖β z2‖ := by
      calc |(β z1 * star (β z2)).re| ≤ ‖β z1 * star (β z2)‖ := Complex.abs_re_le_norm _
        _ = ‖β z1‖ * ‖β z2‖ := by rw [norm_mul, norm_star]
    calc |(β z1 * star (β z2)).re
            * (Work.FIArea2.Ccount Pa f z1 z2 - C0ex F z1 z2)|
        = |(β z1 * star (β z2)).re|
            * |Work.FIArea2.Ccount Pa f z1 z2 - C0ex F z1 z2| := abs_mul _ _
      _ = |(β z1 * star (β z2)).re| * |W.re| := by rw [hre]
      _ ≤ ‖β z1‖ * ‖β z2‖ * ‖W‖ := by
          refine le_trans (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm W) (abs_nonneg _)) ?_
          exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
  · rw [if_neg hc, if_neg hc]; simp

end

end Work.FIArea2.R6
