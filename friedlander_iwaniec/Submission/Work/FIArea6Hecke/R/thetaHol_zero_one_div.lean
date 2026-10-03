/-
# `Submission.Work.FIArea6Hecke.R.thetaHol_zero_one_div`

The Poisson/Poisson-dual transformation of the **holomorphic** theta series `thetaHol` of a strict
character `χ` modulo `4d` at the single point `u = 1/x`, in the *dual* form in which it is consumed
by the Mellin-transform argument for the Hecke `L`-function of `ℚ(i)`:

  `thetaHol χ 0 (1/x) = x·(Σ_{u∈μ₄}χ(u))⁻¹·(16d²)⁻¹·thetaDual d χ (x/(16d²))`,   `x > 0`,

where `thetaDual d χ w = Σ_{ξ ∈ ℤ[i]} ĝ(ξ)·e^{-π|ξ|²w}` (`ĝ(ξ) = gaussSum d χ ξ`) is the dual
theta function (`Submission.Work.FIArea6Hecke.R.A6HeckeDual`).

The input is the twisted Poisson summation identity for the *odd*-summed theta series
(`thetaOdd_eq_poisson_form`, `Submission.Work.FIArea5.S16Hecke.thetaOdd_poisson`) together with the
elementary relation `thetaOdd χ m u = unitSum χ m · thetaHol χ m u` between the sum over the odd
elements and the sum over the primary coset
(`thetaOdd_eq_unitSum_mul_thetaHol`, `Submission.Work.FIArea5.S16Hecke`).  The whole content is
therefore the normalisation of the dual variable `w = 1/(16d²u)` and of the prefactor
`(16d²u)^{-1}`; no primitivity of `χ` is needed.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.A6HeckeDual
import Submission.Work.FIArea5.S16Hecke.thetaOdd_poisson
import Submission.Work.FIArea5.S16Hecke.thetaOdd_eq_unitSum_mul_thetaHol

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- The `m = 0` Poisson form of the odd theta series, written as `thetaDual` at the dual point
`x/(16d²)`: the inner frequency sum of `thetaOdd_eq_poisson_form` with `m = 0` and `u = 1/x`. -/
private lemma thetaOdd_zero_poisson_tsum (d : ℕ) (chi : GaussianInt → ℂ) {x : ℝ} :
    (∑' ξ : ℤ × ℤ, Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩ *
        ((((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ 0) *
        Complex.exp (-Real.pi * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) /
          ((((1 / x : ℝ)) : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2))))
      = thetaDual d chi (x / (16 * (d : ℝ) ^ 2)) := by
  rw [thetaDual]
  refine tsum_congr (fun ξ => ?_)
  have harg : -Real.pi * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) /
        ((((1 / x : ℝ)) : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2))
      = -Real.pi * ((((ξ.1 : ℝ) : ℂ) ^ 2 + ((ξ.2 : ℝ) : ℂ) ^ 2) *
          (((x / (16 * (d : ℝ) ^ 2)) : ℝ) : ℂ)) := by
    push_cast
    field_simp
    ring
  rw [pow_zero, mul_one, harg]

theorem thetaHol_zero_one_div {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hU : Work.FIArea5.S16Hecke.unitSum chi 0 ≠ 0) {x : ℝ} (hx : 0 < x) :
    Work.FIArea5.S16Hecke.thetaHol chi 0 (1 / x) =
      (x : ℂ) * ((Work.FIArea5.S16Hecke.unitSum chi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2)) *
        Work.FIArea6Hecke.R.thetaDual d chi (x / (16 * (d : ℝ) ^ 2))) := by
  have hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w := hchi.1.2.1
  have hu : (0 : ℝ) < 1 / x := div_pos one_pos hx
  have hpois := Work.FIArea5.S16Hecke.thetaOdd_eq_poisson_form d hd chi hchi 0 hu
  rw [Work.FIArea5.S16Hecke.thetaOdd_eq_unitSum_mul_thetaHol chi 0 hmul (1 / x)] at hpois
  rw [thetaOdd_zero_poisson_tsum d chi (x := x)] at hpois
  have hcoef : (1 / (((4 * d : ℕ) : ℂ) ^ 2)) * (-Complex.I) ^ 0 *
        ((((1 / x : ℝ)) : ℂ) ^ (0 + 1))⁻¹
      = (x : ℂ) * (1 / (16 * (d : ℝ) ^ 2)) := by
    push_cast
    field_simp
    ring
  rw [hcoef] at hpois
  have hprod : (Work.FIArea5.S16Hecke.unitSum chi 0) * Work.FIArea5.S16Hecke.thetaHol chi 0 (1 / x)
      = (x : ℂ) * (1 / (16 * (d : ℝ) ^ 2)) *
          Work.FIArea6Hecke.R.thetaDual d chi (x / (16 * (d : ℝ) ^ 2)) := hpois
  have hmain : Work.FIArea5.S16Hecke.thetaHol chi 0 (1 / x) =
      (x : ℂ) * ((Work.FIArea5.S16Hecke.unitSum chi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2)) *
        Work.FIArea6Hecke.R.thetaDual d chi (x / (16 * (d : ℝ) ^ 2))) := by
    calc Work.FIArea5.S16Hecke.thetaHol chi 0 (1 / x)
        = (Work.FIArea5.S16Hecke.unitSum chi 0)⁻¹ *
            ((Work.FIArea5.S16Hecke.unitSum chi 0) *
              Work.FIArea5.S16Hecke.thetaHol chi 0 (1 / x)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hU, one_mul]
      _ = (Work.FIArea5.S16Hecke.unitSum chi 0)⁻¹ *
            ((x : ℂ) * (1 / (16 * (d : ℝ) ^ 2)) *
              Work.FIArea6Hecke.R.thetaDual d chi (x / (16 * (d : ℝ) ^ 2))) := by
          rw [hprod]
      _ = (x : ℂ) * ((Work.FIArea5.S16Hecke.unitSum chi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2)) *
              Work.FIArea6Hecke.R.thetaDual d chi (x / (16 * (d : ℝ) ^ 2))) := by
          ring
  rw [hmain]

end

end Work.FIArea6Hecke.R
