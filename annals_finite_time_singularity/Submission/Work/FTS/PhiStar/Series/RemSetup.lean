/-
# `Work.FTS.PhiStar.Series.RemSetup` — the algebraic setup for `psiSeries_solves_rem`

The target `Work.FTS.PhiStar.Series.psiSeries_solves_rem` is about the mode series of the source

  `RemSource α ψ = fun z θ => α^2 * phiA α z * ψ θ`   (separable!),

so its `m`-th mode coefficient factors through the `m`-th Gegenbauer coefficient of `ψ`:

  `cmode m (RemSource α ψ) z = α^2 * phiA α z * cmode m (fun _ θ => ψ θ) 0`

(`cmode m F z` is the weight-`cos θ` coefficient of the slice `F z ·`, so the `z`-slot of a
`z`-independent test function is irrelevant), and `radGreen` is linear in its source, so

  `acoeff α m (RemSource α ψ) z = (α^2 * cmode m (fun _ θ => ψ θ) 0) * radGreen α m (phiA α) z`.

Both are proved here, together with the boundary values `eFam m 0 = eFam m (π/2) = 0` (which make
the Dirichlet conjunct of the target immediate) and the vanishing of the `m = 0` term.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Series.eFam_zero_moment
import Submission.Work.FTS.PhiStar.Series.acoeff_zero_of_fstar
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-! ## `radGreen` is linear in its source -/

/-- `radGreen` commutes with multiplication of the source by a constant. -/
theorem radGreen_const_mul (α : ℝ) (m : ℕ) (k : ℝ) (c : ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m (fun t => k * c t) z
      = k * Work.FTS.PhiStar.Radial.radGreen α m c z := by
  have h1 : (∫ t in (0 : ℝ)..z, (k * c t) * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      = k * ∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  have h2 : (∫ t in Set.Ioi z, (k * c t) * t ^ (-(2 * (m : ℝ) / α) - 1))
      = k * ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring)
  simp only [Work.FTS.PhiStar.Radial.radGreen, h1, h2]
  ring

/-! ## The source `RemSource α ψ` is separable: its mode coefficients factor -/

/-- The `m`-th weight-`cos θ` coefficient of the angular model `ψ`
(the `z`-slot is irrelevant for a `z`-independent function). -/
def bmode (m : ℕ) (ψ : ℝ → ℝ) : ℝ :=
  (∫ θ in (0 : ℝ)..(Real.pi / 2),
      ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
    / (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)

/-- `bmode m ψ` is `cmode m` of the `z`-independent function `fun _ θ => ψ θ`. -/
theorem bmode_eq_cmode (m : ℕ) (ψ : ℝ → ℝ) (z : ℝ) :
    bmode m ψ = cmode m (fun _ θ => ψ θ) z := rfl

/-- **The mode coefficients of `RemSource` factor.** -/
theorem cmode_RemSource (α : ℝ) (m : ℕ) (ψ : ℝ → ℝ) (z : ℝ) :
    cmode m (Work.FTS.PhiStar.RemSource α ψ) z
      = α ^ 2 * Work.FTS.VocabO.phiA α z * bmode m ψ := by
  have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.PhiStar.RemSource α ψ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * Real.cos θ)
      = α ^ 2 * Work.FTS.VocabO.phiA α z
        * (∫ θ in (0 : ℝ)..(Real.pi / 2),
            ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [Work.FTS.PhiStar.RemSource]
    ring
  simp only [cmode, bmode, hnum]
  ring

/-- **The mode coefficients of `psiSeries`.** -/
theorem acoeff_RemSource (α : ℝ) (m : ℕ) (ψ : ℝ → ℝ) (z : ℝ) :
    acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
      = (α ^ 2 * bmode m ψ) * Work.FTS.PhiStar.Radial.radGreen α m
          (Work.FTS.VocabO.phiA α) z := by
  have hfun : (fun t : ℝ => cmode m (Work.FTS.PhiStar.RemSource α ψ) t)
      = fun t : ℝ => (α ^ 2 * bmode m ψ) * Work.FTS.VocabO.phiA α t := by
    funext t
    rw [cmode_RemSource]
    ring
  rw [acoeff, hfun, radGreen_const_mul]

/-- The `m = 0` coefficient of `psiSeries` for the remainder source vanishes: the source moment
`Fstar (RemSource α ψ) ≡ 0` holds by `AngModel.moment`, and `cmode 0` is `3·Fstar`. -/
theorem acoeff_RemSource_zero (α : ℝ) (ψ : ℝ → ℝ)
    (hψ : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.FTS.PhiStar.RemSource α ψ) z = 0) :
    ∀ z, 0 < z → acoeff α 0 (Work.FTS.PhiStar.RemSource α ψ) z = 0 :=
  acoeff_zero_of_fstar α (Work.FTS.PhiStar.RemSource α ψ) hψ

/-- `Fstar (RemSource α ψ) z = α^2 * phiA α z * ∫ θ in Iθ, ψ θ * sinCos2 θ`. -/
theorem Fstar_RemSource (α : ℝ) (ψ : ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Fstar (Work.FTS.PhiStar.RemSource α ψ) z
      = α ^ 2 * Work.FTS.VocabO.phiA α z
        * (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) := by
  simp only [Work.Elliptic.Fstar, Work.FTS.PhiStar.RemSource]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  ring

/-! ## The angular modes vanish at both endpoints -/

/-- `eFam m` vanishes at `θ = 0` (`gC (2m+1)` is odd, `0` for odd indices). -/
theorem eFam_zero_right (m : ℕ) : Work.FTS.PhiStar.Gegenbauer.eFam m 0 = 0 := by
  simpa only [Work.FTS.PhiStar.Gegenbauer.eFam, Real.sin_zero, Real.cos_zero, one_mul,
    mul_zero] using Work.FTS.PhiStar.Gegenbauer.gC_odd_zero m

/-- `eFam m` vanishes at `θ = π/2` (`cos (π/2) = 0`). -/
theorem eFam_zero_left (m : ℕ) :
    Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2) = 0 := by
  simp only [Work.FTS.PhiStar.Gegenbauer.eFam, Real.cos_pi_div_two, zero_mul]

/-! ## The Dirichlet values of `psiSeries` (conjunct 3 of the target) -/

/-- Every term of the mode series vanishes at `θ = 0`, hence so does the series. -/
theorem psiSeries_zero_right (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    psiSeries α F z 0 = 0 := by
  simp only [psiSeries, eFam_zero_right, mul_zero, tsum_zero]

/-- Every term of the mode series vanishes at `θ = π/2`, hence so does the series. -/
theorem psiSeries_zero_left (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    psiSeries α F z (Real.pi / 2) = 0 := by
  simp only [psiSeries, eFam_zero_left, mul_zero, tsum_zero]

end Work.FTS.PhiStar.Series
