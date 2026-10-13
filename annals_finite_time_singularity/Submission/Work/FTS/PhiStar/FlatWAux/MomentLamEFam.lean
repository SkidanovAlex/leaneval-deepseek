import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Series.eFam_zero_moment
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

/-- The `λ_m`-weighted eigenfunction `λ_m e_m(θ)` has vanishing moment against `sin θ cos²θ` over
`Iθ = [0, π/2]`, and the corresponding integrand is integrable on `Iθ`.

This is the `m`-th component of the *moment* condition

  `∫_θ (λ_m e_m(θ)) · sin θ cos²θ dθ = 0`,

which is what makes the kernel direction of `Lzero` (i.e. `m = 0`) drop out of every mode
expansion.

The reason is the orthogonality `eFam_orthogonal`: `Iθ` is `[0, π/2]`, which differs from the
integration range `(0, π/2)` only by the two endpoints (a null set), and pointwise

  `λ_m e_m(θ) · sin θ cos²θ = (λ_m / 3) · e_m(θ) · e_0(θ) · cos θ`

because `e_0(θ) = 3 sin θ cos θ` (`eFam_zero_apply`) and the self-adjoint weight of the family is
`cos θ dθ`.  For `m ≠ 0` the last integral vanishes by `eFam_orthogonal`; for `m = 0` it does not,
but then the prefactor `λ_0 = 0` kills it.  Integrability is continuity on the compact interval
`Iθ`: `e_m(θ) = cos θ · C^{(3/2)}_{2m+1}(sin θ)` is a polynomial in `sin θ, cos θ`. -/
theorem MomentLamEFam (m : ℕ) :
    (∫ θ in Work.Spaces.Iθ,
      (Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * Work.Elliptic.sinCos2 θ) = 0
    ∧ MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  constructor
  · -- the vanishing of the moment: reduce to the orthogonality of `eFam m` against `eFam 0`
    have hkey : Work.FTS.PhiStar.Gegenbauer.lam m *
        (∫ θ in (0 : ℝ)..(Real.pi / 2),
          Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ
            * Real.cos θ) = 0 := by
      by_cases hm : m = 0
      · -- `m = 0`: the prefactor `lam 0 = 0` kills the term (the `m = 0` moment does not vanish)
        subst hm
        simp [Work.FTS.PhiStar.Gegenbauer.lam]
      · -- `m ≠ 0`: orthogonality of the eigenfunctions with respect to `cos θ dθ`
        rw [Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal m 0 hm, mul_zero]
    -- the two integrands differ by the pointwise identity `e_0(θ) cos θ = 3 sin θ cos²θ`
    have hpt : ∀ θ : ℝ,
        (Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            * Work.Elliptic.sinCos2 θ
          = (Work.FTS.PhiStar.Gegenbauer.lam m / 3)
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ
                * Real.cos θ) := by
      intro θ
      rw [Work.FTS.PhiStar.Series.eFam_zero_apply]
      simp only [Work.Elliptic.sinCos2]
      ring
    have hpile : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    -- move from the closed set `Iθ = Icc 0 (π/2)` to the interval integral `0..π/2`
    have hmain : (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            * Work.Elliptic.sinCos2 θ)
        = (Work.FTS.PhiStar.Gegenbauer.lam m / 3)
          * (∫ θ in (0 : ℝ)..(Real.pi / 2),
              Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ
                * Real.cos θ) := by
      rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
        (intervalIntegral.integral_of_le hpile).symm]
      rw [show (∫ θ in (0 : ℝ)..(Real.pi / 2),
            (Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              * Work.Elliptic.sinCos2 θ)
          = ∫ θ in (0 : ℝ)..(Real.pi / 2),
              (Work.FTS.PhiStar.Gegenbauer.lam m / 3)
                * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
                    * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ)
        from intervalIntegral.integral_congr (fun θ _ => hpt θ)]
      rw [intervalIntegral.integral_const_mul]
    rw [hmain]
    have hdiv : (Work.FTS.PhiStar.Gegenbauer.lam m / 3) *
        (∫ θ in (0 : ℝ)..(Real.pi / 2),
          Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ
            * Real.cos θ)
        = (Work.FTS.PhiStar.Gegenbauer.lam m *
          (∫ θ in (0 : ℝ)..(Real.pi / 2),
            Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ
              * Real.cos θ)) / 3 := by ring
    rw [hdiv, hkey, zero_div]
  · -- integrability: the integrand is continuous (a polynomial in `sin θ`, `cos θ`) and `Iθ`
    -- is compact
    have heFam : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
      change Continuous (fun θ : ℝ => Real.cos θ *
        Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
      exact Real.continuous_cos.mul
        ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp
          Real.continuous_sin)
    have hsinCos2 : Continuous Work.Elliptic.sinCos2 := by
      change Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)
    have hcont : Continuous (fun θ : ℝ =>
        (Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * Work.Elliptic.sinCos2 θ) :=
      (heFam.const_mul (Work.FTS.PhiStar.Gegenbauer.lam m)).mul hsinCos2
    simpa only [Work.Spaces.Iθ] using
      hcont.integrableOn_Icc (a := (0 : ℝ)) (b := Real.pi / 2)

end Work.FTS.PhiStar.FlatWAux
