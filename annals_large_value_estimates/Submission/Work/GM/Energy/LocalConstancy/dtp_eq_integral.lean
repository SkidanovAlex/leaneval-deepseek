import Mathlib
import Submission.Work.GM.Energy.LocalConstancy.Phi

namespace Work.GM.Energy.LocalConstancy

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform
set_option autoImplicit false

/-- Integrability of `ξ ↦ c * efun (ξ * a) * 𝓕ψ ξ`, immediate from the integrability of `𝓕ψ`
(`PsiBump_fourier_integrable`) and `‖efun _‖ = 1` (`efun_norm`). -/
lemma integrable_efun_mul_fourier (c : ℂ) (a : ℝ) :
    Integrable (fun ξ : ℝ => c * efun (ξ * a) * (𝓕 PsiBump) ξ) :=
  PsiBump_fourier_integrable.bdd_mul
    (continuous_const.mul (efun_continuous.comp (continuous_id.mul continuous_const))
      |>.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ξ => by rw [norm_mul, efun_norm, mul_one])

/-- **Fourier inversion, tested against a single frequency.**  For any real `a`,
`∫ ξ, efun (ξ * a) · 𝓕ψ ξ = ψ a`. -/
lemma integral_efun_mul_fourier (a : ℝ) :
    ∫ ξ : ℝ, efun (ξ * a) * (𝓕 PsiBump) ξ = PsiBump a := by
  rw [PsiBump_fourier_inversion']
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show efun (ξ * a) * (𝓕 PsiBump) ξ = efun (inner ℝ ξ a) * (𝓕 PsiBump) ξ
  rw [Real.inner_apply]

/-- **The Fourier identity behind GM Lemma 11.3.**  For `N ≥ 1` and arbitrary coefficients `b`,
the untwisted Dirichlet polynomial `dtp N b` (of `Phi.lean`) equals the average of its own
translates against the Fourier transform of the flat-top bump `psi = PsiBump` (which is `1` on
`[0,1]`; see `Bump.lean`):

  `dtp N b t = ∫ ξ, dtp N b (t + ξ) * (𝓕 psi) ξ`.

Route: `dtp N b t = Σ_n c_n efun (t * dlog N n)` with `c_n = w(n/N) b_n`; by `dlog_mem`,
`dlog N n ∈ [0,1]`, so Fourier inversion (`PsiBump_fourier_inversion'`, which says
`psi s = ∫ ξ, efun (inner ℝ ξ s) * 𝓕psi ξ`) gives `1 = ∫ ξ, efun (ξ * dlog N n) * 𝓕psi ξ`.
Multiply by `c_n efun (t * dlog N n)` and use `efun_add` (with `(t+ξ)*dlog = t*dlog + ξ*dlog`)
to recognise `c_n efun ((t+ξ) * dlog N n)`.  Interchange the finite sum and the integral with
`MeasureTheory.integral_finsetSum`; each summand is integrable because `‖efun _‖ = 1`
(`efun_norm`) and `𝓕 psi` is integrable (`PsiBump_fourier_integrable`). -/
theorem dtp_eq_integral (N : ℕ) (hN : 1 ≤ N) (b : ℕ → ℂ) (t : ℝ) :
    dtp N b t = ∫ ξ : ℝ, dtp N b (t + ξ) * (𝓕 PsiBump) ξ := by
  simp only [dtp]
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum (Finset.Icc N (2 * N)) (fun n hn =>
    (integrable_efun_mul_fourier
      (((Submission.LargeValues.bumpW ((n : ℝ) / (N : ℝ)) : ℝ) : ℂ) * b n *
        efun (t * dlog N n)) (dlog N n)).congr
      (Filter.Eventually.of_forall fun ξ => by
        show (((Submission.LargeValues.bumpW ((n : ℝ) / (N : ℝ)) : ℝ) : ℂ) * b n *
              efun (t * dlog N n)) * efun (ξ * dlog N n) * (𝓕 PsiBump) ξ
            = (((Submission.LargeValues.bumpW ((n : ℝ) / (N : ℝ)) : ℝ) : ℂ) * b n *
                efun ((t + ξ) * dlog N n)) * (𝓕 PsiBump) ξ
        rw [show (t + ξ) * dlog N n = t * dlog N n + ξ * dlog N n by ring, efun_add]
        ring))]
  refine Finset.sum_congr rfl fun n hn => ?_
  have ha : dlog N n ∈ Set.Icc (0 : ℝ) 1 := dlog_mem N n hN hn
  have key : ∀ ξ : ℝ,
      (((Submission.LargeValues.bumpW ((n : ℝ) / (N : ℝ)) : ℝ) : ℂ) * b n *
          efun ((t + ξ) * dlog N n)) * (𝓕 PsiBump) ξ
        = (((Submission.LargeValues.bumpW ((n : ℝ) / (N : ℝ)) : ℝ) : ℂ) * b n *
            efun (t * dlog N n)) * (efun (ξ * dlog N n) * (𝓕 PsiBump) ξ) := by
    intro ξ
    rw [show (t + ξ) * dlog N n = t * dlog N n + ξ * dlog N n by ring, efun_add]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  rw [integral_const_mul, integral_efun_mul_fourier, PsiBump_eq_one ha, mul_one]

end Work.GM.Energy.LocalConstancy
