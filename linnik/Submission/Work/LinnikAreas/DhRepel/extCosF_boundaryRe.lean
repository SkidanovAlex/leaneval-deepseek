/-
# The boundary value `Re F(iy) ≥ 0` of Heath-Brown's extremal Laplace transform

`Commons.NumberTheory.Linnik.extCosF θ λ` (Heath-Brown Lemma 7.1's extremal function, for the
parameter `k = 2`) is, on its support `[0, 2γ]` with `γ = θ/(λ tan θ)`, the convolution square
`g * g` of the even function `g = extCosG θ λ` (`extCosF_eq_conv` of `scratch_l71cond.lean`).
Consequently the cosine transform of `extCosF` is a *square* (`convolution_cos_nonneg`), so
`∫₀^{2γ} cos(y t) extCosF θ λ t dt ≥ 0`.

Unwinding the Laplace kernel on the imaginary axis
(`Complex.exp (-(i y t)) = cos(y t) - i sin(y t)`) this is exactly
`Re ∫₀^{2γ} e^{-i y t} extCosF θ λ t dt ≥ 0`, i.e. the boundary case `Re z = 0` of the
half-plane inequality `Re ∫₀^{2γ} e^{-zt} f dt ≥ 0` that the test function of Heath-Brown §7 has
to satisfy (see `SpecOpt.lean`).

The proof is assembled from
* `convCosF_even`, `convCosF_supp`: the convolution square is even and supported in `[-2γ, 2γ]`;
* `integral_even_compact`: for an even function supported in `[-L, L]`, `∫_ℝ φ = 2 ∫₀^L φ`.
-/
import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l71cond
import Submission.Work.NumberTheory.Linnik.scratch_convcos
import Submission.Work.NumberTheory.Linnik.scratch_reF
import Submission.Work.LinnikAreas.DhRepel.convCosF_even
import Submission.Work.LinnikAreas.DhRepel.convCosF_supp
import Submission.Work.LinnikAreas.DhRepel.integral_even_compact

open MeasureTheory intervalIntegral

namespace Work.LinnikAreas.DhRepel

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- The closed-form branch cutting out `extCosF θ λ` on `[0, 2γ]`, copied verbatim so that on
`[0, 2γ]` the (everywhere discontinuous at `0`) function `extCosF` agrees with the globally
continuous function `phiF`. -/
def phiF (θ lam x : ℝ) : ℝ :=
  lam * (1 + Real.tan θ ^ 2) *
    (lam * (1 + Real.tan θ ^ 2) * (θ / (lam * Real.tan θ) - x / 2)
        * Real.cos ((lam * Real.tan θ) * x)
      + lam * (2 * (θ / (lam * Real.tan θ)) - x)
      + Real.sin (2 * θ - (lam * Real.tan θ) * x) / Real.sin (2 * θ)
      - 2 * (1 + Real.sin (θ - (lam * Real.tan θ) * x) / Real.sin θ))

/-- The convolution square `g * g` of Heath-Brown's `g = extCosG θ λ`: its restriction to
`[0, 2γ]` is the extremal function `extCosF θ λ`. -/
noncomputable def convH (θ lam : ℝ) (v : ℝ) : ℝ :=
  ∫ s : ℝ, Commons.NumberTheory.Linnik.extCosG θ lam s * Commons.NumberTheory.Linnik.extCosG θ lam (v - s)

/-- On `[0, 2γ]`, `extCosF` is the closed form `phiF`. -/
theorem extCosF_eq_phiF {θ lam x : ℝ} (hx : x ∈ Set.Icc 0 (2 * (θ / (lam * Real.tan θ)))) :
    Commons.NumberTheory.Linnik.extCosF θ lam x = phiF θ lam x := by
  unfold Commons.NumberTheory.Linnik.extCosF phiF
  rw [if_pos ⟨hx.1, hx.2⟩]

/-- `phiF θ λ` is continuous (for `0 < θ < π/2`, so that `sin θ` and `sin 2θ` do not vanish). -/
theorem continuous_phiF {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Continuous (phiF θ lam) := by
  have hS : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [hθ1, Real.pi_pos]))
  have hS2 : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ1, Real.pi_pos]))
  unfold phiF
  fun_prop

theorem extCosF_boundaryRe {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) (y : ℝ) :
    0 ≤ (∫ t in (0:ℝ)..(2 * (θ / (lam * Real.tan θ))),
        Complex.exp (-((Complex.I * (y : ℂ)) * (t : ℂ))) *
          ((Commons.NumberTheory.Linnik.extCosF θ lam t : ℝ) : ℂ)).re := by
  have htan : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1
  have hζ : 0 < lam * Real.tan θ := mul_pos hlam htan
  have hγ : 0 < θ / (lam * Real.tan θ) := div_pos hθ0 hζ
  have hL : 0 < 2 * (θ / (lam * Real.tan θ)) := by linarith
  have hLnn : 0 ≤ 2 * (θ / (lam * Real.tan θ)) := le_of_lt hL
  have hφcont : Continuous (phiF θ lam) := continuous_phiF hθ0 hθ1
  have hInt : IntervalIntegrable
      (fun t : ℝ => Complex.exp (-((Complex.I * (y : ℂ)) * (t : ℂ))) * ((phiF θ lam t : ℝ) : ℂ))
      volume (0:ℝ) (2 * (θ / (lam * Real.tan θ))) := by
    apply ContinuousOn.intervalIntegrable
    exact ((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-((Complex.I * (y : ℂ)) * (t : ℂ))))).mul
      (Complex.continuous_ofReal.comp hφcont)).continuousOn
  -- Replace `extCosF` by its continuous closed form on the interval.
  have step1 : (∫ t in (0:ℝ)..(2 * (θ / (lam * Real.tan θ))),
        Complex.exp (-((Complex.I * (y : ℂ)) * (t : ℂ))) *
          ((Commons.NumberTheory.Linnik.extCosF θ lam t : ℝ) : ℂ))
      = (∫ t in (0:ℝ)..(2 * (θ / (lam * Real.tan θ))),
        Complex.exp (-((Complex.I * (y : ℂ)) * (t : ℂ))) * ((phiF θ lam t : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hLnn] at ht
    simp only [extCosF_eq_phiF ht]
  rw [step1]
  -- Take the real part of the (now continuous) Laplace kernel.
  have hre : (∫ t in (0:ℝ)..(2 * (θ / (lam * Real.tan θ))),
        Complex.exp (-((Complex.I * (y : ℂ)) * (t : ℂ))) * ((phiF θ lam t : ℝ) : ℂ)).re
      = ∫ t in (0:ℝ)..(2 * (θ / (lam * Real.tan θ))), Real.cos (y * t) * phiF θ lam t := by
    have h := Commons.NumberTheory.Linnik.re_laplace_eq (x₀ := 2 * (θ / (lam * Real.tan θ)))
      (z := Complex.I * (y : ℂ)) (f := phiF θ lam) hInt
    simpa using h
  rw [hre]
  -- Replace `phiF` by the convolution square `convH`.
  have hconv : ∀ t ∈ Set.Icc 0 (2 * (θ / (lam * Real.tan θ))), phiF θ lam t = convH θ lam t := by
    intro t ht
    rw [← extCosF_eq_phiF ht]
    exact Commons.NumberTheory.Linnik.extCosF_eq_conv hθ0 hθ1 hlam ht
  have step3 : (∫ t in (0:ℝ)..(2 * (θ / (lam * Real.tan θ))), Real.cos (y * t) * phiF θ lam t)
      = ∫ t in (0:ℝ)..(2 * (θ / (lam * Real.tan θ))), Real.cos (y * t) * convH θ lam t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hLnn] at ht
    simp only [hconv t ht]
  rw [step3]
  -- Basic properties of `g` and of the convolution square.
  have hGint : Integrable (Commons.NumberTheory.Linnik.extCosG θ lam) :=
    Commons.NumberTheory.Linnik.extCosG_integrable hθ0 hθ1 hlam
  have hHeven : ∀ v, convH θ lam (-v) = convH θ lam v := by
    intro v
    simp only [convH]
    exact convCosF_even hθ0 hθ1 hlam v
  have hHsupp : ∀ v, 2 * (θ / (lam * Real.tan θ)) < |v| → convH θ lam v = 0 := by
    intro v hv
    simp only [convH]
    exact convCosF_supp hθ0 hθ1 hlam hv
  have hHint : Integrable (convH θ lam) := by
    have h := hGint.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hGint
    convert h using 1
    funext v
    rw [convH, MeasureTheory.convolution]
    simp
  have hφint : Integrable (fun v : ℝ => Real.cos (y * v) * convH θ lam v) := by
    have h1 : Integrable (fun v : ℝ => convH θ lam v * Real.cos (y * v)) :=
      hHint.mul_bdd (by fun_prop : AEStronglyMeasurable (fun v : ℝ => Real.cos (y * v)) volume)
        (Filter.Eventually.of_forall (fun v => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _))
    simpa [mul_comm] using h1
  -- Even and compactly supported: `∫_ℝ φ = 2 ∫₀^{2γ} φ`.
  have hC := integral_even_compact hLnn
    (φ := fun v : ℝ => Real.cos (y * v) * convH θ lam v)
    (fun v => by
      show Real.cos (y * (-v)) * convH θ lam (-v) = Real.cos (y * v) * convH θ lam v
      rw [show y * (-v) = -(y * v) by ring, Real.cos_neg, hHeven v])
    (fun v hv => by rw [hHsupp v hv, mul_zero])
    hφint
  -- The full-line cosine transform is a square, hence non-negative.
  have hbare : 0 ≤ ∫ v : ℝ, Real.cos (y * v) * convH θ lam v := by
    have h := Commons.NumberTheory.Linnik.convolution_cos_nonneg
      (g := Commons.NumberTheory.Linnik.extCosG θ lam) hGint
      (fun v => Commons.NumberTheory.Linnik.extCosG_even θ lam v) y
    simpa [convH] using h
  have hhalf : 0 ≤ ∫ v in (0:ℝ)..(2 * (θ / (lam * Real.tan θ))), Real.cos (y * v) * convH θ lam v := by
    have h2 : 0 ≤ 2 * (∫ v in (0:ℝ)..(2 * (θ / (lam * Real.tan θ))), Real.cos (y * v) * convH θ lam v) := by
      rw [← hC]; exact hbare
    linarith
  exact hhalf

end

end Work.LinnikAreas.DhRepel
