import Mathlib
import Submission.Work.Motion.koebe_distortion

/-!
# The second derivative of the Koebe transform

For `f` holomorphic on the unit disc and `z` in the disc with `deriv f z ≠ 0`, the Koebe
transform
`koebeT f z ζ = (f ((ζ+z)/(1+conj z * ζ)) - f z) / ((1 - ‖z‖²) * deriv f z)`
satisfies
`(koebeT f z)''(0) = (1 - ‖z‖²) * f''(z)/f'(z) - 2 * conj z`.

This is the `n = 1` case of the classical expansion of the Koebe transform
`(f ∘ φ_z)'(z)/f'(z) = 1 + (1 - ‖z‖²) f''(z)/f'(z) * ζ + …`; it is the estimate used to
control the second-order distortion of the moving IFS in §6 of Shishikura's proof.

The argument is a direct computation.  With `φ ζ = (ζ+z)/(1+conj z ζ)` we have `φ 0 = z`,
`φ'(0) = 1 - ‖z‖²`, and `φ'(ζ) = (1 - ‖z‖²)/(1 + conj z ζ)²` near `0`, so that

* `(f ∘ φ)''(0) = f''(z) (1-‖z‖²)² + f'(z) (1-‖z‖²) (-2 conj z)`,
* and dividing by `(1-‖z‖²) f'(z)` gives the stated formula.

All the ingredients are computed here: `deriv_div_sq_aux` (the derivative at `0` of
`ζ ↦ c/(1+aζ)²`), `deriv_first_order` (`φ'(0)`) and `deriv_second_order` (`φ''(0)`, recorded for
reference; the route below uses the product rule instead).
-/

namespace Work.Repel

open scoped ComplexConjugate Topology
open Metric Filter

noncomputable section

/-- `1 - conj z * z` is the complex number `1 - ‖z‖²`. -/
private lemma one_sub_conj_mul_self (z : ℂ) : (1 : ℂ) - conj z * z = ((1 - ‖z‖^2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self (z := z), Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- The derivative at `0` of `ζ ↦ c / (1 + a ζ)²` is `-2 a c`. -/
private lemma deriv_div_sq_aux (c a : ℂ) :
    HasDerivAt (fun t : ℂ => c / (1 + a * t) ^ 2) (c * (-(2 * a))) 0 := by
  have h1 : HasDerivAt (fun t : ℂ => 1 + a * t) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul a).const_add 1
  have h2 : HasDerivAt (fun t : ℂ => (1 + a * t) ^ 2) (2 * (1 + a * 0) ^ (2 - 1) * a) 0 :=
    h1.pow 2
  have h3 : HasDerivAt (fun t : ℂ => ((1 + a * t) ^ 2)⁻¹)
      (-(2 * (1 + a * 0) ^ (2 - 1) * a) / ((1 + a * 0) ^ 2) ^ 2) 0 :=
    h2.inv (by simp)
  have h4 := h3.const_mul c
  convert h4 using 1
  · ext t; simp [div_eq_mul_inv]
  · simp only [mul_zero, add_zero, one_pow]; ring

/-- `φ'(0) = 1 - ‖z‖²` for the disc automorphism `φ ζ = (ζ + z)/(1 + conj z * ζ)`. -/
private lemma deriv_first_order (z : ℂ) :
    deriv (fun ζ : ℂ => (ζ + z) / (1 + conj z * ζ)) 0 = ((1 - ‖z‖^2 : ℝ) : ℂ) := by
  have hnum : HasDerivAt (fun ζ : ℂ => ζ + z) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).add_const z
  have hden : HasDerivAt (fun ζ : ℂ => 1 + conj z * ζ) (conj z) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (conj z)).const_add 1
  have hd : deriv (fun ζ : ℂ => (ζ + z) / (1 + conj z * ζ)) 0
      = (1 * (1 + conj z * 0) - (0 + z) * conj z) / (1 + conj z * 0) ^ 2 :=
    hnum.div hden (by simp) |>.deriv
  rw [hd]
  simp only [mul_zero, add_zero, one_pow, mul_one, zero_add, div_one]
  rw [show (1 : ℂ) - z * conj z = 1 - conj z * z by ring, one_sub_conj_mul_self]

/-- `φ''(0) = -2 * conj z * (1 - ‖z‖²)` for the disc automorphism
`φ ζ = (ζ + z)/(1 + conj z * ζ)`. -/
private lemma deriv_second_order (z : ℂ) :
    deriv (deriv (fun ζ : ℂ => (ζ + z) / (1 + conj z * ζ))) 0
      = -2 * conj z * ((1 - ‖z‖^2 : ℝ) : ℂ) := by
  have hne : ∀ᶠ ζ in 𝓝 (0 : ℂ), 1 + conj z * ζ ≠ 0 := by
    have hcont : Continuous fun ζ : ℂ => 1 + conj z * ζ :=
      continuous_const.add (continuous_const.mul continuous_id)
    exact (hcont.tendsto 0).eventually_ne (by simp)
  have hφ : deriv (fun ζ : ℂ => (ζ + z) / (1 + conj z * ζ))
      =ᶠ[𝓝 0] fun ζ => ((1 - ‖z‖^2 : ℝ) : ℂ) / (1 + conj z * ζ) ^ 2 := by
    filter_upwards [hne] with ζ hζ
    have hnum : HasDerivAt (fun ζ : ℂ => ζ + z) 1 ζ := by
      simpa using (hasDerivAt_id ζ).add_const z
    have hden : HasDerivAt (fun ζ : ℂ => 1 + conj z * ζ) (conj z) ζ := by
      simpa using ((hasDerivAt_id ζ).const_mul (conj z)).const_add 1
    have hd : deriv (fun w : ℂ => (w + z) / (1 + conj z * w)) ζ
        = (1 * (1 + conj z * ζ) - (ζ + z) * conj z) / (1 + conj z * ζ) ^ 2 :=
      hnum.div hden hζ |>.deriv
    rw [hd]
    rw [show (1 * (1 + conj z * ζ) - (ζ + z) * conj z) = 1 - conj z * z by ring]
    rw [one_sub_conj_mul_self]
  rw [hφ.deriv_eq]
  rw [(deriv_div_sq_aux ((1 - ‖z‖^2 : ℝ) : ℂ) (conj z)).deriv]
  ring

/-- **The second derivative of the Koebe transform.**  For `f` holomorphic on the unit disc
and `z` in the disc with `deriv f z ≠ 0`,
`(koebeT f z)''(0) = (1 - ‖z‖²) * f''(z)/f'(z) - 2 * conj z`. -/
theorem koebeT_iteratedDeriv_two {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1)
    (han : ∀ w ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f w) (hfd : deriv f z ≠ 0) :
    iteratedDeriv 2 (Work.Motion.koebeT f z) 0
      = (1 - ‖z‖ ^ 2) * deriv (deriv f) z / deriv f z - 2 * conj z := by
  have hCne : ((1 - ‖z‖^2 : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < 1 - ‖z‖^2 := by nlinarith [norm_nonneg z, mem_ball_zero_iff.mp hz]
    exact_mod_cast hpos.ne'
  -- the disc automorphism `φ ζ = (ζ + z)/(1 + conj z * ζ)`
  set φ : ℂ → ℂ := fun w => (w + z) / (1 + conj z * w) with hφdef
  have hφ0 : φ 0 = z := by rw [hφdef]; simp
  have hφd0 : deriv φ 0 = ((1 - ‖z‖^2 : ℝ) : ℂ) := by
    rw [hφdef]; exact deriv_first_order z
  -- the denominator `1 + conj z * ζ` is nonzero near `0`
  have hne : ∀ᶠ w in 𝓝 (0 : ℂ), 1 + conj z * w ≠ 0 := by
    have hcont : Continuous fun w : ℂ => 1 + conj z * w :=
      continuous_const.add (continuous_const.mul continuous_id)
    exact (hcont.tendsto 0).eventually_ne (by simp)
  have hφdiffAt : ∀ w : ℂ, 1 + conj z * w ≠ 0 → DifferentiableAt ℂ φ w := by
    intro w hw
    rw [hφdef]
    exact (differentiableAt_id.add_const z).div
      ((differentiableAt_const (1 : ℂ)).add
        ((differentiableAt_const (conj z)).mul differentiableAt_id)) hw
  -- `φ` maps a neighbourhood of `0` into the unit disc
  have hmem : ∀ᶠ w in 𝓝 (0 : ℂ), φ w ∈ Metric.ball (0 : ℂ) 1 := by
    have hcont : ContinuousAt φ 0 := by
      rw [hφdef]
      exact (continuousAt_id.add continuousAt_const).div
        (continuousAt_const.add (continuousAt_const.mul continuousAt_id)) (by simp)
    have ht : Tendsto φ (𝓝 0) (𝓝 z) := by
      rw [← hφ0]; exact hcont
    exact ht.eventually (isOpen_ball.mem_nhds hz)
  -- the Koebe transform, as an explicit quotient
  have hkdef : Work.Motion.koebeT f z
      = fun ζ => (f (φ ζ) - f z) / (((1 - ‖z‖^2 : ℝ) : ℂ) * deriv f z) := by
    rw [hφdef]; rfl
  -- chain rule near `0`
  have hF : deriv (fun w => f (φ w)) =ᶠ[𝓝 (0 : ℂ)] fun w => deriv f (φ w) * deriv φ w := by
    filter_upwards [hmem, hne] with w hwmem hwne
    exact deriv_comp w ((han (φ w) hwmem).differentiableAt) (hφdiffAt w hwne)
  -- the explicit first derivative of `φ` near `0`
  have hφderiv : deriv φ =ᶠ[𝓝 (0 : ℂ)]
      fun w => ((1 - ‖z‖^2 : ℝ) : ℂ) / (1 + conj z * w) ^ 2 := by
    filter_upwards [hne] with w hwne
    rw [hφdef]
    have hnum : HasDerivAt (fun ζ : ℂ => ζ + z) 1 w := by
      simpa using (hasDerivAt_id w).add_const z
    have hden : HasDerivAt (fun ζ : ℂ => 1 + conj z * ζ) (conj z) w := by
      simpa using ((hasDerivAt_id w).const_mul (conj z)).const_add 1
    have hd : deriv (fun ζ : ℂ => (ζ + z) / (1 + conj z * ζ)) w
        = (1 * (1 + conj z * w) - (w + z) * conj z) / (1 + conj z * w) ^ 2 :=
      hnum.div hden hwne |>.deriv
    rw [hd]
    rw [show (1 * (1 + conj z * w) - (w + z) * conj z) = 1 - conj z * z by ring]
    rw [one_sub_conj_mul_self]
  have hφdiff0 : DifferentiableAt ℂ φ 0 := hφdiffAt 0 (by simp)
  have hda : DifferentiableAt ℂ (deriv f) (φ 0) := by
    simpa [hφ0] using (han z hz).deriv.differentiableAt
  have hdu : deriv (fun w => deriv f (φ w)) 0
      = deriv (deriv f) z * ((1 - ‖z‖^2 : ℝ) : ℂ) := by
    have hcomp : deriv ((deriv f) ∘ φ) 0 = deriv (deriv f) (φ 0) * deriv φ 0 :=
      deriv_comp (x := (0 : ℂ)) (h := φ) (h₂ := deriv f) hda hφdiff0
    show deriv ((deriv f) ∘ φ) 0 = deriv (deriv f) z * ((1 - ‖z‖^2 : ℝ) : ℂ)
    rw [hcomp, hφ0, hφd0]
  have hdv : deriv (fun w => ((1 - ‖z‖^2 : ℝ) : ℂ) / (1 + conj z * w) ^ 2) 0
      = ((1 - ‖z‖^2 : ℝ) : ℂ) * (-(2 * conj z)) :=
    (deriv_div_sq_aux ((1 - ‖z‖^2 : ℝ) : ℂ) (conj z)).deriv
  have hu : DifferentiableAt ℂ (fun w => deriv f (φ w)) 0 := by
    show DifferentiableAt ℂ ((deriv f) ∘ φ) 0
    exact hda.comp 0 hφdiff0
  have hv : DifferentiableAt ℂ (fun w => ((1 - ‖z‖^2 : ℝ) : ℂ) / (1 + conj z * w) ^ 2) 0 :=
    (deriv_div_sq_aux ((1 - ‖z‖^2 : ℝ) : ℂ) (conj z)).differentiableAt
  -- first derivative of the Koebe transform
  have hk1 : deriv (Work.Motion.koebeT f z)
      = fun ζ => deriv (fun w => f (φ w)) ζ / (((1 - ‖z‖^2 : ℝ) : ℂ) * deriv f z) := by
    funext ζ
    rw [hkdef, deriv_div_const, deriv_sub_const]
  have hk2 : deriv (deriv (Work.Motion.koebeT f z)) 0
      = deriv (deriv (fun w => f (φ w))) 0 / (((1 - ‖z‖^2 : ℝ) : ℂ) * deriv f z) := by
    rw [hk1, deriv_div_const]
  -- second derivative of `f ∘ φ` at `0`
  have hmain : deriv (deriv (fun w => f (φ w))) 0
      = deriv (deriv f) z * ((1 - ‖z‖^2 : ℝ) : ℂ) * ((1 - ‖z‖^2 : ℝ) : ℂ)
        + deriv f z * (((1 - ‖z‖^2 : ℝ) : ℂ) * (-(2 * conj z))) := by
    have h1 : deriv (deriv (fun w => f (φ w))) 0
        = deriv (fun w => deriv f (φ w) * deriv φ w) 0 := hF.deriv_eq
    have h2 : deriv (fun w => deriv f (φ w) * deriv φ w) 0
        = deriv (fun w => deriv f (φ w) *
            (((1 - ‖z‖^2 : ℝ) : ℂ) / (1 + conj z * w) ^ 2)) 0 := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hφderiv] with w hw
      rw [hw]
    rw [h1, h2]
    rw [show (fun w => deriv f (φ w) * (((1 - ‖z‖^2 : ℝ) : ℂ) / (1 + conj z * w) ^ 2))
          = (fun w => deriv f (φ w)) *
            (fun w => ((1 - ‖z‖^2 : ℝ) : ℂ) / (1 + conj z * w) ^ 2) from rfl,
        deriv_mul hu hv, hdu, hdv]
    simp only [mul_zero, add_zero, one_pow, div_one, hφ0]
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hk2, hmain]
  field_simp
  push_cast
  ring

end

end Work.Repel

/-! ### Compatibility alias

The scaffold of this file placed the theorem inside a *doubled* `namespace Work.Repel`, so that
the declaration was named `Work.Repel.Work.Repel.koebeT_iteratedDeriv_two`.  The declaration
requested (and the one every colleague on this area uses, e.g.
`Submission/Work/Repel/deriv_lower.lean`) is `Work.Repel.koebeT_iteratedDeriv_two`, which is the
main declaration above.  The identical statement is kept available under the old, doubled name as
well, so that nothing that referred to the scaffolded name breaks. -/

namespace Work.Repel.Work.Repel

open scoped ComplexConjugate

set_option linter.dupNamespace false in
theorem koebeT_iteratedDeriv_two {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1)
    (han : ∀ w ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f w) (hfd : deriv f z ≠ 0) :
    iteratedDeriv 2 (Work.Motion.koebeT f z) 0
      = (1 - ‖z‖ ^ 2) * deriv (deriv f) z / deriv f z - 2 * conj z :=
  _root_.Work.Repel.koebeT_iteratedDeriv_two hz han hfd

end Work.Repel.Work.Repel
