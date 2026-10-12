import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseB6Est.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — integrability of the mass-integrand `β(t)²/(2t²)`

`Work.BoseB6Est.integrableBetaDiv` is the integrability statement behind FS's
mass integral `I₂ = ∫ β(t)²/(2t²)dt` (`eq:I2-integral`): the function

  `t ↦ β(‖t‖)²/(2‖t‖²)`

is Lebesgue integrable on `Fin 3 → ℝ`.

The mathematical content is entirely in the radial reduction: in polar
coordinates on `ℝ³` the Jacobian `4πr²` cancels the `r⁻²` of the integrand, so
the integrability of the radial function `t ↦ β(‖t‖)²/(2‖t‖²)` is equivalent to
the integrability of `r ↦ r² · β(r)²/(2r²) = β(r)²/2` on `(0,∞)`.  The latter
holds because `β` is measurable, bounded by `K.B` (`FsKernel.bound`) and
supported in `[0, K.T]` (`FsKernel.support`): `β²/2` vanishes beyond the
cutoff, and on the finite-measure interval `(0, K.T]` it is bounded by
`K.B²/2`.

The corpus's radial integration formula
`Work.BoseBox.integrable_eucNorm3_fun_iff` performs the reduction, and the
one-dimensional integrability is the same `Ioc`/`Ioi` split already used for
`Work.BoseB6Est.fsI2_le_bound`.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseB6Est.Zero

/-- **The one-dimensional form of `I₂`-integrability.**  After the radial
Jacobian `r²` is reattached, the integrand is `β(r)²/2`, which is measurable,
bounded and supported in `[0, K.T]`, hence integrable on `(0, ∞)`. -/
lemma integrableOn_r2_beta_div (K : Work.BoseB6Est.FsKernel) :
    MeasureTheory.IntegrableOn
      (fun r : ℝ => r ^ 2 * ((K.β r) ^ 2 / (2 * r ^ 2))) (Set.Ioi (0 : ℝ)) := by
  have hmeas : Measurable (fun r : ℝ => r ^ 2 * ((K.β r) ^ 2 / (2 * r ^ 2))) :=
    (measurable_id.pow_const 2).mul
      ((K.meas.pow_const 2).div (measurable_const.mul (measurable_id.pow_const 2)))
  -- On `(0, K.T]` the function is `β²/2`, hence bounded by `K.B²/2`.
  have h1 : IntegrableOn (fun r : ℝ => r ^ 2 * ((K.β r) ^ 2 / (2 * r ^ 2)))
      (Set.Ioc 0 K.T) := by
    refine IntegrableOn.of_bound (μ := volume) (s := Set.Ioc 0 K.T)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) ?_ (K.B ^ 2 / 2) ?_
    · exact hmeas.aestronglyMeasurable.restrict
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun r hr => ?_)
      have hr0 : 0 < r := hr.1
      have hval : r ^ 2 * ((K.β r) ^ 2 / (2 * r ^ 2)) = (K.β r) ^ 2 / 2 := by
        field_simp
      rw [Real.norm_eq_abs, hval, abs_of_nonneg (by positivity)]
      have h2 := pow_le_pow_left₀ (K.nonneg r) (K.bound r) 2
      linarith
  -- Beyond the cutoff the function vanishes identically.
  have h2 : IntegrableOn (fun r : ℝ => r ^ 2 * ((K.β r) ^ 2 / (2 * r ^ 2)))
      (Set.Ioi K.T) := by
    refine (MeasureTheory.integrableOn_congr_fun
      (f := fun _ : ℝ => (0 : ℝ))
      (g := fun r : ℝ => r ^ 2 * ((K.β r) ^ 2 / (2 * r ^ 2)))
      (fun r hr => ?_) measurableSet_Ioi).mp MeasureTheory.integrableOn_zero
    show (0 : ℝ) = r ^ 2 * ((K.β r) ^ 2 / (2 * r ^ 2))
    rw [K.support r (Set.mem_Ioi.mp hr)]
    simp
  have hun := h1.union h2
  rwa [show Set.Ioc (0 : ℝ) K.T ∪ Set.Ioi K.T = Set.Ioi 0 from ?_] at hun
  ext r
  constructor
  · intro h
    rcases h with h | h
    · exact h.1
    · exact lt_of_le_of_lt K.Tnn h
  · intro hr
    by_cases hle : r ≤ K.T
    · exact Or.inl ⟨hr, hle⟩
    · exact Or.inr (not_le.mp hle)

/-- **The mass integrand `β(t)²/(2t²)` is integrable on `ℝ³`** — the
integrability half of FS's `eq:I2-integral` estimate
(`Work.BoseB6Est.fsI2_le_bound`). -/
theorem integrableBetaDiv (K : Work.BoseB6Est.FsKernel) :
    MeasureTheory.Integrable
      (fun t : Fin 3 → ℝ =>
        (K.β (Submission.BoseGases.eucNorm3 t)) ^ 2 / (2 * (Submission.BoseGases.eucNorm3 t) ^ 2)) := by
  rw [Work.BoseBox.integrable_eucNorm3_fun_iff (g := fun r : ℝ => (K.β r) ^ 2 / (2 * r ^ 2))]
  exact integrableOn_r2_beta_div K

end Work.BoseB6Est.Zero
