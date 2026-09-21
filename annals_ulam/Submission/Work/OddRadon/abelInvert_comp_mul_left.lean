import Mathlib
import Submission.Work.OddRadon.Abel

/-!
# The scaling law for the classical Abel inversion (`Work.OddRadon`)

For `b > 0` the classical Abel inversion `abelInvert` satisfies

  `abelInvert (fun y => Ψ (b * y)) (u / b) = abelInvert Ψ u`,

i.e. it commutes with the rescaling of the argument of the datum by the factor `b`
(pulled back along `u ↦ u / b`).  This is the second half of the scaling law for the
Radon inversion `radonInverse` of the odd-dimensional case (`radonInverse_comp_mul_left`),
the first half being the scaling of the iterated exponent reduction
(`abelReduceIter_comp_mul_left`).

The proof is the change of variable `c = t / b` in the inner interval integral of
`abelInvert`:

  `∫_0^v c Ψ (b c) / √(v² - c²) dc = b⁻¹ ∫_0^{bv} c Ψ c / √((bv)² - c²) dc   (∀ v)`,

which exhibits the defining integral of `abelInvert (Ψ ∘ (b ·))` as
`v ↦ b⁻¹ * B (b v)`, where `B` is the defining integral of `abelInvert Ψ`; the derivative
of that composite is computed by `deriv_comp_mul_left`.

## Main results

* `sqrt_scale_mul_left`, `div_sqrt_scale_mul_left`, `mul_div_sqrt_scale_mul_left` — the
  elementary identity `√(v² - (t/b)²) * b = √((bv)² - t²)`, which is what makes the
  substitution in the singular Abel kernel work;
* `abelInvert_integral_comp_mul_left` — scaling of the inner integral (above);
* `abelInvert_comp_mul_left` — the scaling law for `abelInvert`.
-/

noncomputable section

open MeasureTheory
open scoped Interval

namespace Work.OddRadon

/-- **Scaling of the singular Abel kernel.**  For `b > 0` the factors `√(v² - (t/b)²)` and
`√((b v)² - t²)` differ exactly by `b`.  No hypothesis on the sign of the radicands is
needed: on the negative side both square roots vanish. -/
lemma sqrt_scale_mul_left {b v t : ℝ} (hb : 0 < b) :
    Real.sqrt (v ^ 2 - (t / b) ^ 2) * b = Real.sqrt ((b * v) ^ 2 - t ^ 2) := by
  have hbsq : Real.sqrt (b ^ 2) = b := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hb]
  calc Real.sqrt (v ^ 2 - (t / b) ^ 2) * b
      = Real.sqrt (v ^ 2 - (t / b) ^ 2) * Real.sqrt (b ^ 2) := by rw [hbsq]
    _ = Real.sqrt ((v ^ 2 - (t / b) ^ 2) * b ^ 2) := by
        rw [mul_comm (Real.sqrt (v ^ 2 - (t / b) ^ 2)) (Real.sqrt (b ^ 2)),
          ← Real.sqrt_mul (sq_nonneg b) (v ^ 2 - (t / b) ^ 2), mul_comm (b ^ 2)]
    _ = Real.sqrt ((b * v) ^ 2 - t ^ 2) := by
        congr 1
        field_simp

/-- Pointwise form of `sqrt_scale_mul_left`: the quotient by the scaled square root is the
quotient by the unscaled one. -/
lemma div_sqrt_scale_mul_left {b v t : ℝ} (hb : 0 < b) :
    (t / b) / Real.sqrt (v ^ 2 - (t / b) ^ 2) = t / Real.sqrt ((b * v) ^ 2 - t ^ 2) := by
  have hs := sqrt_scale_mul_left (b := b) (v := v) (t := t) hb
  rw [div_div, mul_comm b (Real.sqrt _), hs]

/-- Pointwise equality of the Abel kernels under the substitution `c = t / b`. -/
lemma mul_div_sqrt_scale_mul_left {b v t : ℝ} (hb : 0 < b) (Ψ : ℝ → ℝ) :
    (t / b) * Ψ t / Real.sqrt (v ^ 2 - (t / b) ^ 2)
      = t * Ψ t / Real.sqrt ((b * v) ^ 2 - t ^ 2) := by
  rw [show (t / b) * Ψ t / Real.sqrt (v ^ 2 - (t / b) ^ 2)
      = ((t / b) / Real.sqrt (v ^ 2 - (t / b) ^ 2)) * Ψ t by ring,
    div_sqrt_scale_mul_left (b := b) (v := v) (t := t) hb]
  ring

/-- **Scaling of the inner integral of `abelInvert`.**  For `b > 0` and every `v`,
the substitution `c = t / b` in `∫_0^v c Ψ (b c) / √(v² - c²) dc` gives
`b⁻¹ ∫_0^{bv} c Ψ c / √((bv)² - c²) dc`. -/
lemma abelInvert_integral_comp_mul_left {Ψ : ℝ → ℝ} {b : ℝ} (hb : 0 < b) (v : ℝ) :
    (∫ c in (0:ℝ)..v, c * Ψ (b * c) / Real.sqrt (v ^ 2 - c ^ 2))
      = b⁻¹ * ∫ c in (0:ℝ)..(b * v), c * Ψ c / Real.sqrt ((b * v) ^ 2 - c ^ 2) := by
  have hbne : b ≠ 0 := ne_of_gt hb
  -- rewrite the integrand as `f (b * c)` for `f t = (t/b) Ψ t / √(v² - (t/b)²)`
  have hL : (∫ c in (0:ℝ)..v, c * Ψ (b * c) / Real.sqrt (v ^ 2 - c ^ 2))
      = ∫ x in (0:ℝ)..v, (b * x / b) * Ψ (b * x) / Real.sqrt (v ^ 2 - (b * x / b) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only
    rw [mul_div_cancel_left₀ x hbne]
  have hcomp := intervalIntegral.integral_comp_mul_left
    (f := fun t : ℝ => (t / b) * Ψ t / Real.sqrt (v ^ 2 - (t / b) ^ 2))
    (a := (0:ℝ)) (b := v) (c := b) hbne
  rw [mul_zero, smul_eq_mul] at hcomp
  rw [hL, hcomp]
  -- now scale the kernel back
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only
  exact mul_div_sqrt_scale_mul_left hb Ψ

/-- **The scaling law for the classical Abel inversion.**  For `b > 0`,
`abelInvert (Ψ ∘ (b ·)) (u/b) = abelInvert Ψ u`: rescaling the datum by `b` rescales the
argument of the inversion by the same factor. -/
theorem abelInvert_comp_mul_left {Ψ : ℝ → ℝ} {b u : ℝ} (hb : 0 < b) (hu : 0 < u) :
    abelInvert (fun y : ℝ => Ψ (b * y)) (u / b) = abelInvert Ψ u := by
  have hbne : b ≠ 0 := ne_of_gt hb
  -- `B` is the inner integral defining `abelInvert Ψ`
  set B : ℝ → ℝ := fun w : ℝ => ∫ c in (0:ℝ)..w, c * Ψ c / Real.sqrt (w ^ 2 - c ^ 2) with hB
  -- the inner integral of `abelInvert (Ψ ∘ (b ·))` is `v ↦ b⁻¹ * B (b v)`
  have hfun : (fun v : ℝ => ∫ c in (0:ℝ)..v,
        c * (fun y : ℝ => Ψ (b * y)) c / Real.sqrt (v ^ 2 - c ^ 2))
      = fun v : ℝ => b⁻¹ * B (b * v) := by
    funext v
    simp only
    rw [abelInvert_integral_comp_mul_left hb v]
  have hderiv : deriv (fun v : ℝ => b⁻¹ * B (b * v)) (u / b) = deriv B u := by
    rw [deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul, mul_div_cancel₀ u hbne,
      ← mul_assoc, inv_mul_cancel₀ hbne, one_mul]
  have hR : deriv (fun u' : ℝ => ∫ c in (0:ℝ)..u', c * Ψ c / Real.sqrt (u' ^ 2 - c ^ 2)) u
      = deriv B u := by
    simp only [hB]
  simp only [abelInvert]
  rw [hfun, hderiv, hR]

end Work.OddRadon
