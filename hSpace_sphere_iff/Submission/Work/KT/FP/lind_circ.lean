import Mathlib
import Submission.Work.KT.FP.LindDefs

/-!
# `Work.KT.FP.lind_circ` — the pencil projection reads off the `z⁻¹`-block

Let `R` be a complex Banach algebra and `pProj A B ρ = (2πi)⁻¹ ∮_{|z|=ρ} (z•A + B)⁻¹ A dz` the
"inside" spectral projection of the pencil `z ↦ z•A + B`.  If on the circle `|z| = ρ` the
resolvent-integrand has the Laurent expansion

  `(z•A + B)⁻¹ A = z⁻¹ • C + z⁻² • D + E`

(three *constant* coefficients, with the expansion valid pointwise on the whole circle), then the
contour integral singles out the `z⁻¹`-coefficient:

  `pProj A B ρ = C`.

This is the formal heart of `Work.KT.FP.lind_linear`/`lind_cls`: for the `3 × 3` block
linearisation of the pencil `(1 - P) + z·P` the block identity `lind_block_identity` exhibits such
an expansion with `C = diag(1, P, 0)`, `D` the `(0,1)`-block and `E` the `(2,1)`-block, so the
projection of the linearisation is exactly `diag(1, P, 0)` — the block form of the projection of
`(1 - P) + z·P`.

The mathematics is three evaluations of contour integrals of monomials, none of which needs any
hypothesis beyond `ρ > 0`:

* `∮_{|z|=ρ} z⁻¹ dz = 2πi` (`circleIntegral.integral_sub_center_inv`),
* `∮_{|z|=ρ} z⁻² dz = 0` (the Cauchy theorem for `(z - 0)ⁿ`, `n = -2 ≠ -1`,
  `circleIntegral.integral_sub_zpow_of_ne`),
* `∮_{|z|=ρ} 1 dz = 0` (`z ↦ z•a` is a primitive of the constant `a`).

The bookkeeping is: rewrite the integrand on the circle using the hypothesis
(`circleIntegral.integral_congr`), split the integral additively
(`circleIntegral.integral_add`; the three summands are continuous on the circle, hence
`CircleIntegrable`, because `z ≠ 0` there), pull the constants out
(`circleIntegral.integral_smul_const`) and evaluate.
-/

namespace Work.KT.FP

open MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

/-- `∮_{|z|=ρ} z⁻¹ dz = 2πi` for `ρ ≠ 0`. -/
lemma circ_inv_eq (ρ : ℝ) (hρ : ρ ≠ 0) :
    (∮ z in C(0, ρ), z⁻¹) = (2 * Real.pi * Complex.I : ℂ) := by
  simpa using circleIntegral.integral_sub_center_inv (0 : ℂ) (R := ρ) hρ

/-- `∮_{|z|=ρ} a dz = 0`: `z ↦ z • a` is a primitive of the constant function `a`. -/
lemma circ_const_eq (a : R) (c : ℂ) (ρ : ℝ) : (∮ _z in C(c, ρ), a) = 0 :=
  circleIntegral.integral_eq_zero_of_hasDerivWithinAt'
    (fun z _ => by simpa using ((hasDerivAt_id z).smul_const a).hasDerivWithinAt)

/-- `∮_{|z|=ρ} z⁻² dz = 0` for `ρ > 0` (the Cauchy theorem for `(z - 0)ⁿ` with `n = -2 ≠ -1`). -/
lemma circ_inv_sq_eq (ρ : ℝ) (hρ : 0 < ρ) :
    (∮ z in C(0, ρ), z⁻¹ * z⁻¹) = 0 := by
  calc (∮ z in C(0, ρ), z⁻¹ * z⁻¹)
      = (∮ z in C(0, ρ), (z - 0) ^ (-2 : ℤ)) := by
        refine circleIntegral.integral_congr hρ.le (fun z _ => ?_)
        rw [sub_zero]
        field_simp
    _ = 0 := circleIntegral.integral_sub_zpow_of_ne (by norm_num) 0 0 ρ

theorem lind_circ {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (A B C D E : R) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ z : ℂ, ‖z‖ = ρ →
      Ring.inverse (z • A + B) * A = z⁻¹ • C + (z⁻¹ * z⁻¹) • D + E) :
    Work.KT.FP.pProj A B ρ = C := by
  have h2piI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  -- on the circle, `z ≠ 0`
  have hz0 : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, z ≠ 0 := by
    intro z hz hz'
    have hzn : ‖z‖ = ρ := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    rw [hz', norm_zero] at hzn
    exact hρ.ne' hzn.symm
  have hcont : ContinuousOn (fun z : ℂ => z⁻¹) (Metric.sphere (0 : ℂ) ρ) :=
    continuousOn_id.inv₀ hz0
  -- the three summands are circle integrable
  have hf : CircleIntegrable (fun z : ℂ => z⁻¹ • C) 0 ρ :=
    (hcont.smul continuousOn_const).circleIntegrable hρ.le
  have hg : CircleIntegrable (fun z : ℂ => (z⁻¹ * z⁻¹) • D) 0 ρ :=
    ((hcont.mul hcont).smul continuousOn_const).circleIntegrable hρ.le
  have he : CircleIntegrable (fun _ : ℂ => E) 0 ρ := circleIntegrable_const E 0 ρ
  -- replace the integrand on the circle by its Laurent expansion
  have hcirc : pCirc A B ρ = (∮ z in C(0, ρ), (z⁻¹ • C + (z⁻¹ * z⁻¹) • D + E)) := by
    rw [pCirc]
    refine circleIntegral.integral_congr hρ.le (fun z hz => ?_)
    have hzn : ‖z‖ = ρ := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    exact h z hzn
  -- split the integral
  have hsplitA : (∮ z in C(0, ρ), (z⁻¹ • C + (z⁻¹ * z⁻¹) • D + E))
      = (∮ z in C(0, ρ), (z⁻¹ • C + (z⁻¹ * z⁻¹) • D)) + (∮ z in C(0, ρ), E) :=
    circleIntegral.integral_add (hf.add hg) he
  have hsplitB : (∮ z in C(0, ρ), (z⁻¹ • C + (z⁻¹ * z⁻¹) • D))
      = (∮ z in C(0, ρ), z⁻¹ • C) + (∮ z in C(0, ρ), (z⁻¹ * z⁻¹) • D) :=
    circleIntegral.integral_add hf hg
  -- evaluate the three pieces
  have h1 : (∮ z in C(0, ρ), z⁻¹ • C) = (2 * Real.pi * Complex.I) • C := by
    rw [circleIntegral.integral_smul_const, circ_inv_eq ρ hρ.ne']
  have h2 : (∮ z in C(0, ρ), (z⁻¹ * z⁻¹) • D) = 0 := by
    rw [circleIntegral.integral_smul_const, circ_inv_sq_eq ρ hρ, zero_smul]
  have h3 : (∮ z in C(0, ρ), E) = 0 := circ_const_eq E 0 ρ
  have hval : (∮ z in C(0, ρ), (z⁻¹ • C + (z⁻¹ * z⁻¹) • D + E))
      = (2 * Real.pi * Complex.I) • C := by
    rw [hsplitA, hsplitB, h1, h2, h3]
    simp
  -- `(2πi)⁻¹ • (2πi • C) = C`
  rw [pProj, hcirc, hval, smul_smul, inv_mul_cancel₀ h2piI, one_smul]

end

end Work.KT.FP
