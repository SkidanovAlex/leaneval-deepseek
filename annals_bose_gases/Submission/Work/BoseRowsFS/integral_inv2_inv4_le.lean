import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.RadialIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.integral_inv2_inv4_le`

The elementary bound

    `∫_{ℝ³} (‖p‖²)⁻¹ (1 + ‖p‖)⁻⁴ dp ≤ 100`.

The integrand is radial, so the polar-coordinate identity of
`Submission.BoseGases.integral_fun_norm_r3` reduces the integral to

    `4π ∫_0^∞ r² · (r²)⁻¹ (1 + r)⁻⁴ dr = 4π ∫_0^∞ (1 + r)⁻⁴ dr`,

and the last integral is `1/3` (antiderivative `-(1/3)(1+r)⁻³`, vanishing at `+∞`).
Hence the value is `4π/3 ≤ 100`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real Topology

namespace Work.BoseRowsFS

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The one-dimensional radial integral `∫_0^∞ (1 + r)^{-4} dr = 1/3`, computed from the
antiderivative `r ↦ -(1/3) (1 + r)^{-3}` by the fundamental theorem of calculus on `(0,∞)`
(`integral_Ioi_of_hasDerivAt_of_tendsto'`), with integrability supplied by
`integrableOn_add_rpow_Ioi_of_lt`. -/
lemma integral_Ioi_one_add_pow_four_inv :
    (∫ r in Set.Ioi (0 : ℝ), ((1 + r) ^ 4)⁻¹) = 1 / 3 := by
  -- replace the natural power by the real power, so that the rpow FTC lemmas apply
  have hrpow : (∫ r in Set.Ioi (0 : ℝ), ((1 + r) ^ 4)⁻¹)
      = ∫ r in Set.Ioi (0 : ℝ), (1 + r) ^ (-4 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro r hr
    have hpos : 0 ≤ 1 + r := by
      have hr' : (0 : ℝ) < r := hr
      linarith
    have h4 : (1 + r) ^ (4 : ℝ) = (1 + r) ^ 4 := by
      simpa using Real.rpow_natCast (1 + r) 4
    change ((1 + r) ^ 4)⁻¹ = (1 + r) ^ (-4 : ℝ)
    rw [← h4, ← Real.rpow_neg hpos (4 : ℝ)]
  rw [hrpow]
  -- the antiderivative `-(1/3) * (1 + r)^{-3}` and its derivative `(1 + r)^{-4}`
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun r : ℝ => -(1 / 3) * (1 + r) ^ (-3 : ℝ)) ((1 + x) ^ (-4 : ℝ)) x := by
    intro x hx
    have hx' : (0 : ℝ) ≤ x := hx
    have hx0 : 1 + x ≠ 0 := by linarith
    have hbase : HasDerivAt (fun r : ℝ => (1 + r)) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have h1 : HasDerivAt (fun r : ℝ => (1 + r) ^ (-3 : ℝ))
        ((-3 : ℝ) * (1 + x) ^ (-4 : ℝ)) x := by
      have hh := hbase.rpow_const (p := (-3 : ℝ)) (Or.inl hx0)
      simpa [show (-3 : ℝ) - 1 = (-4 : ℝ) by norm_num, one_mul] using hh
    have h3 := h1.const_mul (-(1 / 3))
    have key : (-(1 / 3) : ℝ) * ((-3 : ℝ) * (1 + x) ^ (-4 : ℝ)) = (1 + x) ^ (-4 : ℝ) := by
      ring
    rw [key] at h3
    exact h3
  -- integrability of the integrand on `(0,∞)`
  have hint : IntegrableOn (fun r : ℝ => (1 + r) ^ (-4 : ℝ)) (Set.Ioi (0 : ℝ)) := by
    have hh := integrableOn_add_rpow_Ioi_of_lt (a := (-4 : ℝ)) (c := (0 : ℝ)) (m := (1 : ℝ))
      (by norm_num) (by norm_num)
    simpa [add_comm] using hh
  -- the antiderivative tends to `0` at `+∞`
  have htend : Tendsto (fun r : ℝ => (1 + r) ^ (-3 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := (3 : ℝ)) (by norm_num)).comp
      (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
  have hf : Tendsto (fun r : ℝ => -(1 / 3) * (1 + r) ^ (-3 : ℝ)) atTop (𝓝 0) := by
    have h := htend.const_mul (-(1 / 3))
    rw [mul_zero] at h
    exact h
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ)) hderiv hint hf
  rw [hftc]
  norm_num

theorem integral_inv2_inv4_le :
    (∫ p : EuclideanSpace ℝ (Fin 3), (‖p‖ ^ 2)⁻¹ * ((1 + ‖p‖) ^ 4)⁻¹) ≤ 100 := by
  let g : ℝ → ℝ := fun r => (r ^ 2)⁻¹ * ((1 + r) ^ 4)⁻¹
  -- the radial profile of the integrand: `r ^ 2 * g r = (1 + r)^{-4}` for `r > 0`
  have hstep : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r)
      = (∫ r in Set.Ioi (0 : ℝ), ((1 + r) ^ 4)⁻¹) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    have h2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr0
    change r ^ 2 * ((r ^ 2)⁻¹ * ((1 + r) ^ 4)⁻¹) = ((1 + r) ^ 4)⁻¹
    rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]
  have hmain : (∫ p : EuclideanSpace ℝ (Fin 3), (‖p‖ ^ 2)⁻¹ * ((1 + ‖p‖) ^ 4)⁻¹)
      = 4 * π * (∫ r in Set.Ioi (0 : ℝ), ((1 + r) ^ 4)⁻¹) := by
    calc (∫ p : EuclideanSpace ℝ (Fin 3), (‖p‖ ^ 2)⁻¹ * ((1 + ‖p‖) ^ 4)⁻¹)
        = ∫ p : EuclideanSpace ℝ (Fin 3), g ‖p‖ := rfl
      _ = 4 * π * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) :=
            Submission.BoseGases.integral_fun_norm_r3 (g := g)
      _ = 4 * π * (∫ r in Set.Ioi (0 : ℝ), ((1 + r) ^ 4)⁻¹) := by rw [hstep]
  rw [hmain, integral_Ioi_one_add_pow_four_inv]
  nlinarith [Real.pi_le_four]

end Work.BoseRowsFS
