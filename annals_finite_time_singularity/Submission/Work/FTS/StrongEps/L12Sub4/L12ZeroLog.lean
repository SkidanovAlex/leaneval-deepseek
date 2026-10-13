import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Submission.Work.FTS.StrongEps.L12Sub4.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongEps.L12Sub4

/-- **`L₁₂(h)(0)` in log coordinates.**  With `Glw ζ = κ(ζ) K(arctan (e^ζ))` the angular weight of
`L₁₂(·)(0)` in the log coordinate `ζ = log tan θ` (`κ = (arctan ∘ exp)'`, so that
`K(θ) dθ = Glw(ζ) dζ`),

  `L₁₂(h)(0) = ∫_s ∫_ζ Glw ζ · h (e^s) (arctan (e^ζ)) ds dζ`.

This is an **unconditional** identity of Bochner integrals (no integrability hypothesis): each step is
a change of variables which is valid as an identity of Bochner integrals even in the junk cases.

Hints: unfold `L12 = FM.L12 K` (`L12_zero_eq_double`, in `Defs`), replace `Iθ` by `Ioo 0 (π/2)`
(`setIntegral_congr_set` + `MeasureTheory.Ioo_ae_eq_Icc`), pull the factor `1/r` out of the angular
integral (`integral_const_mul`), apply the angular substitution
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` with `f = arctan ∘ exp`, `f' = κ` on
`Set.univ` (whose image is `Ioo 0 (π/2)` by `HkSqAux.range_arctan_exp`), then the radial substitution
with `f = f' = Real.exp` on `Set.univ` (`Real.range_exp`). -/
theorem L12ZeroLog (h : ℝ → ℝ → ℝ) :
    Work.Construction.L12 h 0
      = ∫ s, ∫ ζ, Glw ζ * h (Real.exp s) (Real.arctan (Real.exp ζ)) := by
  rw [L12_zero_eq_double]
  -- Angular substitution `θ = arctan (e^ζ)`: `K(θ) dθ = Glw(ζ) dζ`.
  have angular : ∀ z : ℝ, (∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.K θ * h z θ)
      = ∫ ζ, Glw ζ * h z (Real.arctan (Real.exp ζ)) := by
    intro z
    have hinj : InjOn (fun ζ : ℝ => Real.arctan (Real.exp ζ)) Set.univ := by
      intro a _ b _ hh
      exact Real.exp_injective (Real.arctan_injective hh)
    have hderiv : ∀ ζ ∈ (Set.univ : Set ℝ),
        HasDerivWithinAt (fun ζ' : ℝ => Real.arctan (Real.exp ζ')) (HkSqAux.kappa ζ)
          Set.univ ζ := by
      intro ζ _
      have hd : HasDerivAt (fun ζ' : ℝ => Real.arctan (Real.exp ζ'))
          (1 / (1 + (Real.exp ζ) ^ 2) * Real.exp ζ) ζ := (Real.hasDerivAt_exp ζ).arctan
      have hκ : (1 / (1 + (Real.exp ζ) ^ 2) * Real.exp ζ) = HkSqAux.kappa ζ := by
        rw [HkSqAux.kappa]
        have h2 : Real.exp (2 * ζ) = (Real.exp ζ) ^ 2 := by rw [two_mul, Real.exp_add, pow_two]
        rw [h2, one_div, div_eq_mul_inv, mul_comm]
      exact (hκ ▸ hd).hasDerivWithinAt
    have hsub := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Set.univ)
      (f := fun ζ : ℝ => Real.arctan (Real.exp ζ)) (f' := HkSqAux.kappa)
      MeasurableSet.univ hderiv hinj (fun θ : ℝ => Work.Spaces.K θ * h z θ)
    rw [HkSqAux.range_arctan_exp] at hsub
    rw [setIntegral_univ] at hsub
    rw [hsub]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ζ => ?_))
    simp only []
    rw [abs_of_pos (HkSqAux.kappa_pos ζ), smul_eq_mul, Glw, mul_assoc]
  -- Replace the closed angular interval `Iθ = [0,π/2]` by the open one (null-set difference).
  have step1 : (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h z θ / z)
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.K θ * h z θ / z := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    exact setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc (a := 0) (b := π / 2)).symm
  rw [step1]
  -- Pull the factor `1/z` out of the angular integral and substitute `θ = arctan (e^ζ)`.
  have step2 : (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.K θ * h z θ / z)
      = ∫ z in Set.Ioi 0, (1 / z) * ∫ ζ, Glw ζ * h z (Real.arctan (Real.exp ζ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    calc ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.K θ * h z θ / z
        = ∫ θ in Set.Ioo 0 (π / 2), (1 / z) * (Work.Spaces.K θ * h z θ) := by
          refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring)
      _ = (1 / z) * ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.K θ * h z θ := by
          rw [MeasureTheory.integral_const_mul]
      _ = (1 / z) * ∫ ζ, Glw ζ * h z (Real.arctan (Real.exp ζ)) := by rw [angular z]
  rw [step2]
  -- Radial substitution `z = e^s`: `dz/z = ds`.
  have step3 : (∫ z in Set.Ioi 0, (1 / z) * ∫ ζ, Glw ζ * h z (Real.arctan (Real.exp ζ)))
      = ∫ s, ∫ ζ, Glw ζ * h (Real.exp s) (Real.arctan (Real.exp ζ)) := by
    have hsub := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Set.univ)
      (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (Real.exp_injective.injOn)
      (fun z => (1 / z) * ∫ ζ, Glw ζ * h z (Real.arctan (Real.exp ζ)))
    rw [HkSqAux.range_exp] at hsub
    rw [setIntegral_univ] at hsub
    rw [hsub]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    simp only []
    rw [abs_of_pos (Real.exp_pos s), smul_eq_mul, one_div, ← mul_assoc,
      mul_inv_cancel₀ (Real.exp_ne_zero s), one_mul]
  rw [step3]

end Work.FTS.StrongEps.L12Sub4
