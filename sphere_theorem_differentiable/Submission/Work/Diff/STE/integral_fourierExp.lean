import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Orthogonality of the characters on the unit cube

Layer A of the STE Fourier toolkit: `∫_{unitCube} fourierExp m = 1` if `m = 0` and `= 0` otherwise.

The proof has three independent parts, each proved below:

* `fourierExp_eq_prod`: the character `fourierExp m` is the product of its one-dimensional
  coordinate characters `x i ↦ exp (2πi mᵢ xᵢ);
* `restrict_unitCube`: Lebesgue measure restricted to `(0,1]^ι` is the product of the
  restricted one-dimensional Lebesgue measures, so Fubini in `n` variables
  (`MeasureTheory.integral_fintype_prod_eq_prod`) applies;
* `integral_exp_two_pi_I`: the one-dimensional integral `∫_0^1 exp (2πi n t) dt` is `δ_{n,0}`.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `fourierExp` is the product of the coordinate characters. -/
lemma fourierExp_eq_prod (m : ι → ℤ) (x : ι → ℝ) :
    fourierExp m x
      = ∏ i, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m i : ℂ) * (x i : ℂ))) := by
  simp only [fourierExp]
  rw [Finset.mul_sum, Complex.exp_sum]

omit [DecidableEq ι] in
/-- Lebesgue measure restricted to the unit cube is the product of the restricted
one-dimensional Lebesgue measures on `(0,1]`. -/
lemma restrict_unitCube :
    (volume : Measure (ι → ℝ)).restrict unitCube
      = Measure.pi (fun _ : ι => (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := by
  rw [unitCube, MeasureTheory.volume_pi]
  exact Measure.restrict_pi_pi (μ := fun _ : ι => (volume : Measure ℝ)) (fun _ => Set.Ioc (0 : ℝ) 1)

/-- The one-dimensional character integral: `∫_0^1 exp (2πi n t) dt = δ_{n,0}`. -/
lemma integral_exp_two_pi_I (n : ℤ) :
    (∫ t in Set.Ioc (0 : ℝ) 1,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) * (t : ℂ))))
      = if n = 0 then 1 else 0 := by
  have hcc : ∀ t : ℝ,
      2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) * (t : ℂ))
        = (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * (t : ℂ) := by
    intro t; ring
  simp_rw [hcc]
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  by_cases hn : n = 0
  · subst hn
    simp
  · have hc : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) ?_
      · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      · exact Int.cast_ne_zero.mpr hn
    rw [integral_exp_mul_complex hc]
    have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
            = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    simp [hexp, hn]

theorem integral_fourierExp {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℤ) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), Work.Diff.STE.fourierExp m x
      = if m = 0 then 1 else 0 := by
  rw [restrict_unitCube]
  simp_rw [fourierExp_eq_prod]
  have key :
      (∫ x : ι → ℝ,
          ∏ i, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m i : ℂ) * (x i : ℂ)))
        ∂ Measure.pi (fun _ : ι => (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)))
        = ∏ i, ∫ t : ℝ,
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m i : ℂ) * (t : ℂ)))
          ∂ (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1) :=
    integral_fintype_prod_eq_prod (E := fun _ : ι => ℝ)
      (μ := fun _ : ι => (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))
      (fun i t => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m i : ℂ) * (t : ℂ))))
  rw [key]
  simp_rw [integral_exp_two_pi_I]
  rw [Finset.prod_ite_zero]
  have hm : (∀ i, m i = 0) ↔ m = 0 :=
    ⟨fun h => funext h, fun h i => by rw [h]; rfl⟩
  simp [hm]

end Work.Diff.STE
