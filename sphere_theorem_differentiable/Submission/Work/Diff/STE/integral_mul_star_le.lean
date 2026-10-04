import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.bessel_continuous
import Submission.Work.Diff.STE.norm_sq_Lp_eq_integral

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cauchy–Schwarz (`L²` Hölder with exponents `2,2`) for the integral over the unit cube

For two continuous functions `f g : (ι → ℝ) → ℂ` on the unit cube `(0,1]^ι`,

  `‖∫_{cube} f x * star (g x)‖ ≤ √(∫_{cube} ‖f x‖²) · √(∫_{cube} ‖g x‖²)`,

i.e. Cauchy–Schwarz for the `L²` pairing `⟨f, g⟩ = ∫ f · conj g`.

The proof is the standard three-step chain:

* `‖∫ f · conj g‖ ≤ ∫ ‖f · conj g‖` (triangle inequality for the Bochner integral,
  `MeasureTheory.norm_integral_le_integral_norm`), with `‖f · conj g‖ = ‖f‖ · ‖g‖`;
* Hölder with conjugate exponents `p = q = 2` for the nonnegative functions `‖f‖`, `‖g‖`
  (`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`);
* rewriting the `L²` exponents `(∫ ‖f‖²)^{1/2}` as `Real.sqrt`.

The only non-trivial ingredient is square integrability on the cube, which is supplied by
`BesselCont.memLp_of_continuous`: a continuous function is bounded on the compact cube
`[0,1]^ι`.
-/

noncomputable section

open MeasureTheory BigOperators ComplexConjugate

namespace Work.Diff.STE

/-- **Cauchy–Schwarz for the unit cube.** For continuous `f g : (ι → ℝ) → ℂ`, the modulus of
`∫_{cube} f · conj g` is at most the product of the `L²` norms of `f` and `g`. -/
theorem integral_mul_star_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : (ι → ℝ) → ℂ) (hf : Continuous f) (hg : Continuous g) :
    ‖∫ x in Work.Diff.STE.unitCube, f x * star (g x)‖
      ≤ Real.sqrt (∫ x in Work.Diff.STE.unitCube, ‖f x‖ ^ 2)
        * Real.sqrt (∫ x in Work.Diff.STE.unitCube, ‖g x‖ ^ 2) := by
  have hmf : MemLp f 2 ((volume : Measure (ι → ℝ)).restrict (unitCube (ι := ι))) :=
    BesselCont.memLp_of_continuous f hf
  have hmg : MemLp g 2 ((volume : Measure (ι → ℝ)).restrict (unitCube (ι := ι))) :=
    BesselCont.memLp_of_continuous g hg
  -- Step 1: triangle inequality, and `‖f x * star (g x)‖ = ‖f x‖ * ‖g x‖`.
  have h1 : ‖∫ x, f x * star (g x) ∂((volume : Measure (ι → ℝ)).restrict (unitCube (ι := ι)))‖
      ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂((volume : Measure (ι → ℝ)).restrict (unitCube (ι := ι))) := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans_eq ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_mul, norm_star]
  -- Step 2: Hölder with `p = q = 2` for `‖f‖` and `‖g‖`.
  have h2 := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := (volume : Measure (ι → ℝ)).restrict (unitCube (ι := ι)))
      (p := 2) (q := 2) Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (by simpa using hmf.norm) (by simpa using hmg.norm)
  -- Step 3: assemble and rewrite `x ^ (1/2)` as `Real.sqrt x`.
  have hbridge : ‖∫ x in unitCube, f x * star (g x)‖
      = ‖∫ x, f x * star (g x) ∂((volume : Measure (ι → ℝ)).restrict (unitCube (ι := ι)))‖ := rfl
  rw [hbridge]
  refine h1.trans (h2.trans_eq ?_)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]

end Work.Diff.STE
