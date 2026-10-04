import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.integral_fourierExp
import Submission.Work.Diff.STE.norm_sq_Lp_eq_integral
import Submission.Work.Diff.STE.bessel_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bessel's inequality for the Fourier coefficients on the unit cube

Layer A of the STE Fourier toolkit.  For any `f : (ι → ℝ) → ℂ` whose `‖f‖²` is integrable on
the half-open unit cube `unitCube = (0,1]^ι`, the Fourier coefficient family
`k ↦ fourierCoeff f k = ∫_{unitCube} fourierExp (-k) · f` is square summable and its weighted
`ℓ²` norm is bounded by the `L²` norm of `f`:

  `Σ_k ‖fourierCoeff f k‖² ≤ ∫_{unitCube} ‖f‖²`.

This is Bessel's inequality for the family of characters, which is an orthonormal system in the
Hilbert space `L²(unitCube)`: Mathlib's `Orthonormal.inner_products_summable` and
`Orthonormal.tsum_inner_products_le` give both the summability and the bound.

The orthonormality of the characters in `L²` and the identity
`⟪fourierExp k, f⟫ = fourierCoeff f k` for `f ∈ L²` are proved in the sibling module
`Submission/Work/Diff/STE/bessel_continuous.lean` (namespace `Work.Diff.STE.BesselCont`, where
the character is called `charLp`); here we only have to reduce the hypothesis
`Integrable (fun x => ‖f x‖²)` to that situation:

* if `f` is a.e. strongly measurable, then `MemLp f 2` by `memLp_two_iff_integrable_sq_norm`,
  and the Bessel inequality is that of `BesselCont.orthonormal_charLp` applied to the class of
  `f`, using `‖MemLp.toLp f _‖² = ∫ ‖f‖²`;
* if `f` is *not* a.e. strongly measurable then every Fourier coefficient vanishes: the
  integrand `fourierExp (-k) · f` is not integrable, since multiplying by the nowhere
  vanishing continuous factor `fourierExp (-k)` preserves a.e. strong measurability, and the
  Bochner integral of a non-integrable function is `0` by convention.  The right-hand side is
  nonnegative for trivial reasons, so the inequality survives.

Note that the hypothesis `Integrable (fun x => ‖f x‖²)` does **not** imply that `f` is
a.e. strongly measurable (compose the constant function `1` with the indicator of a
non-measurable set), which is why the second case genuinely occurs and why the statement is
made for `f` with `Integrable (fun x => ‖f x‖²)` rather than for `f ∈ L²`.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lebesgue measure restricted to the half-open unit cube `(0,1]^ι`. -/
abbrev besselCubeMeas (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  (volume : Measure (ι → ℝ)).restrict (unitCube (ι := ι))

/-- For `f ∈ L²` on the cube, the square of the `L²` norm of its `Lp`-class is the integral of
`‖f‖²`. -/
lemma bessel_norm_sq_toLp (f : (ι → ℝ) → ℂ) (hf : MemLp f 2 (besselCubeMeas ι)) :
    ‖MemLp.toLp f hf‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂besselCubeMeas ι := by
  rw [norm_sq_Lp_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hf] with a ha
  rw [ha]

/-- If `f` is not a.e. strongly measurable on the unit cube, then all its Fourier coefficients
vanish: the integrand `fourierExp (-k) · f` is not integrable (multiplication by the nowhere
vanishing continuous factor `fourierExp (-k)` preserves a.e. strong measurability), and the
Bochner integral of a non-integrable function is `0` by convention. -/
lemma bessel_fourierCoeff_eq_zero_of_not_aestronglyMeasurable (f : (ι → ℝ) → ℂ)
    (hf : ¬ AEStronglyMeasurable f (besselCubeMeas ι)) (k : ι → ℤ) : fourierCoeff f k = 0 := by
  have hcontr : ¬ Integrable (fun x : ι → ℝ => fourierExp (-k) x * f x) (besselCubeMeas ι) := by
    intro hint
    refine hf ?_
    have hconj : AEStronglyMeasurable (fun x : ι → ℝ => conj (fourierExp (-k) x))
        (besselCubeMeas ι) :=
      (Complex.continuous_conj.comp (BesselCont.continuous_fourierExp_char (-k))).aestronglyMeasurable
    refine (hconj.mul hint.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun x => ?_)
    show conj (fourierExp (-k) x) * (fourierExp (-k) x * f x) = f x
    rw [← mul_assoc, Complex.conj_mul', BesselCont.norm_fourierExp_char]
    norm_num
  exact integral_undef hcontr

/-- **Bessel's inequality** for the Fourier coefficients of a function on the unit cube whose
square is integrable. -/
theorem bessel_fourierCoeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ)
    (hf : MeasureTheory.Integrable (fun x : ι → ℝ => ‖f x‖ ^ 2)
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι)))) :
    Summable (fun k : ι → ℤ => ‖Work.Diff.STE.fourierCoeff f k‖ ^ 2) ∧
      ∑' k : ι → ℤ, ‖Work.Diff.STE.fourierCoeff f k‖ ^ 2
        ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖f x‖ ^ 2 := by
  classical
  by_cases hmeas : AEStronglyMeasurable f (besselCubeMeas ι)
  · -- ## Case 1: `f` has an `L²` class, so Bessel's inequality in `L²` applies.
    have hmem : MemLp f 2 (besselCubeMeas ι) :=
      (memLp_two_iff_integrable_sq_norm hmeas).mpr hf
    have horth := BesselCont.orthonormal_charLp (ι := ι)
    have hinner : ∀ k : ι → ℤ,
        inner ℂ (BesselCont.charLp (ι := ι) k) (MemLp.toLp f hmem) = fourierCoeff f k :=
      fun k => BesselCont.inner_charLp_toLp f hmem k
    have hnorm : ‖MemLp.toLp f hmem‖ ^ 2 = ∫ x in unitCube (ι := ι), ‖f x‖ ^ 2 :=
      bessel_norm_sq_toLp f hmem
    refine ⟨(horth.inner_products_summable (MemLp.toLp f hmem)).congr
      (fun k => by rw [hinner k]), ?_⟩
    calc ∑' k : ι → ℤ, ‖fourierCoeff f k‖ ^ 2
        = ∑' k : ι → ℤ,
            ‖inner ℂ (BesselCont.charLp (ι := ι) k) (MemLp.toLp f hmem)‖ ^ 2 :=
          tsum_congr (fun k => by rw [hinner k])
      _ ≤ ‖MemLp.toLp f hmem‖ ^ 2 := horth.tsum_inner_products_le (MemLp.toLp f hmem)
      _ = ∫ x in unitCube (ι := ι), ‖f x‖ ^ 2 := hnorm
  · -- ## Case 2: `f` is not a.e. strongly measurable, so all coefficients vanish.
    have hzero : ∀ k : ι → ℤ, fourierCoeff f k = 0 :=
      fun k => bessel_fourierCoeff_eq_zero_of_not_aestronglyMeasurable f hmeas k
    have hzero' : ∀ k : ι → ℤ, ‖fourierCoeff f k‖ ^ 2 = (0 : ℝ) := fun k => by
      rw [hzero k]
      norm_num
    refine ⟨?_, ?_⟩
    · simpa only [hzero'] using (summable_zero : Summable fun _ : ι → ℤ => (0 : ℝ))
    · rw [tsum_congr hzero']
      simp only [tsum_zero]
      exact integral_nonneg fun x => by positivity

end Work.Diff.STE
