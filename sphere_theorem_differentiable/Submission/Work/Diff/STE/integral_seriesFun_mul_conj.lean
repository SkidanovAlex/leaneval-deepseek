import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.integral_fourierExp
import Submission.Work.Diff.STE.seriesFun_mul
import Submission.Work.Diff.STE.star_seriesFun
import Submission.Work.Diff.STE.summable_conv_norm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `L²` pairing of a Fourier series with the conjugate of another

Layer A of the STE Fourier toolkit.  For two coefficient families
`c d : (ι → ℤ) → ℂ` in `ℓ¹(ℤ^ι)`, the integral over the half open unit cube
`unitCube = (0,1]^ι` of the pointwise product of the Fourier series
`seriesFun c` with the *complex conjugate* of `seriesFun d` is the pairing of the
coefficients:

  `∫_{unitCube} seriesFun c x * star (seriesFun d x) dx = ∑'_k c k * star (d k)`.

This is Parseval/orthogonality of the characters `fourierExp k` on the cube, made
elementary by absolute convergence: the characters have modulus one, so the `ℓ¹` norms of the
coefficient families bound the relevant integrals, and the integral of a character
`∫_{unitCube} fourierExp m x dx` is `1` for `m = 0` and `0` otherwise
(`Work.Diff.STE.integral_fourierExp`).

The proof splits into two independent pieces, proved in sibling files:

* `Work.Diff.STE.star_seriesFun`: conjugating a Fourier series conjugates and reflects the
  coefficient family, `star (seriesFun d x) = seriesFun (fun k => star (d (-k))) x`;
* `Work.Diff.STE.summable_conv_norm`: `ℓ¹` is closed under the coefficient convolution
  `conv` (`Work.Diff.STE.seriesFun_mul` writes the product of two series as the series of the
  convolution), so that the coefficient family of the product is again in `ℓ¹`;

and on the local lemma `integral_seriesFun` below: the integral of a Fourier series over the
cube is its zeroth coefficient.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators
open scoped ComplexConjugate

/-- **Integral of a Fourier series.**  If the coefficient family `c` is in `ℓ¹`, then term by
term integration of `seriesFun c x = ∑_k c k * fourierExp k x` against the orthogonality
relation `∫_{unitCube} fourierExp m = δ_{m,0}` gives the zeroth coefficient. -/
private theorem integral_seriesFun {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → ℤ) → ℂ) (hc : Summable (fun k : ι → ℤ => ‖c k‖)) :
    (∫ x in Work.Diff.STE.unitCube (ι := ι), Work.Diff.STE.seriesFun c x) = c 0 := by
  -- The characters are continuous ...
  have hcont : ∀ k : ι → ℤ, Continuous (Work.Diff.STE.fourierExp (ι := ι) k) := by
    intro k
    unfold Work.Diff.STE.fourierExp
    fun_prop
  -- ... and of modulus one.
  have hnorm : ∀ (k : ι → ℤ) (x : ι → ℝ), ‖Work.Diff.STE.fourierExp k x‖ = 1 := by
    intro k x
    have hmain : (2 * (Real.pi : ℂ) * Complex.I * ∑ i, ((k i : ℤ) : ℂ) * (x i : ℂ))
        = (((2 * Real.pi * ∑ i, ((k i : ℤ) : ℝ) * x i : ℝ)) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [Work.Diff.STE.fourierExp, hmain, Complex.norm_exp_ofReal_mul_I]
  -- Bookkeeping for the cube: it has volume one.
  set μ : Measure (ι → ℝ) :=
    (volume : Measure (ι → ℝ)).restrict (Work.Diff.STE.unitCube (ι := ι)) with hμdef
  have hvol : (volume : Measure (ι → ℝ)) (Work.Diff.STE.unitCube (ι := ι)) = 1 := by
    rw [Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
    simp
  have hμuniv : μ Set.univ = 1 := by
    rw [hμdef, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hvol]
  -- The `k`-th summand has constant modulus `‖c k‖` on the cube.
  have hterm : ∀ k : ι → ℤ, ∫⁻ a, ‖c k * Work.Diff.STE.fourierExp k a‖ₑ ∂μ = ‖c k‖ₑ := by
    intro k
    have hpt : ∀ a : ι → ℝ, ‖c k * Work.Diff.STE.fourierExp k a‖ₑ = ‖c k‖ₑ := by
      intro a
      have hE : ‖Work.Diff.STE.fourierExp k a‖ₑ = 1 := by
        rw [enorm_eq_nnnorm, ← ENNReal.coe_one, ENNReal.coe_inj, ← NNReal.coe_eq_one,
          coe_nnnorm, hnorm k a]
      rw [enorm_mul, hE, mul_one]
    simp_rw [hpt]
    rw [MeasureTheory.lintegral_const, hμuniv, mul_one]
  -- Hence the dominated convergence theorem for series applies.
  have hlin : ∑' k : ι → ℤ, ∫⁻ a, ‖c k * Work.Diff.STE.fourierExp k a‖ₑ ∂μ ≠ ⊤ := by
    simp_rw [hterm, enorm_eq_nnnorm]
    refine ENNReal.tsum_coe_ne_top_iff_summable.mpr ?_
    rw [← NNReal.summable_coe (f := fun k : ι → ℤ => ‖c k‖₊)]
    simpa only [coe_nnnorm] using hc
  rw [show (∫ x in Work.Diff.STE.unitCube (ι := ι), Work.Diff.STE.seriesFun c x)
      = ∫ x, ∑' k : ι → ℤ, c k * Work.Diff.STE.fourierExp k x ∂μ from rfl]
  rw [MeasureTheory.integral_tsum
    (fun k => ((hcont k).const_mul (c k)).aestronglyMeasurable) hlin]
  simp_rw [MeasureTheory.integral_const_mul]
  simp_rw [show ∀ k : ι → ℤ,
      (∫ x, Work.Diff.STE.fourierExp k x ∂μ) = if k = 0 then 1 else 0
      from fun k => Work.Diff.STE.integral_fourierExp k]
  have hite : ∀ k : ι → ℤ, c k * (if k = 0 then (1 : ℂ) else 0) = if k = 0 then c k else 0 := by
    intro k
    by_cases h : k = 0 <;> simp [h]
  simp_rw [hite]
  rw [tsum_ite_eq]

theorem integral_seriesFun_mul_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c d : (ι → ℤ) → ℂ) (hc : Summable (fun k : ι → ℤ => ‖c k‖))
    (hd : Summable (fun k : ι → ℤ => ‖d k‖)) :
    (∫ x in Work.Diff.STE.unitCube (ι := ι),
        Work.Diff.STE.seriesFun c x * star (Work.Diff.STE.seriesFun d x))
      = ∑' k : ι → ℤ, c k * star (d k) := by
  classical
  -- The conjugated coefficient family, and its `ℓ¹` summability.
  have hd' : Summable (fun k : ι → ℤ => ‖star (d (-k))‖) := by
    have hinj : Function.Injective (fun k : ι → ℤ => -k) := fun a b h => by simpa using h
    have h1 : Summable (fun k : ι → ℤ => ‖d (-k)‖) := hd.comp_injective hinj
    simpa using h1
  -- Conjugate the second series and apply the multiplicativity of `seriesFun`.
  have key : (∫ x in Work.Diff.STE.unitCube (ι := ι),
        Work.Diff.STE.seriesFun c x * star (Work.Diff.STE.seriesFun d x))
      = ∫ x in Work.Diff.STE.unitCube (ι := ι),
          Work.Diff.STE.seriesFun (Work.Diff.STE.conv c (fun k : ι → ℤ => star (d (-k)))) x := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [Work.Diff.STE.star_seriesFun d hd x,
      Work.Diff.STE.seriesFun_mul c (fun k : ι → ℤ => star (d (-k))) hc hd' x]
  rw [key,
    integral_seriesFun (Work.Diff.STE.conv c (fun k : ι → ℤ => star (d (-k))))
      (Work.Diff.STE.summable_conv_norm c (fun k : ι → ℤ => star (d (-k))) hc hd')]
  -- The zeroth coefficient of the convolution is the pairing with the reflected family.
  simp only [Work.Diff.STE.conv]
  exact tsum_congr (fun l => by simp)

end Work.Diff.STE
