import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.integral_fourierExp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Fourier coefficients of `g * seriesFun c`

For a function `g` integrable on the unit cube and an `ℓ¹` coefficient family `c`, the pointwise
product `g · seriesFun c` has Fourier coefficients given by the coefficient convolution

  `fourierCoeff (fun x => g x * seriesFun c x) k = conv c (fourierCoeff g) k`,

the Fourier-side product rule.  The series `seriesFun c = ∑_l c l · fourierExp l` is absolutely
convergent (the characters have modulus one), so the product may be integrated term by term
(`MeasureTheory.integral_tsum`, with the dominating constant `∑ ‖c l‖ · ‖g‖`), and the characters
multiply, `fourierExp m x * fourierExp l x = fourierExp (m + l) x`, so that
`fourierExp (-k) · fourierExp l = fourierExp (-(k - l))`.

The auxiliary lemma `integral_mul_seriesFun` is the term by term integration step.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE

/-! ## Elementary properties of the characters -/

private lemma fourierExp_norm_eq_one {ι : Type*} [Fintype ι] (k : ι → ℤ) (x : ι → ℝ) :
    ‖fourierExp k x‖ = 1 := by
  have hmain : (2 * (Real.pi : ℂ) * Complex.I * ∑ i, ((k i : ℤ) : ℂ) * (x i : ℂ))
      = (((2 * Real.pi * ∑ i, ((k i : ℤ) : ℝ) * x i : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [fourierExp, hmain, Complex.norm_exp_ofReal_mul_I]

private lemma fourierExp_enorm_eq_one {ι : Type*} [Fintype ι] (k : ι → ℤ) (x : ι → ℝ) :
    ‖fourierExp k x‖ₑ = 1 := by
  have h : ‖fourierExp k x‖ = 1 := fourierExp_norm_eq_one k x
  rw [enorm_eq_nnnorm, show ‖fourierExp k x‖₊ = 1 from by
    rw [← NNReal.coe_inj, coe_nnnorm, h]; rfl, ENNReal.coe_one]

private lemma continuous_fourierExp_char {ι : Type*} [Fintype ι] (k : ι → ℤ) :
    Continuous (fourierExp (ι := ι) k) := by
  unfold fourierExp
  fun_prop

private lemma fourierExp_mul_add {ι : Type*} [Fintype ι] (m n : ι → ℤ) (x : ι → ℝ) :
    fourierExp m x * fourierExp n x = fourierExp (m + n) x := by
  rw [fourierExp, fourierExp, fourierExp, ← Complex.exp_add]
  congr 1
  have h : (∑ i, (((m + n) i : ℤ) : ℂ) * (x i : ℂ))
      = (∑ i, ((m i : ℤ) : ℂ) * (x i : ℂ)) + ∑ i, ((n i : ℤ) : ℂ) * (x i : ℂ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.add_apply, Int.cast_add]; ring)
  rw [h]; ring

/-! ## Term by term integration of a Fourier series -/

/-- For an `ℓ¹` coefficient family `c` and an integrable `h`, the product `h · seriesFun c`
integrates term by term:

  `∫ h · seriesFun c = ∑_l c l · ∫ h · fourierExp l`.

The characters have modulus one, so `‖c l · fourierExp l‖ = ‖c l‖` and the hypotheses of
`MeasureTheory.integral_tsum` hold with dominating summable family `l ↦ ‖c l‖ · ∫⁻ ‖h‖`. -/
private theorem integral_mul_seriesFun {ι : Type*} [Fintype ι] (h : (ι → ℝ) → ℂ)
    (c : (ι → ℤ) → ℂ)
    (hh : Integrable h (volume.restrict (unitCube (ι := ι))))
    (hc : Summable (fun l : ι → ℤ => ‖c l‖)) :
    (∫ x in unitCube, h x * seriesFun c x)
      = ∑' l : ι → ℤ, c l * ∫ x in unitCube, h x * fourierExp l x := by
  have hmeas : ∀ l : ι → ℤ, AEStronglyMeasurable
      (fun x : ι → ℝ => h x * (c l * fourierExp l x))
      (volume.restrict (unitCube (ι := ι))) :=
    fun l => hh.aestronglyMeasurable.mul
      ((continuous_const.mul (continuous_fourierExp_char l)).aestronglyMeasurable)
  have hterms : ∀ l : ι → ℤ,
      ∫⁻ x, ‖h x * (c l * fourierExp l x)‖ₑ ∂(volume.restrict (unitCube (ι := ι)))
        = ‖c l‖ₑ * ∫⁻ x, ‖h x‖ₑ ∂(volume.restrict (unitCube (ι := ι))) := by
    intro l
    have hpt : ∀ x : ι → ℝ,
        ‖h x * (c l * fourierExp l x)‖ₑ = ‖c l‖ₑ * ‖h x‖ₑ := by
      intro x
      rw [enorm_mul, enorm_mul, fourierExp_enorm_eq_one l x, mul_one, mul_comm]
    simp_rw [hpt]
    exact lintegral_const_mul' _ _ (by rw [enorm_eq_nnnorm]; exact ENNReal.coe_ne_top)
  have hA : ∫⁻ x, ‖h x‖ₑ ∂(volume.restrict (unitCube (ι := ι))) ≠ ⊤ :=
    ne_of_lt hh.hasFiniteIntegral
  have htsum : (∑' l : ι → ℤ, ‖c l‖ₑ) ≠ ⊤ := by
    simp only [enorm_eq_nnnorm]
    rw [ENNReal.tsum_coe_ne_top_iff_summable]
    rw [← NNReal.summable_coe (f := fun k : ι → ℤ => ‖c k‖₊)]
    simpa only [coe_nnnorm] using hc
  have hlin : ∑' l : ι → ℤ,
      ∫⁻ x, ‖h x * (c l * fourierExp l x)‖ₑ ∂(volume.restrict (unitCube (ι := ι))) ≠ ⊤ := by
    have h1 : ∑' l : ι → ℤ,
        ∫⁻ x, ‖h x * (c l * fourierExp l x)‖ₑ ∂(volume.restrict (unitCube (ι := ι)))
        = (∑' l : ι → ℤ, ‖c l‖ₑ)
          * ∫⁻ x, ‖h x‖ₑ ∂(volume.restrict (unitCube (ι := ι))) := by
      simp_rw [hterms]
      exact ENNReal.tsum_mul_right
    rw [h1]
    exact ENNReal.mul_ne_top htsum hA
  have key := integral_tsum (μ := volume.restrict (unitCube (ι := ι)))
    (f := fun (l : ι → ℤ) (x : ι → ℝ) => h x * (c l * fourierExp l x)) hmeas hlin
  calc (∫ x in unitCube, h x * seriesFun c x)
      = ∫ x, ∑' l : ι → ℤ, h x * (c l * fourierExp l x)
          ∂(volume.restrict (unitCube (ι := ι))) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [seriesFun]
        exact (tsum_mul_left (a := h x)
          (f := fun l : ι → ℤ => c l * fourierExp l x)).symm
    _ = ∑' l : ι → ℤ, ∫ x, h x * (c l * fourierExp l x)
          ∂(volume.restrict (unitCube (ι := ι))) := key
    _ = ∑' l : ι → ℤ, c l * ∫ x in unitCube, h x * fourierExp l x := by
        apply tsum_congr
        intro l
        have hpt : ∀ x : ι → ℝ, h x * (c l * fourierExp l x) = c l * (h x * fourierExp l x) :=
          fun x => by ring
        simp_rw [hpt]
        rw [integral_const_mul]

theorem fourierCoeff_mul_seriesFun {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℝ) → ℂ) (c : (ι → ℤ) → ℂ) (k : ι → ℤ)
    (hg : MeasureTheory.Integrable g
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι))))
    (hc : Summable (fun l : ι → ℤ => ‖c l‖)) :
    Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => g x * Work.Diff.STE.seriesFun c x) k
      = Work.Diff.STE.conv c (Work.Diff.STE.fourierCoeff g) k := by
  -- `fourierExp (-k) * g` is integrable on the cube, being bounded times `g`.
  have hh : Integrable (fun x : ι → ℝ => fourierExp (-k) x * g x)
      (volume.restrict (unitCube (ι := ι))) := by
    refine hg.norm.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((continuous_fourierExp_char (-k)).aestronglyMeasurable).mul hg.aestronglyMeasurable
    · rw [norm_mul, fourierExp_norm_eq_one, one_mul]
  have key := integral_mul_seriesFun (fun x : ι → ℝ => fourierExp (-k) x * g x) c hh hc
  show (∫ x in unitCube, fourierExp (-k) x * (g x * seriesFun c x))
      = conv c (fourierCoeff g) k
  have h1 : (∫ x in unitCube, fourierExp (-k) x * (g x * seriesFun c x))
      = ∫ x in unitCube, (fourierExp (-k) x * g x) * seriesFun c x := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [h1, key,
    show conv c (fourierCoeff g) k = ∑' l : ι → ℤ, c l * fourierCoeff g (k - l) from rfl]
  apply tsum_congr
  intro l
  congr 1
  rw [fourierCoeff]
  apply integral_congr_ae
  filter_upwards with x
  rw [show (fourierExp (-k) x * g x) * fourierExp l x
      = (fourierExp (-k) x * fourierExp l x) * g x by ring, fourierExp_mul_add,
    show (-k + l : ι → ℤ) = -(k - l) by
      funext i; simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]; ring]

end Work.Diff.STE
