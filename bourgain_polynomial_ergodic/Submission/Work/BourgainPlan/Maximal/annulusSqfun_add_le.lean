import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSqfunDefs
import Submission.Work.BourgainPlan.Maximal.annulusKernel_size
import Submission.Work.BourgainPlan.Maximal.annulusSquare_l2
import Submission.Work.BourgainPlan.Maximal.ENNReal_sqrt_tsum_tsum_sq_le_general

/-!
# The triangle inequality for the annulus square function

The annulus square function

  `S_j f = (∑'_n ‖(K_{j+n} * f)‖²)^{1/2}`,   `K_m = 𝓕⁻ (b m)`,

is subadditive, `S_j (g + β) ≤ S_j g + S_j β`.  This is the elementary triangle inequality that lets
the Calderón--Zygmund assembly split an `L¹` function into its good and bad parts: it is the `ℓ²`
triangle inequality applied after the linearity of the convolution.

There are three pieces.

* `annulusConv_add_of_integrable` — the convolution `annulusConv` is additive in the function
  argument, for `L¹` functions (`annulusKernel_size` at `N = 0` makes the kernel bounded, so the
  pieces are integrable and `integral_add` applies).
* `sqrt_tsum_add_sq_le_two` — discrete Minkowski for two summands, a direct consequence of the
  general discrete Minkowski inequality `ENNReal_sqrt_tsum_tsum_sq_le_general` with index type
  `Bool`.
* the pointwise norm inequality `‖K(x-y)(g y + β y)‖ ≤ ‖K(x-y) g y‖ + ‖K(x-y) β y‖`, i.e.
  `enorm_add_le`, pushed through the `ℓ²` sum.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-! ## 1. The annulus kernel is continuous -/

lemma continuous_fourierInv_of_integrable_annulus {f : ℝ → ℂ} (hf : Integrable f volume) :
    Continuous (FourierTransform.fourierInv f) := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  exact VectorFourier.fourierIntegral_continuous (L := innerₗ ℝ) Real.continuous_fourierChar
    continuous_inner hf.comp_neg

lemma continuous_annulusK_annulus (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ) :
    Continuous (annulusK b m) := by
  have hbint : Integrable (b m) volume := by
    simpa only [iteratedDeriv_zero] using annulusK_integrable b hb hsmooth m 0
  simpa only [annulusK] using continuous_fourierInv_of_integrable_annulus hbint

/-! ## 2. The convolution is additive in the function argument -/

lemma annulusConv_add_of_integrable (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (m : ℤ) (g β : ℝ → ℂ) (hg : Integrable g volume) (hβ : Integrable β volume) (x : ℝ) :
    annulusConv b m (fun y => g y + β y) x = annulusConv b m g x + annulusConv b m β x := by
  obtain ⟨C, _hCpos, hCbnd⟩ := annulusKernel_size b hb hsmooth 0
  have hKbdd : ∀ z : ℝ, ‖annulusK b m z‖ ≤ C * (2 : ℝ) ^ (-m) := by
    intro z
    have h := hCbnd m z
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at h
    simpa only [annulusK] using h
  have hcont : Continuous (fun y : ℝ => annulusK b m (x - y)) :=
    (continuous_annulusK_annulus b hb hsmooth m).comp (continuous_const.sub continuous_id)
  have hbdd : ∀ᵐ y ∂volume, ‖annulusK b m (x - y)‖ ≤ C * (2 : ℝ) ^ (-m) :=
    Filter.Eventually.of_forall fun y => hKbdd _
  have hint1 : Integrable (fun y : ℝ => annulusK b m (x - y) * g y) :=
    hg.bdd_mul hcont.aestronglyMeasurable hbdd
  have hint2 : Integrable (fun y : ℝ => annulusK b m (x - y) * β y) :=
    hβ.bdd_mul hcont.aestronglyMeasurable hbdd
  have hcongr : (∫ y, annulusK b m (x - y) * (g y + β y))
      = ∫ y, (annulusK b m (x - y) * g y + annulusK b m (x - y) * β y) :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  simp only [annulusConv]
  rw [hcongr, integral_add hint1 hint2]

/-! ## 3. Discrete Minkowski for two summands -/

lemma sqrt_tsum_add_sq_le_two (A B : ℤ → ℝ≥0∞) :
    (∑' n : ℤ, (A n + B n) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ (∑' n : ℤ, (A n) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        + (∑' n : ℤ, (B n) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  have h := ENNReal_sqrt_tsum_tsum_sq_le_general (ι := Bool)
    (a := fun n i => if i then B n else A n)
  simpa only [tsum_bool, Bool.false_eq_true, if_true, if_false, add_comm] using h

/-! ## 4. The triangle inequality -/

theorem annulusSqfun_add_le (b : ℤ → ℝ → ℂ)
    (hb : Work.BourgainPlan.Maximal.AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (j : ℤ) (g β : ℝ → ℂ)
    (hg : MeasureTheory.MemLp g 1 MeasureTheory.volume)
    (hβ : MeasureTheory.MemLp β 1 MeasureTheory.volume) (x : ℝ) :
    Work.BourgainPlan.Maximal.annulusSqfun b j (fun y : ℝ => g y + β y) x
      ≤ Work.BourgainPlan.Maximal.annulusSqfun b j g x
        + Work.BourgainPlan.Maximal.annulusSqfun b j β x := by
  have hgint : Integrable g volume := memLp_one_iff_integrable.mp hg
  have hβint : Integrable β volume := memLp_one_iff_integrable.mp hβ
  have hconv : ∀ n : ℤ, annulusConv b (j + n) (fun y => g y + β y) x =
      annulusConv b (j + n) g x + annulusConv b (j + n) β x :=
    fun n => annulusConv_add_of_integrable b hb hsmooth (j + n) g β hgint hβint x
  have hstep1 : (∑' n : ℤ, ‖annulusConv b (j + n) (fun y => g y + β y) x‖ₑ
        ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ (∑' n : ℤ, (‖annulusConv b (j + n) g x‖ₑ
          + ‖annulusConv b (j + n) β x‖ₑ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
    refine ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun n => ?_) (by norm_num)
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [hconv n]
    exact enorm_add_le _ _
  have hstep2 := sqrt_tsum_add_sq_le_two (fun n : ℤ => ‖annulusConv b (j + n) g x‖ₑ)
    (fun n : ℤ => ‖annulusConv b (j + n) β x‖ₑ)
  simp only [annulusSqfun]
  exact hstep1.trans hstep2

end Work.BourgainPlan.Maximal
