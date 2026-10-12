import Mathlib.Tactic.Have
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.ProfHatDecay
import Submission.Work.OneBodyKin.integrable_chiMul_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.exists_fsKinCoeff_mul_abs_profHat_le`

The FS cut-off `fsKinCoeff C r = [r − C]₊² = (max (r − C) 0)²` vanishes on `r ≤ C`, so for every
`C ≥ 0` the integrand `fsKinCoeff C ‖p‖ · |profHat p|` is dominated by `(1 + ‖p‖)² |profHat p|`,
and the latter is integrable because the bump profile decays like `(1 + ‖p‖)^{-6}`
(`Work.OneBodyKin.ProfHatDecay`), which leaves the integrable weight `(1 + ‖p‖)^{-4}` in
dimension `3`.

As `C → ∞` the integrand tends to `0` pointwise (`fsKinCoeff C r = 0` as soon as `C ≥ r`), so
Lebesgue dominated convergence (`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`)
gives

    `∫_p fsKinCoeff C ‖p‖ · |profHat p| dp  ⟶ 0`     as `C → ∞`,

hence for every `δ > 0` there is a cut-off `C > 0` for which the integral is at most `δ`.

This is the "the cut-off may be taken large" step for the symbol of the projected moving-box
family: it is what converts *pointwise* far-regime bounds on `famSym ℓ (fsKinCoeff C) q` — which
improve as `C` grows — into a statement about the untruncated symbol.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The dominating function -/

/-- **`p ↦ (1 + ‖p‖)² |profHat p|` is integrable.**  The decay `|profHat p| ≤ K (1+‖p‖)^{-6}`
turns it into `K (1 + ‖p‖)^{-4}`, and `(1 + ‖p‖)^{-4}` is integrable in dimension `3`.  This is
the domination used for every `fsKinCoeff`-weighted integral of `|profHat|` (the weight
`fsKinCoeff C ‖p‖ ≤ (1 + ‖p‖)²` for `C ≥ 0`). -/
lemma integrable_mul_abs_profHat_oneAddNorm_sq :
    Integrable (fun p : ℝ³ => (1 + ‖p‖) ^ 2 * |profHat p|) := by
  obtain ⟨K, _hK0, hK⟩ := ProfHatDecay
  have hdom : Integrable (fun p : ℝ³ => K * (1 + ‖p‖) ^ (-(4 : ℝ))) volume :=
    (integrable_one_add_norm (E := ℝ³) (μ := volume) (r := 4)
      (by rw [finrank_euclideanSpace_fin]; norm_num)).const_mul K
  have hmeas : AEStronglyMeasurable (fun p : ℝ³ => (1 + ‖p‖) ^ 2 * |profHat p|) volume :=
    (((continuous_const.add continuous_norm).pow 2).mul continuous_profHat.abs).aestronglyMeasurable
  refine hdom.mono' hmeas ?_
  filter_upwards with p
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (abs_nonneg _))]
  have hx : (0 : ℝ) < 1 + ‖p‖ := by positivity
  calc (1 + ‖p‖) ^ 2 * |profHat p|
      ≤ (1 + ‖p‖) ^ 2 * (K / (1 + ‖p‖) ^ 6) :=
        mul_le_mul_of_nonneg_left (hK p) (by positivity)
    _ = K * (1 + ‖p‖) ^ (-(4 : ℝ)) := by
        have h1 : (1 + ‖p‖) ^ (-(4 : ℝ)) = (((1 + ‖p‖) ^ 4 : ℝ))⁻¹ := by
          rw [Real.rpow_neg hx.le (4 : ℝ)]; norm_num
        rw [h1]
        field_simp

/-! ## The limit -/

/-- **The cut-off can be made large enough.**  For every `δ > 0` there is a cut-off `C > 0` with
`∫_p [‖p‖ − C]₊² |profHat p| dp ≤ δ`. -/
theorem exists_fsKinCoeff_mul_abs_profHat_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff C ‖p‖ * |profHat p| ≤ δ := by
  -- Dominated convergence: the integrals tend to `0` as `C → ∞`.
  have hmain : Tendsto (fun C : ℝ => ∫ p : ℝ³, fsKinCoeff C ‖p‖ * |profHat p|) atTop (nhds 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
      (F := fun C : ℝ => fun p : ℝ³ => fsKinCoeff C ‖p‖ * |profHat p|) (f := fun _ => 0)
      (fun p : ℝ³ => (1 + ‖p‖) ^ 2 * |profHat p|)
      ?_ ?_ integrable_mul_abs_profHat_oneAddNorm_sq ?_
    · simpa using h
    · -- measurability of every integrand
      exact Filter.Eventually.of_forall fun C =>
        ((((continuous_norm.sub continuous_const).max continuous_const).pow 2).mul
          continuous_profHat.abs).aestronglyMeasurable
    · -- domination, for `C ≥ 0`
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with C hC
      filter_upwards with p
      rw [Real.norm_of_nonneg (mul_nonneg (fsKinCoeff_nonneg C ‖p‖) (abs_nonneg _))]
      have h2 : fsKinCoeff C ‖p‖ ≤ (1 + ‖p‖) ^ 2 := by
        rw [fsKinCoeff]
        refine pow_le_pow_left₀ (le_max_right _ _) (max_le ?_ ?_) 2
        · linarith
        · positivity
      exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
    · -- pointwise convergence to `0`: the cut-off eventually swallows `‖p‖`
      filter_upwards with p
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop ‖p‖] with C hC
      rw [fsKinCoeff_of_le hC, zero_mul]
  -- Read off a cut-off `C > 0` at which the integral is at most `δ`.
  have hlt : ∀ᶠ C in atTop, (∫ p : ℝ³, fsKinCoeff C ‖p‖ * |profHat p|) < δ :=
    hmain.eventually (isOpen_Iio.mem_nhds hδ)
  have hpos : ∀ᶠ C in atTop, (0 : ℝ) < C := eventually_gt_atTop 0
  obtain ⟨C, hC1, hC2⟩ := (hlt.and hpos).exists
  exact ⟨C, hC2, le_of_lt hC1⟩

end Work.OneBodyKin
