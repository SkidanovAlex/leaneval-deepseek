import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_err1_bump_defs
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs
import Submission.Commons.Analysis.Fourier.fourier_transform_min_decay

/-!
# Decay of the level-bump transform `mstHat`

`mstHat η t = ∫_{−1/2}^{1/2} η u · e^{−2πi t u} du` (`mst_err1_bump_defs`) is the `ℝ`-Fourier
transform of the level bump `η`, read off the fundamental domain.  This file proves the `t⁻²`
decay used in the MST route:

`‖mstHat η t‖ ≤ E / t²` for every `t ≠ 0`, provided the fundamental-domain lift
`circleLift (mstEta d χ η 0)` of the level-zero bump is `C²`.

The level-zero bump is `mstEta d χ η 0 ξ = η (iwRep ξ)` (`mstScale d χ 0 = 1`), so the hypothesis
says that `u ↦ η u` is `C²` on `(−1/2, 1/2)` and that the extension by `0` is `C²` at the
endpoints; equivalently `η` is a compactly supported `C²` function of the fundamental interval.

The proof is the standard two-fold integration by parts, in the finite-difference form of
`Commons.Analysis.Fourier.fourier_transform_min_decay` — which needs no boundary hypothesis at
all, only that the function and its second derivative are integrable:

* `m u := circleLift (mstEta d χ η 0) (−u)` is `C²` and compactly supported, and coincides with
  `η` on the interval `(−1/2, 1/2)` where the integral of `mstHat` lives;
* hence `mstHat η t = 𝓕 m t` (both sides are the integral of `e^{−2πi t u} η u` over that
  interval, up to the measure-zero endpoints);
* `‖𝓕 m t‖ ≤ (∫ ‖m''‖) / (2π|t|)²`, which is `E / t²` with `E = (∫ ‖m''‖) / (2π)²`.
-/

open MeasureTheory

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

noncomputable section

/-- The level-zero MST bump is the fixed bump read along the canonical lift:
`mstEta d χ η 0 ξ = η (iwRep ξ)` (because `mstScale d χ 0 = 2^0 = 1`). -/
lemma mstHat_mstEta_zero_eq (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) :
    mstEta d χ η 0 = fun ξ => η (iwRep ξ) := by
  funext ξ
  simp [mstEta_apply]

/-- On the open fundamental interval `(−1/2, 1/2)`, which is where the transform `mstHat`
integrates, the lift `circleLift (mstEta d χ η 0)` of the level-zero bump agrees with `η ∘ Neg.neg`:
the canonical lift `iwRep` inverts the sign there. -/
lemma circleLift_mstEta_zero_eq (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) :
    ∀ u ∈ Set.Ioo (-(1/2) : ℝ) (1/2),
      Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0) u = η (-u) := by
  intro u hu
  rw [Work.BourgainPlan.Thm52.circleLift_of_mem ⟨hu.1, hu.2.le⟩]
  have hη : mstEta d χ η 0 = fun ξ => η (iwRep ξ) := mstHat_mstEta_zero_eq d χ η
  have hinner : iwRep (-(u : Circ)) = -u := by
    have hcoe : (-(u : Circ)) = ((-u : ℝ) : Circ) :=
      (AddCircle.coe_neg (p := (1 : ℝ)) (x := u)).symm
    rw [hcoe]
    have hmem : (-u : ℝ) ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1) := by
      rw [Set.mem_Ioc]
      constructor <;> linarith [hu.1, hu.2]
    exact AddCircle.liftIoc_coe_apply hmem
  rw [hη]
  dsimp only
  rw [hinner]

theorem mstHat_decay {d : ℕ} {χ : ℝ} (η : ℝ → ℂ)
    (hcd0 : ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0))) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ, t ≠ 0 → ‖mstHat η t‖ ≤ E / t ^ 2 := by
  have hΦeval := circleLift_mstEta_zero_eq d χ η
  -- The function whose Fourier transform is `mstHat η`: the level bump composed with `Neg.neg`.
  set m : ℝ → ℂ := fun u => Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0) (-u) with hm
  have hm_apply : ∀ u : ℝ, m u = Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0) (-u) :=
    fun u => by rw [hm]
  have hcdm : ContDiff ℝ 2 m := by
    rw [hm]
    simpa only [Function.comp_def] using hcd0.comp contDiff_neg
  -- `m` agrees with `η` on the open fundamental interval
  have hmIoo : ∀ u ∈ Set.Ioo (-(1/2) : ℝ) (1/2), m u = η u := by
    intro u hu
    rw [hm_apply, hΦeval (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩, neg_neg]
  -- ... and vanishes off the closed fundamental interval
  have hmzero : ∀ u : ℝ, u ∉ Set.Icc (-(1/2) : ℝ) (1/2) → m u = 0 := by
    intro u hu
    rw [hm_apply]
    refine Work.BourgainPlan.Thm52.circleLift_of_notMem ?_
    intro hmem
    rw [Set.mem_Ioc] at hmem
    rw [Set.mem_Icc] at hu
    exact hu ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  have hcs : HasCompactSupport m := HasCompactSupport.intro isCompact_Icc hmzero
  -- integrability of `m` and of its second derivative, and its two derivatives
  have hint0 : Integrable m := hcdm.continuous.integrable_of_hasCompactSupport hcs
  have hcont2 : Continuous (deriv (deriv m)) := by
    have h := hcdm.continuous_iteratedDeriv 2 le_rfl
    have hid : iteratedDeriv 2 m = deriv (deriv m) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rwa [hid] at h
  have hint2 : Integrable (deriv (deriv m)) :=
    hcont2.integrable_of_hasCompactSupport hcs.deriv.deriv
  have hdiff1 : Differentiable ℝ m := hcdm.differentiable (by norm_num)
  have hdiff2 : Differentiable ℝ (deriv m) := by
    have h := hcdm.differentiable_iteratedDeriv' 1
    rwa [iteratedDeriv_one] at h
  -- `mstHat η t` is the Fourier transform of `m` at `t`
  have hFourier_eq : ∀ t : ℝ, FourierTransform.fourier m t =
      ∫ x in Set.Ioo (-(1/2) : ℝ) (1/2),
        Complex.exp ((↑(-2 * Real.pi * inner ℝ x t) * Complex.I)) • m x := by
    intro t
    rw [Real.fourier_eq' m t]
    have h1 : ∀ x ∉ Set.Icc (-(1/2) : ℝ) (1/2),
        Complex.exp ((↑(-2 * Real.pi * inner ℝ x t) * Complex.I)) • m x = 0 :=
      fun x hx => by rw [hmzero x hx, smul_zero]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h1,
      MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hmstHat_eq : ∀ t : ℝ, mstHat η t =
      ∫ x in Set.Ioo (-(1/2) : ℝ) (1/2),
        η x * Complex.exp ((((-(2 * Real.pi * t * x)) : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [mstHat_apply, intervalIntegral.integral_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hpt : ∀ t : ℝ, Set.EqOn
      (fun x : ℝ => η x * Complex.exp ((((-(2 * Real.pi * t * x)) : ℝ) : ℂ) * Complex.I))
      (fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * inner ℝ x t) * Complex.I)) • m x)
      (Set.Ioo (-(1/2) : ℝ) (1/2)) := by
    intro t x hx
    dsimp only
    rw [hmIoo x hx]
    have hexp : Complex.exp ((((-(2 * Real.pi * t * x)) : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((↑(-2 * Real.pi * inner ℝ x t) * Complex.I)) := by
      congr 1
      simp only [Real.inner_apply]
      push_cast
      ring
    rw [hexp, smul_eq_mul]
    ring
  have hmstHat : ∀ t : ℝ, mstHat η t = FourierTransform.fourier m t := by
    intro t
    rw [hmstHat_eq t, hFourier_eq t,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (hpt t)]
  -- two-fold integration by parts via `fourier_transform_min_decay`
  set B : ℝ := ∫ x, ‖deriv (deriv m) x‖ with hB
  have hB0 : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun x => norm_nonneg _)
  have hA0 : 0 ≤ ∫ x, ‖m x‖ := integral_nonneg (fun x => norm_nonneg _)
  refine ⟨B / (2 * Real.pi) ^ 2, by positivity, fun t ht => ?_⟩
  rw [hmstHat t]
  have hdec := Commons.Analysis.Fourier.fourier_transform_min_decay m (∫ x, ‖m x‖) B hA0 hB0
    hint0 hint2 hdiff1 hdiff2 le_rfl le_rfl t ht
  have h1 : ‖FourierTransform.fourier m t‖ ≤ B / (2 * Real.pi * |t|) ^ 2 :=
    hdec.trans (min_le_right _ _)
  have h2 : B / (2 * Real.pi * |t|) ^ 2 = (B / (2 * Real.pi) ^ 2) / t ^ 2 := by
    rw [mul_pow, sq_abs, ← div_div]
  rwa [h2] at h1

end

end Work.BourgainPlan.Maximal
