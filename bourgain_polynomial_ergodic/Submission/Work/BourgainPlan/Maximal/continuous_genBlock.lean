import Mathlib
import Submission.Work.BourgainPlan.Maximal.genWindow_defs

/-!
# Continuity of the general-`P` block `genBlock`

`genBlock P k q D φ g s z` is `q` times the inverse Fourier transform of the amplitude
`genAmpF P k q D φ g s z = genBetaAmp · conj(polyProfile)`, evaluated at `q x`.

Two facts give continuity:

* the amplitude `genAmpF` is integrable — it is the product of the compactly supported continuous
  slice amplitude `genBetaAmp` (supported in `[-1/(2D), 1/(2D)]` because the window `φ` vanishes
  off `[-1/2,1/2]`) with the profile `polyProfile`, which is bounded by `1`;
* an inverse Fourier transform of an integrable function is continuous
  (`Commons.Analysis.ExponentialSums.continuous_fourierInv`).

Continuity is then preserved by the dilation `x ↦ q x` and multiplication by the constant `q`.

The integrability lemmas are proved here in full (rather than imported from
`genWindow_analytic`) so that this module only depends on the definitional file `genWindow_defs`.
-/

open MeasureTheory Set

namespace Work.BourgainPlan.Maximal

/-- The slice amplitude is integrable (it is continuous with compact support `[-1/(2D),1/(2D)]`). -/
theorem integrable_genBetaAmp_local (q : ℕ) {D : ℝ} (hD : 0 < D) {φ : ℝ → ℂ}
    (hφ : Continuous φ) (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) : Integrable (genBetaAmp q D φ g s z) := by
  refine Continuous.integrable_of_hasCompactSupport (continuous_genBetaAmp q D hφ g s z) ?_
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(1/(2*D))) (1/(2*D)))
    isCompact_Icc (fun β hβ => ?_)
  rw [Function.mem_support] at hβ
  by_contra hcon
  exact hβ (genBetaAmp_eq_zero_of_notMem q hD hφs g s z hcon)

/-- The full amplitude of the `k`-th block is integrable. -/
theorem integrable_genAmpF_local (P : Polynomial ℤ) (k : ℕ) (q : ℕ) {D : ℝ} (hD : 0 < D)
    {φ : ℝ → ℂ} (hφ : Continuous φ) (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) : Integrable (genAmpF P k q D φ g s z) := by
  have hbdd : ∀ β : ℝ, ‖starRingEnd ℂ (polyProfile P (2^k) β)‖ ≤ 1 := by
    intro β
    rw [starRingEnd_apply, norm_star]
    exact norm_polyProfile_le_one P (2^k) β
  refine Integrable.mono' ((integrable_genBetaAmp_local q hD hφ hφs g s z).norm)
    ((continuous_genAmpF P k q D hφ g s z).aestronglyMeasurable) ?_
  filter_upwards with β
  rw [genAmpF, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hbdd β)

theorem continuous_genBlock (P : Polynomial ℤ) (k q : ℕ) (hq : 0 < q) {D : ℝ} (hD : 0 < D)
    (h1D : 1 ≤ D) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    Continuous (genBlock P k q D φ g s z) := by
  have hInt : Integrable (genAmpF P k q D φ g s z) :=
    integrable_genAmpF_local P k q hD hφ.continuous hφs g s z
  have hcont : Continuous (FourierTransformInv.fourierInv (genAmpF P k q D φ g s z)) :=
    Commons.Analysis.ExponentialSums.continuous_fourierInv hInt
  unfold genBlock
  exact continuous_const.mul (hcont.comp (by fun_prop))

end Work.BourgainPlan.Maximal
