import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.gSum_fourier

/-!
# `∫_s ‖ĝ‖² ≤ ∫ (g)²` for GM's majorant

For a continuous compactly supported `f : ℝ → ℝ`, write `g = gSum K M₁ M₂ M₃ f` for GM's
majorant of the affine sum and `ĝ = ghat K M₁ M₂ M₃ f = 𝓕 g` for its Fourier transform.

By Plancherel for `g` (the workspace lemma `gSum_fourier`, proved in `gSum_fourier.lean`) the
total `L²` mass of `g` equals that of `ĝ`:

  `∫ u, (g u)² = ∫ ξ, ‖ĝ ξ‖²`.

Hence, for any set `s`, the estimate `∫_s ‖ĝ‖² ≤ ∫ u, (g u)²` is the monotonicity statement
`∫_s ‖ĝ‖² ≤ ∫_ℝ ‖ĝ‖²`, the only real content of which is that `‖ĝ‖²` is *integrable*: for the
Bochner integral the inequality `∫_s h ≤ ∫_ℝ h` needs integrability of `h` (otherwise the
right-hand side collapses to the junk value `0`).

We obtain integrability from Plancherel written in `ℝ≥0∞`-valued (Lebesgue integral) form:
for continuous compactly supported `g : ℝ → ℂ`,

  `∫⁻ ξ, ENNReal.ofReal ‖𝓕 g ξ‖² = ∫⁻ x, ENNReal.ofReal ‖g x‖²`,

which is `lintegral_ofReal_fourier_sq_eq` below.  In this form the two sides are genuinely
equal (no junk values): the right-hand side is finite because `g` is continuous with compact
support, and the equality transfers this finiteness to the left-hand side.

Everything is then assembled with the monotonicity lemma `setLIntegral_le_lintegral` for the
Lebesgue integral and `ENNReal.toReal_mono` for the passage back to the Bochner integral.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.GM.Affine

noncomputable section

/-- **Plancherel in `ℝ≥0∞` form.**  For a continuous compactly supported `g : ℝ → ℂ`,
`∫⁻ ξ, ENNReal.ofReal ‖𝓕 g ξ‖² = ∫⁻ x, ENNReal.ofReal ‖g x‖²`.

Contrary to the Bochner form (`plancherel_continuous`), this identity carries no integrability
conventions, so it can be used to *transfer finiteness* of the two sides. -/
lemma lintegral_ofReal_fourier_sq_eq (g : ℝ → ℂ) (hg : Continuous g) (hcs : HasCompactSupport g) :
    (∫⁻ ξ, ENNReal.ofReal (‖𝓕 g ξ‖ ^ 2)) = ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) := by
  have hgint : Integrable g volume := hg.integrable_of_hasCompactSupport hcs
  have hFcont : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hgint
  have hgnc : Continuous (fun x : ℝ => ‖g x‖ ^ 2) := by fun_prop
  have hFnc : Continuous (fun ξ : ℝ => ‖𝓕 g ξ‖ ^ 2) := by fun_prop
  -- both Bochner integrals, rewritten with `integral_eq_lintegral_of_nonneg_ae`
  have hA : ∫ x, ‖g x‖ ^ 2 = (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
      hgnc.aestronglyMeasurable
  have hB : ∫ ξ, ‖𝓕 g ξ‖ ^ 2 = (∫⁻ ξ, ENNReal.ofReal (‖𝓕 g ξ‖ ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ξ => sq_nonneg _)
      hFnc.aestronglyMeasurable
  have hpl : ∫ x, ‖g x‖ ^ 2 = ∫ ξ, ‖𝓕 g ξ‖ ^ 2 := plancherel_continuous g hg hcs
  have hto : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2)).toReal
      = (∫⁻ ξ, ENNReal.ofReal (‖𝓕 g ξ‖ ^ 2)).toReal := by rw [← hA, ← hB, hpl]
  -- the right-hand side is finite
  have hAne : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2)) ≠ ⊤ := by
    have hint : Integrable (fun x : ℝ => ‖g x‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp
        (hg.memLp_of_hasCompactSupport hcs)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  by_cases hBtop : (∫⁻ ξ, ENNReal.ofReal (‖𝓕 g ξ‖ ^ 2)) = ⊤
  · -- then the left-hand side is `0`, forcing `g = 0` a.e. and hence `𝓕 g = 0`, contradiction
    exfalso
    have hA0 : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2)) = 0 := by
      have h1 : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2)).toReal = 0 := by
        rw [hto, hBtop, ENNReal.toReal_top]
      rcases (ENNReal.toReal_eq_zero_iff _).mp h1 with h | h
      · exact h
      · exact absurd h hAne
    have hg0 : g =ᵐ[volume] (0 : ℝ → ℂ) := by
      have hae : (fun x : ℝ => ENNReal.ofReal (‖g x‖ ^ 2)) =ᵐ[volume] (0 : ℝ → ENNReal) :=
        (lintegral_eq_zero_iff' (hgnc.measurable.ennreal_ofReal).aemeasurable).mp hA0
      filter_upwards [hae] with x hx
      have hx0 : ‖g x‖ ^ 2 = 0 :=
        le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (sq_nonneg _)
      have hx1 : ‖g x‖ = 0 := by
        have h2 : ‖g x‖ * ‖g x‖ = 0 := by simpa [pow_two] using hx0
        exact mul_self_eq_zero.mp h2
      exact norm_eq_zero.mp hx1
    have hB0 : (∫⁻ ξ, ENNReal.ofReal (‖𝓕 g ξ‖ ^ 2)) = 0 := by
      have hf0 : ∀ ξ : ℝ, 𝓕 g ξ = 0 := by
        intro ξ
        rw [Real.fourier_congr_ae hg0 ξ, Real.fourier_eq]
        simp
      simp [hf0]
    rw [hB0] at hBtop
    exact ENNReal.top_ne_zero hBtop.symm
  · exact ((ENNReal.toReal_eq_toReal_iff' hAne hBtop).mp hto).symm

/-- The `ℝ≥0∞`-valued Lebesgue integral of `ofReal ‖g‖²` is finite for a continuous compactly
supported `g : ℝ → ℂ`. -/
lemma lintegral_ofReal_normSq_ne_top (g : ℝ → ℂ) (hg : Continuous g)
    (hcs : HasCompactSupport g) : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2)) ≠ ⊤ := by
  have hint : Integrable (fun x : ℝ => ‖g x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp
      (hg.memLp_of_hasCompactSupport hcs)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  exact ENNReal.ofReal_ne_top

theorem setIntegral_ghat_sq_le {K M₁ M₂ M₃ : ℝ} (hK : 0 < K) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (hb : 0 ≤ (∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2)) (s : Set ℝ) (hs : MeasurableSet s) :
    (∫ ξ in s, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2) ≤ ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2 := by
  -- the complexified majorant and its properties
  have hGc : Continuous (fun u : ℝ => ((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ)) :=
    continuous_gSum_complex K M₁ M₂ M₃ hf
  have hGcs : HasCompactSupport (fun u : ℝ => ((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ)) :=
    hasCompactSupport_gSum_complex K M₁ M₂ M₃ hM₁ hcs
  -- `ĝ` is continuous (Fourier transform of an `L¹` function)
  have hghatc : Continuous (fun ξ : ℝ => ghat K M₁ M₂ M₃ f ξ) := by
    have hgint : Integrable (fun u : ℝ => ((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ)) volume :=
      hGc.integrable_of_hasCompactSupport hGcs
    have h1 : Continuous (𝓕 (fun u : ℝ => ((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ))) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hgint
    exact h1.congr (fun ξ => rfl)
  have hFcont : Continuous (fun ξ : ℝ => ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2) := by fun_prop
  have hSqReal : Continuous (fun u : ℝ => gSum K M₁ M₂ M₃ f u) :=
    (Complex.continuous_re.comp hGc).congr (fun u => Complex.ofReal_re _)
  have hSqcont : Continuous (fun u : ℝ => (gSum K M₁ M₂ M₃ f u) ^ 2) := by fun_prop
  -- the two integrands, written as `ℝ≥0∞`-valued integrals
  have hconv : (∫⁻ u, ENNReal.ofReal ((gSum K M₁ M₂ M₃ f u) ^ 2))
      = (∫⁻ u, ENNReal.ofReal
          (‖(fun v : ℝ => ((gSum K M₁ M₂ M₃ f v : ℝ) : ℂ)) u‖ ^ 2)) :=
    lintegral_congr (fun u => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])
  have hghatF : (∫⁻ ξ, ENNReal.ofReal (‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2))
      = (∫⁻ ξ, ENNReal.ofReal
          (‖𝓕 (fun u : ℝ => ((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ)) ξ‖ ^ 2)) :=
    lintegral_congr (fun ξ => by simp only [ghat])
  -- Plancherel for the majorant, in `ℝ≥0∞` form
  have hPl : (∫⁻ ξ, ENNReal.ofReal (‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2))
      = (∫⁻ u, ENNReal.ofReal ((gSum K M₁ M₂ M₃ f u) ^ 2)) := by
    rw [hghatF, hconv]
    exact lintegral_ofReal_fourier_sq_eq _ hGc hGcs
  have hfinu : (∫⁻ u, ENNReal.ofReal ((gSum K M₁ M₂ M₃ f u) ^ 2)) ≠ ⊤ := by
    rw [hconv]
    exact lintegral_ofReal_normSq_ne_top _ hGc hGcs
  have hfini : (∫⁻ ξ, ENNReal.ofReal (‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)) ≠ ⊤ := by
    rw [hPl]; exact hfinu
  -- the two Bochner integrals in `ℝ≥0∞` form
  have hset : (∫ ξ in s, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      = (∫⁻ ξ in s, ENNReal.ofReal (‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ξ => sq_nonneg _)
      hFcont.aestronglyMeasurable.restrict
  have hfull : (∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2)
      = (∫⁻ u, ENNReal.ofReal ((gSum K M₁ M₂ M₃ f u) ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => sq_nonneg _)
      hSqcont.aestronglyMeasurable
  calc (∫ ξ in s, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      = (∫⁻ ξ in s, ENNReal.ofReal (‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)).toReal := hset
    _ ≤ (∫⁻ ξ, ENNReal.ofReal (‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)).toReal :=
        ENNReal.toReal_mono hfini (setLIntegral_le_lintegral s _)
    _ = (∫⁻ u, ENNReal.ofReal ((gSum K M₁ M₂ M₃ f u) ^ 2)).toReal := by rw [hPl]
    _ = ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2 := hfull.symm

end

end Work.GM.Affine
