import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Submission.Work.BoseFixR.LatGreen.W1funDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.W1fun_chat_small`

The Fourier transform of the renormalised kernel `W₁ = W1fun v h ℓ` (FS §4) vanishes at
infinity: for every `θ > 0` there is a radius `P > 0` beyond which `|Ŵ₁(p)| ≤ θ`, where
`Ŵ₁ = Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)` in the corpus's `p`-convention
(`chat W p = ∫ e^{-i⟪p,y⟫} W(y) dy`, the real part of `kinFT`).

This is the **Riemann–Lebesgue lemma** in the corpus's Fourier convention, applied to an
*arbitrary* real function `W` on `ℝ³`: no integrability, no support, no positivity
hypothesis on `W` is needed, because Mathlib's
`tendsto_integral_exp_inner_smul_cocompact` has none either — when the function is not
integrable both sides of the identification are the junk value `0`, which is of course
equally small.  (In particular `W1fun v h ℓ = wScaled ℓ (g0 v h)` is *not* in general
`L¹` without the dilute-regime hypotheses `supp v ⊆ ball 0 R`, `R ≤ ℓ·chiR0`; the
statement below needs none of them.)

Two ingredients:

* `Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`: `kinFT g p = 𝓕 g ((2π)⁻¹ • p)`, i.e.
  the change of variable `w = (2π)⁻¹ • p` between the corpus's and Mathlib's
  normalisations of the Fourier transform (both being `∫ e^{-i⟪p,y⟫}·`);
* the extraction of a *radius* from convergence along the `cocompact` filter
  (`exists_norm_le_of_tendsto_cocompact`), via
  `comap_dist_left_atTop_eq_cocompact : comap (dist 0) atTop = cocompact ℝ³`.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory Filter
open scoped Topology

/-- **Riemann–Lebesgue for the corpus's `chat`.**  For every real function `W` on `ℝ³`
(integrable or not — in the latter case `chat W` is the junk function `0`), the
`p`-convention Fourier transform `p ↦ Ŵ(p)` tends to `0` at infinity.

Mathlib's Riemann–Lebesgue lemma (`tendsto_integral_exp_inner_smul_cocompact`, which
carries no integrability hypothesis) is stated exactly for the integrand of `𝓕`; reading
it through `kinFT_eq_fourier` and reparametrising `w = (2π)⁻¹ • p` gives the claim. -/
theorem tendsto_chat_cocompact (W : ℝ³ → ℝ) :
    Tendsto (fun p : ℝ³ => Work.BoseFixR.chat W p) (cocompact ℝ³) (𝓝 0) := by
  have hc : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
  -- Mathlib's Riemann–Lebesgue lemma for the `ℂ`-valued function `fun y => (W y : ℂ)`
  have hRL : Tendsto (fun w : ℝ³ => (FourierTransform.fourier
      (fun y : ℝ³ => ((W y : ℝ) : ℂ)) w).re) (cocompact ℝ³) (𝓝 0) := by
    have h := (Complex.continuous_re.tendsto (0 : ℂ)).comp
      (tendsto_integral_exp_inner_smul_cocompact (fun y : ℝ³ => ((W y : ℝ) : ℂ)))
    simpa only [Function.comp_def, Real.fourier_eq, Complex.zero_re] using h
  -- the reparametrisation `p ↦ (2π)⁻¹ • p` is a cocompact self-map of `ℝ³`
  have hφ : Tendsto (fun p : ℝ³ => (2 * Real.pi)⁻¹ • p) (cocompact ℝ³) (cocompact ℝ³) := by
    refine tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℝ³) ?_
    have h1 : Tendsto (fun p : ℝ³ => dist (0 : ℝ³) p) (cocompact ℝ³) atTop :=
      tendsto_dist_left_cocompact_atTop 0
    refine (h1.const_mul_atTop hc).congr' (Eventually.of_forall fun p => ?_)
    simp only [dist_eq_norm, sub_zero, zero_sub, norm_neg]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have h3 : Tendsto (fun p : ℝ³ => (FourierTransform.fourier
      (fun y : ℝ³ => ((W y : ℝ) : ℂ)) ((2 * Real.pi)⁻¹ • p)).re) (cocompact ℝ³) (𝓝 0) := by
    simpa only [Function.comp_def] using hRL.comp hφ
  -- identify `chat W p` with the reparametrised Mathlib transform
  refine h3.congr' (Eventually.of_forall fun p => ?_)
  simp only [Work.BoseFixR.chat, Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]

/-- From convergence to `0` along `cocompact` of a real function `g` on `ℝ³`, extract a
radius `P > 0` beyond which `|g| ≤ θ`. -/
theorem exists_norm_le_of_tendsto_cocompact {g : ℝ³ → ℝ}
    (hg : Tendsto g (cocompact ℝ³) (𝓝 0)) {θ : ℝ} (hθ : 0 < θ) :
    ∃ P : ℝ, 0 < P ∧ ∀ p : ℝ³, P ≤ ‖p‖ → |g p| ≤ θ := by
  have h1 : ∀ᶠ p in cocompact ℝ³, |g p| ≤ θ := by
    have h2 : ∀ᶠ p in cocompact ℝ³, dist (g p) 0 < θ := (Metric.tendsto_nhds.mp hg) θ hθ
    refine h2.mono fun p hp => ?_
    have hp' : |g p| < θ := by simpa [Real.dist_eq] using hp
    exact le_of_lt hp'
  -- `cocompact ℝ³ = comap (dist 0) atTop`, so `∀ᶠ p in cocompact, ·` is
  -- `∃ a, ∀ b ≥ a, ∀ p, dist 0 p = b → ·`
  rw [← comap_dist_left_atTop_eq_cocompact (0 : ℝ³), Filter.eventually_comap,
    Filter.eventually_atTop] at h1
  obtain ⟨a, ha⟩ := h1
  refine ⟨max a 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro p hp
  have hp' : a ≤ ‖p‖ := le_trans (le_max_left _ _) hp
  exact ha ‖p‖ hp' p (by simp only [dist_eq_norm, zero_sub, norm_neg])

theorem W1fun_chat_small {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {ℓ : ℝ}
    (hℓ : 0 < ℓ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ P : ℝ, 0 < P ∧ ∀ p : EuclideanSpace ℝ (Fin 3), P ≤ ‖p‖ →
      |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| ≤ θ := by
  exact exists_norm_le_of_tendsto_cocompact
    (tendsto_chat_cocompact (Work.BoseFixR.W1fun v h ℓ)) hθ

end Work.BoseBoxFock.PCFU
