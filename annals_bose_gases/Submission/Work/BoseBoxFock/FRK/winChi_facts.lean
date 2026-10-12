import Mathlib.Tactic.Have
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseBoxFock.FRK.kinFT_inv
import Submission.Work.BoseBoxFock.FRK.windowState
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.winChi_facts` — the standard facts about the FRK window `χ_Λ`

`winChi ℓ = χ_Λ` is the (complexified) smooth bump `Submission.BoseGases.chiScale ℓ` of the
corpus: the localisation window of the FRK chapter.  This module collects, in one place, the
four facts every frequency-space argument about it uses:

* `Continuous (winChi ℓ)` and `HasCompactSupport (winChi ℓ)` — the window is a `C^∞` bump;
* `Integrable (kinFT (winChi ℓ))` — its `p`-convention Fourier transform is rapidly decreasing
  (the window is smooth with compact support, so its transform is Schwartz);
* **Fourier inversion** — `winChi ℓ z = (2π)^{-3}∫_s e^{i⟪s,z⟫}·kinFT (winChi ℓ) s ds`.

The inversion is the corpus's `Work.BoseBoxFock.FRK.kinFT_inv` (Fourier inversion in the
`p`-convention), which needs `winChi ℓ ∈ L¹`, `𝓕(winChi ℓ) ∈ L¹` and continuity.  The analytic
input is that the window, being `C^∞` with compact support, is a Schwartz function: its Fourier
transform is then Schwartz, hence `L¹` (`SchwartzMap.integrable`), and the `p`-convention
transform is the rescaled Mathlib transform
(`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`), a change of variables which preserves `L¹`
(`MeasureTheory.Integrable.comp_smul`).

The auxiliary lemmas below are `private`: they are the technical steps of this one statement.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real FourierTransform SchwartzMap

namespace Work.BoseBoxFock.FRK

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Smoothness and compact support of the window -/

private lemma winChiFacts_support_subset (ℓ : ℝ) :
    Function.support (winChi ℓ) ⊆ Function.support (Submission.BoseGases.chiScale ℓ) := by
  intro z hz
  simp only [Function.mem_support] at hz ⊢
  intro h
  exact hz (by rw [winChi_apply, h]; simp)

/-- The window is the complexification of the scaled bump `chiScale ℓ`, hence `C^∞`. -/
private lemma winChiFacts_contDiff {ℓ : ℝ} (hℓ : ℓ ≠ 0) : ContDiff ℝ (⊤ : ℕ∞) (winChi ℓ) :=
  Complex.ofRealCLM.contDiff.comp (Submission.BoseGases.chiScale_contDiff hℓ)

private lemma winChiFacts_continuous {ℓ : ℝ} (hℓ : ℓ ≠ 0) : Continuous (winChi ℓ) :=
  (winChiFacts_contDiff hℓ).continuous

/-- The window is supported in the box `Λ`, hence has compact support. -/
private lemma winChiFacts_hasCompactSupport {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    HasCompactSupport (winChi ℓ) :=
  (Submission.BoseGases.chiScale_hasCompactSupport hℓ).mono (winChiFacts_support_subset ℓ)

/-! ## 2. The window as a Schwartz function -/

/-- The window, viewed as a Schwartz function (a `C^∞` function with compact support is
Schwartz). -/
private def winChiFactsSch (ℓ : ℝ) (hℓ : ℓ ≠ 0) : 𝓢(E3, ℂ) :=
  (winChiFacts_hasCompactSupport hℓ).toSchwartzMap (winChiFacts_contDiff hℓ)

private lemma winChiFactsSch_apply (ℓ : ℝ) (hℓ : ℓ ≠ 0) (z : E3) :
    (winChiFactsSch ℓ hℓ : E3 → ℂ) z = winChi ℓ z := by
  rw [winChiFactsSch]; rfl

/-- The corpus's `p`-convention Fourier transform of the window is Mathlib's Fourier transform of
its Schwartz version, evaluated at the rescaled frequency `(2π)⁻¹ • q`. -/
private lemma winChiFacts_kinFT_fourier (ℓ : ℝ) (hℓ : ℓ ≠ 0) (q : E3) :
    Submission.BoseGases.kinFT (winChi ℓ) q
      = (FourierTransform.fourier (winChiFactsSch ℓ hℓ) : E3 → ℂ) ((2 * Real.pi)⁻¹ • q) := by
  rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, SchwartzMap.fourier_coe]
  rfl

/-! ## 3. Integrability -/

private lemma winChiFacts_integrable {ℓ : ℝ} (hℓ : ℓ ≠ 0) : Integrable (winChi ℓ) :=
  (SchwartzMap.integrable (winChiFactsSch ℓ hℓ)).congr
    (Filter.Eventually.of_forall fun z => winChiFactsSch_apply ℓ hℓ z)

private lemma winChiFacts_integrable_fourier {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    Integrable (FourierTransform.fourier (winChi ℓ)) := by
  have hcoe : (FourierTransform.fourier (winChiFactsSch ℓ hℓ) : E3 → ℂ)
      = FourierTransform.fourier (winChi ℓ) := by
    rw [SchwartzMap.fourier_coe]
    exact congrArg FourierTransform.fourier (funext fun z => winChiFactsSch_apply ℓ hℓ z)
  exact (SchwartzMap.integrable (FourierTransform.fourier (winChiFactsSch ℓ hℓ))).congr
    (Filter.Eventually.of_forall fun z => congrFun hcoe z)

/-- The `p`-convention Fourier transform of the window is integrable: it is the Schwartz
transform of the window, rescaled by `(2π)⁻¹`. -/
private lemma winChiFacts_integrable_kinFT {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    Integrable (Submission.BoseGases.kinFT (winChi ℓ)) := by
  have h1 : Integrable ((FourierTransform.fourier (winChiFactsSch ℓ hℓ) : 𝓢(E3, ℂ)) : E3 → ℂ) :=
    SchwartzMap.integrable _
  have h2 : Integrable (fun p : E3 =>
      (FourierTransform.fourier (winChiFactsSch ℓ hℓ) : E3 → ℂ) ((2 * Real.pi)⁻¹ • p)) :=
    h1.comp_smul (R := (2 * Real.pi)⁻¹) (by positivity)
  exact h2.congr (Filter.Eventually.of_forall fun p =>
    (winChiFacts_kinFT_fourier ℓ hℓ p).symm)

/-! ## 4. The four facts -/

theorem winChi_facts {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Continuous (Work.BoseBoxFock.FRK.winChi ℓ)
      ∧ HasCompactSupport (Work.BoseBoxFock.FRK.winChi ℓ)
      ∧ MeasureTheory.Integrable (Submission.BoseGases.kinFT (Work.BoseBoxFock.FRK.winChi ℓ))
      ∧ (∀ z : EuclideanSpace ℝ (Fin 3),
          Work.BoseBoxFock.FRK.winChi ℓ z = (((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ) *
            MeasureTheory.integral MeasureTheory.volume
              (fun s : EuclideanSpace ℝ (Fin 3) =>
                Complex.exp (Complex.I * ((inner ℝ s z : ℝ) : ℂ)) *
                  Submission.BoseGases.kinFT (Work.BoseBoxFock.FRK.winChi ℓ) s)) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  refine ⟨winChiFacts_continuous hℓne, winChiFacts_hasCompactSupport hℓne,
    winChiFacts_integrable_kinFT hℓne, ?_⟩
  intro z
  exact kinFT_inv (f := winChi ℓ) (winChiFacts_integrable hℓne)
    (winChiFacts_integrable_fourier hℓne) (winChiFacts_continuous hℓne) z

end Work.BoseBoxFock.FRK
