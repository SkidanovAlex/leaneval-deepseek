import Mathlib
import Submission.Work.KMTAreas.MSW_toolbox

/-!
# `MSW` integrability of the pieces

Integrability on the circle of `periodize φ` (for a Schwartz symbol supported in a short arc), of
the IW symbol built from it, and of the IW symbol times a trigonometric polynomial.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators ENNReal NNReal FourierTransform
open MeasureTheory

namespace Work.KMTAreas

/-- `periodize φ` is integrable on the circle for a Schwartz symbol supported in a short arc. -/
theorem msw_periodize_integrable {k : ℤ} {Q : ℕ} (hQ : 1 ≤ Q)
    (hk : (2 : ℝ) ^ k * (2 * (Q : ℝ)) ≤ 1) {φ : SchwartzMap ℝ ℂ}
    (hφ : ∀ x, φ x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k) :
    Integrable (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ))
      Work.Analysis.IonescuWainger.circleMeasure := by
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hφ' : ∀ x : ℝ, φ x ≠ 0 → x ∈ Set.Icc (-(2 : ℝ) ^ k) ((2 : ℝ) ^ k) := by
    intro x hx
    rw [Work.Analysis.IonescuWainger.realArc] at hφ
    exact hφ x hx
  have h0 : ∀ x : ℝ, (2 : ℝ) ^ k < |x| → (φ : ℝ → ℂ) x = 0 := by
    intro x hx
    by_contra hne
    have hle : |x| ≤ (2 : ℝ) ^ k := abs_le.mpr (hφ' x hne)
    linarith
  refine (Work.Analysis.IonescuWainger.memLp_periodize φ.continuous.measurable
    h2k.le h0 (fun x => SchwartzMap.norm_le_seminorm ℂ φ x)).integrable le_top

/-- The IW symbol of an integrable symbol on the circle is integrable. -/
theorem msw_symbol_integrable {A : Finset mswCircle} {Φ : mswCircle → ℂ}
    (hΦ : Integrable Φ Work.Analysis.IonescuWainger.circleMeasure) :
    Integrable (Work.Analysis.IonescuWainger.iwSymbolSet A Φ)
      Work.Analysis.IonescuWainger.circleMeasure := by
  show Integrable (fun τ : mswCircle => ∑ α ∈ A, Φ (τ - α))
    Work.Analysis.IonescuWainger.circleMeasure
  exact integrable_finsetSum A fun α _ => hΦ.comp_sub_right α

set_option maxHeartbeats 2000000 in
/-- The pairing identity in the form in which it is applied: the pairing of the IW convolution
with a finitely supported test sequence is the circle integral of the symbol times the
trigonometric polynomials. -/
theorem msw_pairing_eq_conv {A : Finset mswCircle} {Φ : mswCircle → ℂ}
    (hΦ : Integrable (Work.Analysis.IonescuWainger.iwSymbolSet A Φ)
      Work.Analysis.IonescuWainger.circleMeasure)
    {s t : Finset ℤ} {f g : ℤ → ℂ} (hs : ∀ m, m ∉ s → f m = 0) (ht : ∀ m, m ∉ t → g m = 0) :
    tsum (fun n : ℤ => Work.Analysis.IWMultiplier.iwConv A Φ f n * starRingEnd ℂ (g n))
      = ∫ τ : mswCircle, (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) τ
          * (mswTrigC s f τ * starRingEnd ℂ (mswTrigC t g τ))
        ∂Work.Analysis.IonescuWainger.circleMeasure := by
  have h := msw_pairing_eq (Ψ := Work.Analysis.IonescuWainger.iwSymbolSet A Φ) hΦ hs ht
  simpa only [Work.Analysis.IWMultiplier.iwConv] using h

end Work.KMTAreas
