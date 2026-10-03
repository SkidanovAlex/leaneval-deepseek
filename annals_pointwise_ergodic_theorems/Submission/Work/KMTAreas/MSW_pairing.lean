import Mathlib
import Submission.Work.KMTAreas.MSW_integrable
import Submission.Work.KMTAreas.MSW_interp_bound
import Submission.Work.KMTAreas.MSW_dual_pairing
import Submission.Work.KMTAreas.MSW_dual_pairing_one

/-!
# `MSW` single-torsion sampling: the pairing bound

The pairing bound for the single-torsion Ionescu–Wainger projection, together with the finiteness
of the `ℓ^p` norm of a finitely supported sequence.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators ENNReal NNReal FourierTransform
open MeasureTheory

namespace Work.KMTAreas

open Work.Analysis.IWMultiplier

/-- Finitely supported sequences vanish off their support (as a `Finset`). -/
theorem msw_support_zero {f : ℤ → ℂ} (hf : (Function.support f).Finite) :
    ∀ m, m ∉ hf.toFinset → f m = 0 :=
  fun m hm => by by_contra h; exact hm ((Set.Finite.mem_toFinset hf).mpr h)

/-- A finitely supported sequence has finite `ℓ^p` norm for `p < ⊤`. -/
theorem msw_eLpNorm_lt_top {p : ENNReal} (hp1 : 1 ≤ p) (hp2 : p < ⊤) {f : ℤ → ℂ}
    (hf : (Function.support f).Finite) : eLpNorm f p Measure.count < ⊤ := by
  have hp0 : p ≠ 0 := by positivity
  have hqpos : 0 < p.toReal := ENNReal.toReal_pos hp0 (ne_of_lt hp2)
  rw [← ENNReal.ofReal_toReal (ne_of_lt hp2),
    MSW_finsupp_eLpNorm (s := hf.toFinset) (msw_support_zero hf) hqpos]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt ?_)
  refine ENNReal.sum_lt_top.mpr fun n _ => ?_
  exact ENNReal.rpow_lt_top_of_nonneg (le_of_lt hqpos) (enorm_ne_top)

/-- `ENNReal.ofReal` of the `NNReal`-truncation of a finite extended nonnegative real. -/
theorem msw_ofReal_toNNReal {a : ENNReal} (ha : a < ⊤) :
    ENNReal.ofReal ((a.toNNReal : ℝ)) = a := by
  rw [show ((a.toNNReal : ℝ)) = ((a.toNNReal : ℝ≥0) : ℝ) from rfl, ENNReal.ofReal_coe_nnreal,
    ENNReal.coe_toNNReal (ne_of_lt ha)]

/-- **The pairing bound (raw form).**  For finitely supported `f, g` the pairing of the
single-torsion projection with `g` is bounded by `Q · M · CK² · ‖f‖_{ℓ^p} ‖g‖_{ℓ^r}`. -/
theorem msw_pairing_bound_aux {Q : ℕ} (hQ : 1 ≤ Q) {k : ℤ}
    (hk : (2 : ℝ) ^ k * (2 * (Q : ℝ)) ≤ 1)
    {φ : SchwartzMap ℝ ℂ}
    (hφ : ∀ x, φ x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k)
    {p r : ENNReal} (hpr : p.HolderConjugate r) (hp1 : 1 ≤ p) (hr1 : 1 ≤ r)
    {M : NNReal} (hM : IsLqMultiplierBound p (φ : ℝ → ℂ) M)
    {CK : NNReal} (hCK : ∀ (q : ENNReal), 1 ≤ q → ∀ (s : Finset ℤ) (u : ℤ → ℂ),
      (∀ m, m ∉ s → u m = 0) →
      eLpNorm (fun y : ℝ => ∑ m ∈ s, u m * mswK (y + m)) q volume
        ≤ ENNReal.ofReal (CK : ℝ) * eLpNorm u q Measure.count)
    {f g : ℤ → ℂ} {s t : Finset ℤ} (hs : ∀ m, m ∉ s → f m = 0)
    (ht : ∀ m, m ∉ t → g m = 0) :
    enorm (tsum (fun n : ℤ => Work.Analysis.IWMultiplier.iwConv (iwDenomFreqs {Q})
        (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ)) f n * starRingEnd ℂ (g n)))
      ≤ ENNReal.ofReal ((Q : ℝ) * (M : ℝ) * (CK : ℝ) * (CK : ℝ))
          * eLpNorm f p Measure.count * eLpNorm g r Measure.count := by
  classical
  set A : Finset mswCircle := iwDenomFreqs {Q} with hA
  set Φ : mswCircle → ℂ := Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ) with hΦdef
  have hΦint : Integrable Φ Work.Analysis.IonescuWainger.circleMeasure := by
    rw [hΦdef]
    exact msw_periodize_integrable hQ hk hφ
  have hΨint : Integrable (Work.Analysis.IonescuWainger.iwSymbolSet A Φ)
      Work.Analysis.IonescuWainger.circleMeasure := msw_symbol_integrable hΦint
  change enorm (tsum (fun n : ℤ => (∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j • f (n - j)) * starRingEnd ℂ (g n)))
      ≤ ENNReal.ofReal ((Q : ℝ) * (M : ℝ) * (CK : ℝ) * (CK : ℝ))
          * eLpNorm f p Measure.count * eLpNorm g r Measure.count
  rw [msw_pairing_eq (Ψ := Work.Analysis.IonescuWainger.iwSymbolSet A Φ) hΨint hs ht]
  have hsym : Work.Analysis.IonescuWainger.iwSymbolSet A Φ
      = fun τ : mswCircle => ∑ a ∈ Finset.range Q,
          Φ (τ - (((a : ℝ) / (Q : ℝ) : ℝ) : mswCircle)) := by
    rw [hA, hΦdef]
    exact MSW_symbol_sum Q hQ (φ : ℝ → ℂ)
  rw [hsym]
  simp only []
  simp only [Finset.sum_mul]
  have hInt : ∀ a ∈ Finset.range Q, Integrable (fun τ : mswCircle =>
      Φ (τ - (((a : ℝ) / (Q : ℝ) : ℝ) : mswCircle))
        * (mswTrigC s f τ * starRingEnd ℂ (mswTrigC t g τ)))
      Work.Analysis.IonescuWainger.circleMeasure := by
    intro a _
    have hb := (hΦint.comp_sub_right (((a : ℝ) / (Q : ℝ) : ℝ) : mswCircle)).bdd_mul
      ((mswTrigC_continuous s f).mul
        (Complex.continuous_conj.comp (mswTrigC_continuous t g))).aestronglyMeasurable
      (c := (∑ m ∈ s, ‖f m‖) * (∑ m ∈ t, ‖g m‖))
      (Filter.Eventually.of_forall fun τ => by
        simp only [Pi.mul_apply, Function.comp_apply, norm_mul, Complex.norm_conj]
        exact mul_le_mul (mswTrigC_norm_le s f τ) (mswTrigC_norm_le t g τ) (norm_nonneg _)
          (Finset.sum_nonneg fun m _ => norm_nonneg _))
    simpa [mul_comm] using hb
  rw [integral_finsetSum (Finset.range Q) hInt]
  refine le_trans (enorm_sum_le (Finset.range Q) (fun a => ∫ τ : mswCircle,
        Φ (τ - (((a : ℝ) / (Q : ℝ) : ℝ) : mswCircle))
          * (mswTrigC s f τ * starRingEnd ℂ (mswTrigC t g τ))
        ∂Work.Analysis.IonescuWainger.circleMeasure)) ?_
  refine le_trans (Finset.sum_le_sum fun a _ =>
    msw_term_bound hQ hk hφ hpr hp1 hr1 hM hCK hs ht a) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [show ((Q : ℝ) * (M : ℝ) * (CK : ℝ) * (CK : ℝ))
      = (Q : ℝ) * ((M : ℝ) * (CK : ℝ) * (CK : ℝ)) from by ring,
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Q : ℝ)), ENNReal.ofReal_natCast]
  exact le_of_eq (by ac_rfl)

end Work.KMTAreas
