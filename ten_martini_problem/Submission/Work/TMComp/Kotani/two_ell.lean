import Mathlib
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.mfun_props
import Submission.Work.TMComp.Kotani.mfun_im_shift

/-!
# (L2): `2 ℓ = ∫₀¹ log(1 + ε/im p)`

Here `ℓ = ell α lam E = ∫₀¹ log ‖m(E,x)‖ dx` and `p = pSec α lam E x = -1/m(E,x)`.

The proof is the pointwise identity (from the covariance relation and `mfun_im_shift`)

  `1 + ε/im p(x) = ‖m(x)‖² · im m(x+α) / im m(x)`,

whose logarithm is `2 log ‖m(x)‖ + log (im m(x+α)) - log (im m(x))`; the last two terms
cancel after integration because `x ↦ im m(x)` is `1`-periodic.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani

open Work.TMContract

/-- `im (-1/m) = im m / ‖m‖²`. -/
theorem pSec_im (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (x : ℝ) :
    (pSec α lam E x).im = (mfun α lam E x).im / ‖mfun α lam E x‖ ^ 2 := by
  have hm0 : mfun α lam E x ≠ 0 := by
    intro h0
    have h := MfunProbs.mfun_im_pos α lam hE x
    rw [h0] at h; simp at h
  have h1 : (-1 : ℂ) / mfun α lam E x = -((mfun α lam E x)⁻¹) := by ring
  rw [pSec, h1, Complex.neg_im, Complex.inv_im, Complex.normSq_eq_norm_sq]
  ring

/-- `im p(x) = im m(x+α) - Im E`. -/
theorem pSec_im_shift (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (x : ℝ) :
    (pSec α lam E x).im = (mfun α lam E (x + α)).im - E.im := by
  rw [pSec_im α lam E hE x]
  linarith [mfun_im_shift α lam E hE x]

/-- The key pointwise identity: `1 + Im E / im p = im m(x+α) · ‖m(x)‖² / im m(x)`. -/
theorem one_add_im_div_pSec (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (x : ℝ) :
    1 + E.im / (pSec α lam E x).im
      = (mfun α lam E (x + α)).im * ‖mfun α lam E x‖ ^ 2 / (mfun α lam E x).im := by
  have hm0 : mfun α lam E x ≠ 0 := by
    intro h0
    have h := MfunProbs.mfun_im_pos α lam hE x
    rw [h0] at h; simp at h
  have hb : 0 < (mfun α lam E x).im := MfunProbs.mfun_im_pos α lam hE x
  have hn : ‖mfun α lam E x‖ ≠ 0 := norm_ne_zero_iff.mpr hm0
  rw [pSec_im α lam E hE x, mfun_im_shift α lam E hE x]
  field_simp
  ring

/-- The pointwise log identity. -/
theorem log_pSec_eq (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (x : ℝ) :
    Real.log (1 + E.im / (pSec α lam E x).im)
      = 2 * Real.log ‖mfun α lam E x‖
        + (Real.log ((mfun α lam E (x + α)).im) - Real.log ((mfun α lam E x).im)) := by
  have ha : 0 < (mfun α lam E (x + α)).im := MfunProbs.mfun_im_pos α lam hE (x + α)
  have hb : 0 < (mfun α lam E x).im := MfunProbs.mfun_im_pos α lam hE x
  have hn : 0 < ‖mfun α lam E x‖ := norm_pos_iff.mpr (by
    intro h0
    rw [h0] at hb
    simp at hb)
  rw [one_add_im_div_pSec α lam E hE x]
  rw [Real.log_div (by positivity) (ne_of_gt hb),
      Real.log_mul (ne_of_gt ha) (by positivity),
      Real.log_pow]
  ring

theorem two_ell (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) :
    2 * Work.TMComp.Kotani.ell α lam E
      = ∫ x in (0 : ℝ)..1,
          Real.log (1 + E.im / (Work.TMComp.Kotani.pSec α lam E x).im) := by
  -- continuity of `x ↦ mfun α lam E x`
  have hm : Continuous (fun x : ℝ => mfun α lam E x) := by
    have hc := MfunProbs.mfun_continuousOn α lam
    have h2 : Continuous (fun x : ℝ => (E, x)) := continuous_const.prodMk continuous_id
    have hcomp := hc.comp_continuous h2 (fun x => hE)
    simpa [Function.comp_def] using hcomp
  have him : Continuous (fun x : ℝ => (mfun α lam E x).im) := Complex.continuous_im.comp hm
  have hm_a : Continuous (fun x : ℝ => mfun α lam E (x + α)) :=
    hm.comp (continuous_id.add continuous_const)
  have him_a : Continuous (fun x : ℝ => (mfun α lam E (x + α)).im) :=
    Complex.continuous_im.comp hm_a
  have hnorm : Continuous (fun x : ℝ => ‖mfun α lam E x‖) := continuous_norm.comp hm
  have hbpos : ∀ x : ℝ, 0 < (mfun α lam E x).im := fun x => MfunProbs.mfun_im_pos α lam hE x
  have hapos : ∀ x : ℝ, 0 < (mfun α lam E (x + α)).im :=
    fun x => MfunProbs.mfun_im_pos α lam hE (x + α)
  have hnpos : ∀ x : ℝ, 0 < ‖mfun α lam E x‖ := fun x =>
    norm_pos_iff.mpr (fun h0 => by have := hbpos x; rw [h0] at this; simp at this)
  have hlog_b : Continuous (fun x : ℝ => Real.log ((mfun α lam E x).im)) :=
    Real.continuousOn_log.comp_continuous him (fun x => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt (hbpos x))
  have hlog_a : Continuous (fun x : ℝ => Real.log ((mfun α lam E (x + α)).im)) :=
    Real.continuousOn_log.comp_continuous him_a (fun x => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt (hapos x))
  have hlog_n : Continuous (fun x : ℝ => Real.log ‖mfun α lam E x‖) :=
    Real.continuousOn_log.comp_continuous hnorm (fun x => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt (hnpos x))
  have hint_b : IntervalIntegrable (fun x : ℝ => Real.log ((mfun α lam E x).im)) volume 0 1 :=
    hlog_b.intervalIntegrable _ _
  have hint_a : IntervalIntegrable (fun x : ℝ => Real.log ((mfun α lam E (x + α)).im)) volume 0 1 :=
    hlog_a.intervalIntegrable _ _
  have hint_n : IntervalIntegrable (fun x : ℝ => Real.log ‖mfun α lam E x‖) volume 0 1 :=
    hlog_n.intervalIntegrable _ _
  -- periodicity of `x ↦ log (im m(x))`
  have hper : ∫ x in (0:ℝ)..1, Real.log ((mfun α lam E (x + α)).im)
      = ∫ x in (0:ℝ)..1, Real.log ((mfun α lam E x).im) := by
    have hperfun : Function.Periodic (fun x : ℝ => Real.log ((mfun α lam E x).im)) 1 := by
      intro x
      simp only
      rw [MfunProbs.mfun_period]
    rw [intervalIntegral.integral_comp_add_right
      (fun x : ℝ => Real.log ((mfun α lam E x).im)) α]
    simpa [zero_add, add_comm] using hperfun.intervalIntegral_add_eq α 0
  have hmain : ∫ x in (0:ℝ)..1, Real.log (1 + E.im / (pSec α lam E x).im)
      = 2 * ell α lam E := by
    rw [ell]
    calc ∫ x in (0:ℝ)..1, Real.log (1 + E.im / (pSec α lam E x).im)
        = ∫ x in (0:ℝ)..1, (2 * Real.log ‖mfun α lam E x‖
            + (Real.log ((mfun α lam E (x + α)).im)
                - Real.log ((mfun α lam E x).im))) :=
          intervalIntegral.integral_congr (fun x _ => log_pSec_eq α lam E hE x)
      _ = (∫ x in (0:ℝ)..1, 2 * Real.log ‖mfun α lam E x‖)
            + (∫ x in (0:ℝ)..1, (Real.log ((mfun α lam E (x + α)).im)
                - Real.log ((mfun α lam E x).im))) :=
          intervalIntegral.integral_add (hint_n.const_mul 2) (hint_a.sub hint_b)
      _ = (2 * (∫ x in (0:ℝ)..1, Real.log ‖mfun α lam E x‖))
            + ((∫ x in (0:ℝ)..1, Real.log ((mfun α lam E (x + α)).im))
                - ∫ x in (0:ℝ)..1, Real.log ((mfun α lam E x).im)) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hint_a hint_b]
      _ = (2 * (∫ x in (0:ℝ)..1, Real.log ‖mfun α lam E x‖)) + 0 := by rw [hper]; ring
      _ = 2 * (∫ x in (0:ℝ)..1, Real.log ‖mfun α lam E x‖) := by ring
  exact hmain.symm

end Work.TMComp.Kotani
