import Mathlib
import Submission.Core.FullPeriod
import Submission.Core.LayerCake
import Submission.Core.WInterval
import Submission.Core.ConstIntegral
import Submission.Core.Endpoint

/-!
# D2: the single-arc (unimodality) bound -- STATEMENT + PROOF MAP

TARGET (R2, sharp, numerically validated incl. long arcs and the extremal
q = cos on a π-window giving equality in the limit):

    for a ≤ b, any UNIMODAL q : [a,b] → [0,1]:
        ∫_a^b log ‖1 - q(t)·e^{it}‖ dt ≥ -π log 2.

VALIDATED DECOMPOSITION (each piece is a separate standard step):

  G(t,q) := log‖1 - q e^{it}‖ = (1/2)log(1 - 2q cos t + q²),
  w_s(t) := ∂G/∂q at q=s = (s - cos t)/(1 - 2s cos t + s²).

  (L1) LAYER CAKE (Submission.Core.LayerCake.layer_cake): for any
       (continuous) q: [a,b]→[0,1],
         ∫_a^b G(t,q(t))dt = ∫_0^1 [∫_{t∈[a,b], q(t)>s} w_s(t) dt] ds.
       [Fubini + FTC in s; G(t,0)=0]
  (L2) UNIMODALITY ⇒ SUPERLEVELS ARE INTERVALS (order theory; tiny):
       for every s, J_s := {t∈[a,b] | q(t) > s} is an interval.
  (L3) PER-LEVEL PRIMITIVE BOUND (Submission.Core.WInterval.w_interval_lower):
       for 0 ≤ s < 1 with a := arccos s (so cos a = s, 0 ≤ a ≤ π/2), for
       EVERY interval [u,v]:
         ∫_u^v w_s(t)dt ≥ ∫_{-a}^{a} w_s(t)dt =: -C(s),   C(s) > 0.
       Proof: w_s is 2π-periodic even; its odd primitive W_s(t)=∫_0^t w_s
       is periodic (period mean 0) with max C(s)/2 at t ≡ -a and min
       -C(s)/2 at t ≡ a (w_s < 0 iff cos t > s iff |t-2πk| < a); hence
       ∫_u^v w_s = W_s(v) - W_s(u) ≥ -C(s).
  (L4) CONSTANT: ∫_0^1 C(s) ds = π log 2, because (swap the double
       integral over {0<s<cos t, |t|<π/2})
         ∫_0^1 C(s)ds = -∫_{-π/2}^{π/2} G(t, cos t) dt
                       = -∫_{-π/2}^{π/2} log|sin t| dt
                       = π log 2
       (uses Mathlib's integral_log_sin_zero_pi_div_two).
  ASSEMBLY: (L1) + (L2)+(L3) give ∫_a^b G(t,q(t))dt = ∫_0^1 P(s)ds ≥
       ∫_0^1(-C(s))ds = -π log 2.

Numerical validation (see /tmp): the constant is |interval|-independent;
random unimodal q (lengths up to 40) never beat -π log 2; q = cos on a
π-window at level → 1 approaches -π log 2 from above; NON-unimodal q
(cos₊ over two periods) reaches ≈ -2π log 2 < -π log 2, so the unimodality
hypothesis is essential (it is used exactly to make J_s an interval).
-/

noncomputable section

open scoped Real Complex
open Complex
open MeasureTheory
open Interval

namespace Submission.Core

/-- Real/imaginary parts of `E t`. -/
private lemma re_E' (t : ℝ) : (E t).re = Real.cos t := by
  dsimp [E]
  rw [Complex.exp_mul_I]
  rw [Complex.add_re, Complex.mul_re]
  rw [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  simp [Complex.ofReal_im, Complex.I_re, Complex.I_im]

/-- Real/imaginary parts of `E t`. -/
private lemma im_E' (t : ℝ) : (E t).im = Real.sin t := by
  dsimp [E]
  rw [Complex.exp_mul_I]
  rw [Complex.add_im, Complex.mul_im]
  rw [Complex.cos_ofReal_im, Complex.sin_ofReal_re]
  simp [Complex.ofReal_im, Complex.I_re, Complex.I_im]

/-- `‖1 - q·E t‖² = 1 - 2q cos t + q²`. -/
private lemma norm_sq_one_sub_poly (q t : ℝ) :
    ‖(1 : ℂ) - (q : ℂ) * E t‖ ^ 2 = 1 - 2 * q * Real.cos t + q ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_apply]
  have hzre : ((q : ℂ) * E t).re = q * Real.cos t := by
    rw [Complex.mul_re, re_E', im_E']
    simp
  have hzim : ((q : ℂ) * E t).im = q * Real.sin t := by
    rw [Complex.mul_im, re_E', im_E']
    simp
  have hre : ((1 : ℂ) - (q : ℂ) * E t).re = 1 - q * Real.cos t := by
    rw [Complex.sub_re, hzre]
    simp
  have him : ((1 : ℂ) - (q : ℂ) * E t).im = -(q * Real.sin t) := by
    rw [Complex.sub_im, hzim]
    simp
  rw [hre, him]
  have hsc : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
  nlinarith

/-- `log‖1 - q·E t‖ = (1/2)·log(1 - 2q cos t + q²)` (pointwise; the log-0
conventions agree at the isolated zeros). -/
private lemma log_norm_one_sub_eq (q t : ℝ) :
    Real.log ‖(1 : ℂ) - (q : ℂ) * E t‖ =
      (1 / 2 : ℝ) * Real.log (1 - 2 * q * Real.cos t + q ^ 2) := by
  have hx2 := norm_sq_one_sub_poly q t
  have hp : Real.log (‖(1 : ℂ) - (q : ℂ) * E t‖ ^ 2) =
      2 * Real.log ‖(1 : ℂ) - (q : ℂ) * E t‖ := by
    simpa using (Real.log_pow ‖(1 : ℂ) - (q : ℂ) * E t‖ 2)
  calc
    Real.log ‖(1 : ℂ) - (q : ℂ) * E t‖
        = (1 / 2 : ℝ) * (2 * Real.log ‖(1 : ℂ) - (q : ℂ) * E t‖) := by ring
    _ = (1 / 2 : ℝ) * Real.log (‖(1 : ℂ) - (q : ℂ) * E t‖ ^ 2) := by rw [hp]
    _ = (1 / 2 : ℝ) * Real.log (1 - 2 * q * Real.cos t + q ^ 2) := by rw [hx2]

/-- The `w_s` kernel in inline form (matches `WInterval`, `LayerCake` and
`ConstIntegral` conventions). -/
def wDs (s t : ℝ) : ℝ := (s - Real.cos t) / (1 - 2 * s * Real.cos t + s ^ 2)

/-- The layer-cake slice `P(s) = ∫_a^b (cut of w_s to {q > s})`. -/
noncomputable def Ps (a b : ℝ) (q : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in a..b, if s < q t then wDs s t else 0

/-- The window integral `W(s) = ∫_{-arccos s}^{arccos s} w_s`. -/
noncomputable def Ws (s : ℝ) : ℝ :=
  ∫ t in (-Real.arccos s)..Real.arccos s, wDs s t

/-- For `0 ≤ s < 1`, `wDs s` is continuous on every `[a,b]`. -/
lemma continuousOn_wDs {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (a b : ℝ) :
    ContinuousOn (fun t : ℝ => wDs s t) (Set.Icc a b) := by
  have hden : ∀ t : ℝ, (1 : ℝ) - 2 * s * Real.cos t + s ^ 2 ≠ 0 := by
    intro t
    have hrel : (1 - s) ^ 2 + 2 * s * (1 - Real.cos t) =
        1 - 2 * s * Real.cos t + s ^ 2 := by ring
    have h1 : 0 < (1 - s) ^ 2 := by
      apply sq_pos_of_ne_zero
      linarith
    have h2 : 0 ≤ 2 * s * (1 - Real.cos t) := by
      exact mul_nonneg (mul_nonneg (by norm_num) hs0) (sub_nonneg.mpr (Real.cos_le_one t))
    have hpos : 0 < 1 - 2 * s * Real.cos t + s ^ 2 := by
      rw [← hrel]
      nlinarith
    exact ne_of_gt hpos
  dsimp [wDs]
  exact (ContinuousOn.sub continuousOn_const Real.continuousOn_cos).div
    (by fun_prop : ContinuousOn (fun t : ℝ => 1 - 2 * s * Real.cos t + s ^ 2) (Set.Icc a b))
    (fun t ht => hden t)

/-- `W` is interval-integrable over `[0,1]` (it equals the `const_integral`
integrand, whose integral is the nonzero `-π log 2`). -/
lemma Ws_intervalIntegrable : IntervalIntegrable Ws volume 0 1 := by
  by_contra hWn
  have hzero : (∫ s in 0..1, Ws s) = 0 := intervalIntegral.integral_undef hWn
  have hc := const_integral
  have hc' : (∫ s in 0..1, Ws s) = -Real.pi * Real.log 2 := by
    simpa [Ws, wDs] using hc
  have hlt : -Real.pi * Real.log 2 < 0 := by
    have hπ : 0 < Real.pi := Real.pi_pos
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  exact (ne_of_lt hlt) (by linarith)

/-- **The single-arc (unimodality) bound (R2).**  For a continuous unimodal
`q : [a,b] → [0,1]`, `∫_a^b log‖1 - q(t)e^{it}‖ ≥ -π log 2`. -/
theorem unimodal_bound (a b : ℝ) (q : ℝ → ℝ)
    (hle : a ≤ b)
    (hq_cont : ContinuousOn q (Set.Icc a b))
    (hu : ∃ m : ℝ, UnimodalOn a b m q)
    (hq0 : ∀ t : ℝ, a ≤ t → t ≤ b → 0 ≤ q t)
    (hq1 : ∀ t : ℝ, a ≤ t → t ≤ b → q t ≤ 1) :
    (∫ t in a..b, Real.log ‖(1 : ℂ) - (q t : ℂ) * E t‖)
      ≥ -Real.pi * Real.log 2 := by
  classical
  -- (i) connect the ‖·‖-form to the real log-form
  have hLHS : (∫ t in a..b, Real.log ‖(1 : ℂ) - (q t : ℂ) * E t‖)
      = (∫ t in a..b, (1 / 2 : ℝ) * Real.log (1 - 2 * q t * Real.cos t + (q t) ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact log_norm_one_sub_eq (q t) t
  -- (ii) apply the layer cake
  have hqc2 : ContinuousOn q (Set.Icc (min a b) (max a b)) := by
    simpa [min_eq_left hle, max_eq_right hle] using hq_cont
  have hlc := layer_cake a b hle q hqc2 hq0 hq1
  -- per-level pointwise bound P(s) ≥ W(s) for s ∈ [0,1]
  have hlevel : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → Ps a b q s ≥ Ws s := by
    intro s hs0 hs1
    by_cases hslt : s < 1
    · -- 0 ≤ s < 1
      rcases superlevel_cut_interval a b s q (fun t : ℝ => wDs s t) hle hq_cont hu
        (continuousOn_wDs hs0 hslt a b) with ⟨l, r, hla, hlr, hrb, hcut⟩
      have hP : Ps a b q s = ∫ t in l..r, wDs s t := by
        dsimp [Ps]
        simpa using hcut
      have hWineq : (∫ t in l..r, wDs s t) ≥ Ws s := by
        have ha0 : 0 ≤ Real.arccos s := Real.arccos_nonneg s
        have hcos : Real.cos (Real.arccos s) = s :=
          Real.cos_arccos (by linarith) (by linarith)
        have hale : Real.arccos s ≤ Real.pi / 2 := (Real.arccos_le_pi_div_two).mpr hs0
        have hwl := w_interval_lower s (Real.arccos s) hs0 hslt ha0 hcos hale
        have hwl' : (∫ t in l..r, wDs s t) ≥
            (∫ t in (-Real.arccos s)..Real.arccos s, wDs s t) := by
          dsimp [wDs] at hwl ⊢
          exact hwl hlr
        simpa [Ws] using hwl'
      exact hP.trans_ge hWineq
    · -- s = 1: both sides vanish
      have hs_eq : s = 1 := le_antisymm hs1 (le_of_not_gt hslt)
      have hP1 : Ps a b q 1 = 0 := by
        dsimp [Ps]
        have hpf : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
            (if 1 < q t then wDs 1 t else 0) = 0 := by
          filter_upwards with t
          intro htI
          have htcc : t ∈ Set.Icc a b := by
            have hsub : Set.uIoc a b ⊆ Set.Icc a b := by
              intro x hx
              have hx' : x ∈ Set.Ioc a b := by
                simpa [Set.uIoc_of_le hle] using hx
              exact Set.mem_Icc.mpr ⟨le_of_lt hx'.1, hx'.2⟩
            exact hsub htI
          have hqle : q t ≤ 1 := hq1 t htcc.1 htcc.2
          have hnot : ¬ 1 < q t := by linarith
          simp [hnot]
        rw [intervalIntegral.integral_congr_ae hpf]
        simp
      have hW1 : Ws 1 = 0 := by
        dsimp [Ws]
        rw [Real.arccos_one]
        simp
      rw [hs_eq, hP1, hW1]
  -- integrate the pointwise bound over s ∈ [0,1]
  have hmono : (∫ s in 0..1, Ps a b q s) ≥ ∫ s in 0..1, Ws s := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
    · exact Ws_intervalIntegrable
    · convert (s_side_intervalIntegrable a b hle q hq_cont) using 1
      funext s
      dsimp [Ps, wDs]
    · intro s hs
      exact hlevel s hs.1 hs.2
  have hconst2 : (∫ s in 0..1, Ws s) = -Real.pi * Real.log 2 := by
    rw [← const_integral]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp [Ws, wDs]
  have htarget : (∫ s in 0..1, Ps a b q s) ≥ -Real.pi * Real.log 2 := by
    rw [hconst2] at hmono
    exact hmono
  -- assemble
  rw [hLHS]
  rw [hlc]
  simpa [Ps, wDs] using htarget

end Submission.Core

end
