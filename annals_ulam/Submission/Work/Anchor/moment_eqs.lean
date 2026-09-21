import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddEnvelope.Defs
import Submission.Work.OddVolterra.Existence.setup_of_envelope
import Submission.Work.OddVolterra.Existence.theta_integrable
import Submission.Work.OddVolterra.RowIdentity.odd_rowF
import Submission.Work.OddVolterra.RowIdentity.odd_rowH
import Submission.Work.OddVolterra.Abel.abel_form_of_volterra_form
import Submission.Work.OddVolterra.Bridge.momentEqs_of_volterra
import Submission.Work.OddVolterra.Smooth.contDiffOn_momentF_sub
import Submission.Work.OddBridge.harik_of_curveData
import Submission.Work.OddBridge.contH_of_curveData
import Submission.Work.OddBridge.RowGlue

/-!
# The moment equations of the anchor slopes `(1/2, 1]`

This file proves `Work.Anchor.moment_eqs`: from the odd transition-slope Volterra system
`(hah44)` restricted to the anchor interval `(1/2, 1)`, the envelope-curve package and the
`C²`-closeness of the curve to the semicircle, the two moment equations hold on `(1/2, 1]`.

The proof is the localised form of the `Work.OddBridge` bridge.  Everything in the bridge is
already available *without* the `CurveData` structure, as long as one works on the anchor
interval:

* the two row identities `(t1)`, `(t2)` come from `Work.OddVolterra.RowIdentity.odd_rowF/odd_rowH`
  with the `Setup` built by `Work.OddVolterra.Existence.setup_of_envelope` at each slope
  individually (`a = c = s`), so only the envelope-curve package and the `1/100`-closeness are
  needed;
* the square-root denominators of the Abel kernels are positive on the anchor because the bump is
  bounded by `3/50` and its derivative by `3/5`
  (`Work.OddVolterra.Existence.abs_h_le`, `..._abs_deriv_h_le`, `..._Kden_pos_box`);
* the `Θ`-integrand is interval-integrable by
  `Work.OddVolterra.Existence.theta_deriv_parametrization_integrable` together with the
  manifest-kernel agreement `Work.OddVolterra.KernelExt.KvecM_eq_Kvec`;
* the Abel inversion `(arik)` is `Work.OddBridge.abel_inversion_continuous_endpoint`;
* the passage from the differentiated identities to the moment equations is the
  constant-of-integration argument, localised to `(1/2,1)`, with the initial values supplied on the
  tail `[1-τ,1]` (where `h` vanishes and the curve is the ball's).
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam (profileX semicircle)

namespace Work.Anchor

noncomputable section

variable {h x y : ℝ → ℝ}

/-! ## 1. The semicircle radicand on the section window

On the fixed window `(-profileX 1, profileX 1) ⊂ (-tStar, tStar)` the envelope profile *is* the
semicircle (`Work.OddEnvelope.envelopeProfile_eq_semicircle`), so the radicand with the semicircle
is positive wherever the radicand with the envelope profile is; the latter is positive on the
section by the concavity of the envelope (`Work.OddVolterra.Smooth.psi_semicircle_pos_of_envelope`).
The closed `t`-window needs the size of the bump: `|h| ≤ 3/50`. -/

/-- `1/√2 = profileX 1 ≤ 5/7`. -/
lemma profileX_one_le_five_sevenths : profileX 1 ≤ 5 / 7 := by
  have hsq : profileX 1 ^ 2 = (1 : ℝ) / 2 := by
    rw [Commons.Geometry.Ulam.profileX_sq]; norm_num
  have hpos : 0 < profileX 1 := Commons.Geometry.Ulam.profileX_pos 1 (by norm_num)
  nlinarith [sq_nonneg (profileX 1 - 5 / 7), hsq, hpos]

/-- **Positivity of the semicircle radicand on the section window**, from the envelope curve. -/
theorem hmid_semicircle_closed (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv profileX) s| ≤ 1 / 100 ∧
      |y s - profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv profileX) s| ≤ 1 / 100) :
    ∀ s ∈ Set.Ioo (0 : ℝ) 1, ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
      0 < Work.OddVolterra.psi h semicircle s t := by
  have hX1pos : 0 < profileX 1 := Commons.Geometry.Ulam.profileX_pos 1 (by norm_num)
  have hX1sq : profileX 1 ^ 2 = (1 : ℝ) / 2 := by
    rw [Commons.Geometry.Ulam.profileX_sq]; norm_num
  have hX1le : profileX 1 ≤ 5 / 7 := profileX_one_le_five_sevenths
  have hb : ∀ z : ℝ, |h z| ≤ 3 / 50 := Work.OddVolterra.Existence.abs_h_le hh H hclose
  intro s hs t ht
  have htabs : |t| ≤ 5 / 7 := by
    rw [abs_le]
    exact ⟨by linarith [ht.1, hX1le], by linarith [ht.2, hX1le]⟩
  have ht2 : t ^ 2 ≤ 1 / 2 := by
    have h' : |t| ≤ |profileX 1| := by rw [abs_of_pos hX1pos]; exact abs_le.mpr ht
    have h2 := sq_le_sq.mpr h'
    rwa [hX1sq] at h2
  have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
    have h1 := (abs_le.mp htabs).1
    have h2 := (abs_le.mp htabs).2
    constructor <;> linarith
  rw [Work.OddVolterra.psi, Work.OddVolterra.line,
    Commons.Geometry.Ulam.semicircle_sq_of_mem_Icc htIcc]
  rcases le_or_gt s (9 / 10) with hcase | hcase
  · have h1 : |s * t| ≤ (9 / 10) * (5 / 7) := by
      rw [abs_mul]
      exact mul_le_mul (by rw [abs_of_pos hs.1]; exact hcase) htabs (abs_nonneg _) (by norm_num)
    have hst : |s * t + h s| ≤ 9 / 14 + 3 / 50 := by
      calc |s * t + h s| ≤ |s * t| + |h s| := abs_add_le _ _
        _ ≤ (9 / 10) * (5 / 7) + 3 / 50 := add_le_add h1 (hb s)
        _ = 9 / 14 + 3 / 50 := by norm_num
    have h2 : (s * t + h s) ^ 2 ≤ (9 / 14 + 3 / 50) ^ 2 := by
      rw [sq_le_sq, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 14 + 3 / 50)]
      exact hst
    have h3 : (9 / 14 + 3 / 50 : ℝ) ^ 2 < 1 / 2 := by norm_num
    nlinarith [h2, h3, ht2, sq_nonneg t]
  · have hsz : h s = 0 := Work.OddVolterra.Existence.h_eq_zero_of_gt H hcase
    rw [hsz, add_zero]
    have hs2 : s ^ 2 < 1 := by nlinarith [hs.1, hs.2]
    nlinarith [ht2, hs2, sq_nonneg t]

/-! ## 2. The kinetic (manifest) kernel on the anchor box -/

/-- **The manifest kernel equals the paper's kernel on the anchor triangle.** -/
theorem kvecM_eq_kvec_anchor (n : ℕ) (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv profileX) s| ≤ 1 / 100 ∧
      |y s - profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv profileX) s| ≤ 1 / 100) :
    ∀ s σ : ℝ, 1 / 2 ≤ s → s ≤ σ → σ ≤ 1 →
      Work.OddBridge.KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)
        = Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ) := by
  obtain ⟨hposy, hposx⟩ :=
    Work.OddVolterra.Existence.Kden_pos_box (s := 1 / 2) (by norm_num) (by norm_num) hh H hclose
  intro s σ has hsσ hσ1
  have hs0 : 0 < s := by linarith
  have hσ0 : 0 < σ := lt_of_lt_of_le hs0 hsσ
  have hs1 : s ≤ 1 := le_trans hsσ hσ1
  have hR1 : 0 < (y σ + Work.OddVolterra.hquot h s σ) *
      (Work.OddVolterra.line h σ (y σ) + Work.OddVolterra.line h s (y σ)) :=
    Real.sqrt_pos.mp (hposy s σ ⟨by linarith, hs1⟩ ⟨by linarith, hσ1⟩)
  have hR2 : 0 < (-(x σ) + Work.OddVolterra.hquot h s σ) *
      (Work.OddVolterra.line h σ (-(x σ)) + Work.OddVolterra.line h s (-(x σ))) :=
    Real.sqrt_pos.mp (hposx s σ ⟨by linarith, hs1⟩ ⟨by linarith, hσ1⟩)
  exact Work.OddBridge.KvecM_eq_Kvec n hn hh hsσ (x σ) (y σ) (deriv x σ) (deriv y σ) hR1 hR2

/-- **Positivity of the Abel denominators on the anchor box.** -/
theorem Kden_pos_anchor_box (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv profileX) s| ≤ 1 / 100 ∧
      |y s - profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv profileX) s| ≤ 1 / 100) :
    (∀ s σ : ℝ, s ∈ Set.Icc (1 / 2) 1 → σ ∈ Set.Icc (1 / 2) 1 →
        0 < Work.OddVolterra.Kden h s σ (y σ)) ∧
    (∀ s σ : ℝ, s ∈ Set.Icc (1 / 2) 1 → σ ∈ Set.Icc (1 / 2) 1 →
        0 < Work.OddVolterra.Kden h s σ (-(x σ))) := by
  obtain ⟨hposy, hposx⟩ :=
    Work.OddVolterra.Existence.Kden_pos_box (s := 1 / 2) (by norm_num) (by norm_num) hh H hclose
  exact ⟨fun s σ hs hσ => hposy s σ ⟨by linarith [hs.1], hs.2⟩ ⟨by linarith [hσ.1], hσ.2⟩,
    fun s σ hs hσ => hposx s σ ⟨by linarith [hs.1], hs.2⟩ ⟨by linarith [hσ.1], hσ.2⟩⟩


/-- **Interval-integrability of the `Θ`-integrand on the anchor**

This is the anchor form of `Work.OddVolterra.Existence.theta_integrable`: the two moment
equations that the latter carries as (unused) hypotheses are dropped. -/
theorem theta_integrable_anchor (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv profileX) s| ≤ 1 / 100 ∧
      |y s - profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv profileX) s| ≤ 1 / 100) :
    ∀ s ∈ Set.Ioo (0:ℝ) 1,
      IntervalIntegrable (fun σ : ℝ =>
        Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) volume s 1 := by
  intro s hs
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hposy, hposx⟩ := Work.OddVolterra.Existence.Kden_pos_box hs0 hs1 hh H hclose
  -- the manifest kernel is `C²` on the square `[s/2,1]²`
  have hbox2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      Work.OddVolterra.KernelExt.KvecM n h p.1 p.2 (x p.2) (y p.2) (deriv x p.2) (deriv y p.2))
      (Set.Icc (s / 2) 1 ×ˢ Set.Icc (s / 2) 1) :=
    Work.OddVolterra.KernelExt.KvecM_contDiffOn_box n hh H.smooth_x H.smooth_y
      (by linarith) le_rfl hposy hposx
  have hGfun : ∀ i : Fin 2, ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      (Work.OddVolterra.KernelExt.KvecM n h p.1 p.2 (x p.2) (y p.2) (deriv x p.2)
        (deriv y p.2)) i) (Set.Icc (s / 2) 1 ×ˢ Set.Icc (s / 2) 1) := by
    intro i
    have h1 := hbox2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).contDiff.comp_contDiffOn
      h1).of_le (by norm_num)
  -- the last two rows of `ΘM`, via the parametric differentiation lemma
  have hrow : ∀ i : Fin 2, IntervalIntegrable (fun σ : ℝ => deriv (fun u : ℝ =>
      ∫ τ in (0 : ℝ)..1, (Work.OddVolterra.KernelExt.KvecM n h (u + τ * (σ - u)) σ
        (x σ) (y σ) (deriv x σ) (deriv y σ)) i / Real.sqrt (τ * (1 - τ))) s) volume s 1 :=
    fun i => Work.OddVolterra.Existence.theta_deriv_parametrization_integrable _ (hGfun i) hs0 hs1
  -- the manifest integrand is interval-integrable
  have hintM : IntervalIntegrable (fun σ : ℝ =>
      Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ))
      volume s 1 := by
    rw [intervalIntegrable_iff, uIoc_of_le hs1.le]
    have hiff : IntegrableOn (fun σ : ℝ =>
        Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ))
        (Set.Ioc s 1) volume ↔
        ∀ i : Fin 4, IntegrableOn (fun σ : ℝ =>
          (Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ)) i)
          (Set.Ioc s 1) volume := by
      show Integrable (fun σ : ℝ =>
          Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ))
          (volume.restrict (Set.Ioc s 1)) ↔
        ∀ i : Fin 4, Integrable (fun σ : ℝ =>
          (Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ)) i)
          (volume.restrict (Set.Ioc s 1))
      exact integrable_pi_iff
    rw [hiff]
    intro i
    fin_cases i
    · have hcont : ContinuousOn (fun σ : ℝ => -deriv x σ) (Set.uIcc s 1) := by
        refine ContinuousOn.neg ?_
        refine (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_x).continuousOn.mono ?_
        intro σ hσ
        exact lt_of_lt_of_le hs0 (by simpa [min_eq_left hs1.le] using hσ.1)
      refine (hcont.intervalIntegrable).1.congr_fun (fun σ _ => ?_) measurableSet_Ioc
      simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
    · have hcont : ContinuousOn (fun σ : ℝ => -deriv y σ) (Set.uIcc s 1) := by
        refine ContinuousOn.neg ?_
        refine (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_y).continuousOn.mono ?_
        intro σ hσ
        exact lt_of_lt_of_le hs0 (by simpa [min_eq_left hs1.le] using hσ.1)
      refine (hcont.intervalIntegrable).1.congr_fun (fun σ _ => ?_) measurableSet_Ioc
      simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
    · have hmain : IntervalIntegrable (fun σ : ℝ => -deriv (fun u : ℝ =>
          (Work.OddVolterra.KernelExt.G2M n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0) s)
          volume s 1 := (hrow 0).neg
      refine hmain.1.congr_fun (fun σ _ => ?_) measurableSet_Ioc
      simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
    · have hmain : IntervalIntegrable (fun σ : ℝ => -deriv (fun u : ℝ =>
          (Work.OddVolterra.KernelExt.G2M n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1) s)
          volume s 1 := (hrow 1).neg
      refine hmain.1.congr_fun (fun σ _ => ?_) measurableSet_Ioc
      simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
  -- `G2` and `G2M` agree eventually in the `u`-slot at `u = s`
  have hG2eq : ∀ (σ : ℝ) (i : Fin 2), σ ∈ Set.Ioo s 1 →
      (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i)
        =ᶠ[𝓝 s] (fun u : ℝ =>
          (Work.OddVolterra.KernelExt.G2M n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) := by
    intro σ i hσ
    filter_upwards [isOpen_Ioo.mem_nhds
      (show s ∈ Set.Ioo (s / 2) σ from ⟨by linarith, hσ.1⟩)] with u hu
    simp only [Work.OddVolterra.G2, Work.OddVolterra.KernelExt.G2M]
    refine intervalIntegral.integral_congr (fun τ hτ => ?_)
    have hτ0 : (0:ℝ) ≤ τ := by simpa using hτ.1
    have hτ1 : τ ≤ 1 := by simpa using hτ.2
    have hv : u + τ * (σ - u) ∈ Set.Icc (s / 2) 1 := by
      constructor
      · nlinarith [hu.1, hτ0, hτ1, hσ.1]
      · nlinarith [hu.2, hτ0, hτ1, hσ.2]
    have hσI : σ ∈ Set.Icc (s / 2) 1 := ⟨by linarith [hσ.1], hσ.2.le⟩
    have hR1 : 0 < (y σ + Work.OddVolterra.hquot h (u + τ * (σ - u)) σ) *
        (Work.OddVolterra.line h σ (y σ) + Work.OddVolterra.line h (u + τ * (σ - u)) (y σ)) :=
      Real.sqrt_pos.mp (hposy (u + τ * (σ - u)) σ hv hσI)
    have hR2 : 0 < (-(x σ) + Work.OddVolterra.hquot h (u + τ * (σ - u)) σ) *
        (Work.OddVolterra.line h σ (-(x σ))
          + Work.OddVolterra.line h (u + τ * (σ - u)) (-(x σ))) :=
      Real.sqrt_pos.mp (hposx (u + τ * (σ - u)) σ hv hσI)
    have hK := Work.OddVolterra.KernelExt.KvecM_eq_Kvec (s := u + τ * (σ - u)) (σ := σ)
      n hn hh (by nlinarith [hu.2, hτ0, hτ1]) (x σ) (y σ) (deriv x σ) (deriv y σ) hR1 hR2
    rw [hK]
  -- `Θ` and `ΘM` agree on the open interval
  have heq : Set.EqOn (fun σ : ℝ =>
      Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ))
      (fun σ : ℝ => Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ))
      (Set.Ioo s 1) := by
    intro σ hσ
    show Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)
      = Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ)
    funext i
    fin_cases i
    · simp [Work.OddVolterra.Theta, Work.OddVolterra.KernelExt.ThetaM,
        Work.OddVolterra.stateOf]
    · simp [Work.OddVolterra.Theta, Work.OddVolterra.KernelExt.ThetaM,
        Work.OddVolterra.stateOf]
    · show (Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 2
        = (Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ)) 2
      have h1 : (Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 2
          = -(deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (x σ) (y σ)
              (deriv x σ) (deriv y σ)) 0) s) := by
        simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
      have h2 : (Work.OddVolterra.KernelExt.ThetaM n h s σ
            (Work.OddVolterra.stateOf x y σ)) 2
          = -(deriv (fun u : ℝ => (Work.OddVolterra.KernelExt.G2M n h u σ (x σ) (y σ)
              (deriv x σ) (deriv y σ)) 0) s) := by
        simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
      rw [h1, h2]
      congr 1
      exact Filter.EventuallyEq.deriv_eq (hG2eq σ 0 hσ)
    · show (Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 3
        = (Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.stateOf x y σ)) 3
      have h1 : (Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 3
          = -(deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (x σ) (y σ)
              (deriv x σ) (deriv y σ)) 1) s) := by
        simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
      have h2 : (Work.OddVolterra.KernelExt.ThetaM n h s σ
            (Work.OddVolterra.stateOf x y σ)) 3
          = -(deriv (fun u : ℝ => (Work.OddVolterra.KernelExt.G2M n h u σ (x σ) (y σ)
              (deriv x σ) (deriv y σ)) 1) s) := by
        simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.stateOf]
      rw [h1, h2]
      congr 1
      exact Filter.EventuallyEq.deriv_eq (hG2eq σ 1 hσ)
  refine hintM.congr_uIoo ?_
  rw [Set.uIoo_of_le hs1.le]
  exact heq.symm




/-! ## 3. The two scalar rows `(dvi)` of the system -/

/-- The second component of the Volterra system, in scalar form (the paper's `(dvi)`, first row). -/
lemma row_zero_anchor (n : ℕ) {h x y : ℝ → ℝ} {s : ℝ}
    (hsys : Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s) =
      (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) +
        Work.OddVolterra.Xi n h s)
    (hintTheta : IntervalIntegrable
      (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) volume s 1) :
    - (Work.OddVolterra.G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) 0
      = - (∫ σ in s..1,
            deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0) s)
        + (Work.OddVolterra.Qtilde n h s) 0 := by
  have h2 : (Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s)) 2
      = ((∫ σ in s..1, Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) +
          Work.OddVolterra.Xi n h s) 2 := by rw [hsys]
  rw [Pi.add_apply] at h2
  have hG : (Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s)) 2
      = - (Work.OddVolterra.G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) 0 := by
    simp [Work.OddVolterra.Godd, Work.OddVolterra.stateOf]
  have hX : (Work.OddVolterra.Xi n h s) 2 = (Work.OddVolterra.Qtilde n h s) 0 := by
    simp [Work.OddVolterra.Xi]
  have hT : (∫ σ in s..1, Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 2
      = ∫ σ in s..1, - deriv (fun u : ℝ =>
          (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0) s := by
    rw [Work.OddBridge.intervalIntegral_apply_fin4 (i := 2) (h := hintTheta)]
    refine intervalIntegral.integral_congr (fun σ _ => ?_)
    simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
  rw [hG, hX, hT, intervalIntegral.integral_neg] at h2
  linarith [h2]

/-- The third component of the Volterra system, in scalar form (the paper's `(dvi)`, second row). -/
lemma row_one_anchor (n : ℕ) {h x y : ℝ → ℝ} {s : ℝ}
    (hsys : Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s) =
      (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) +
        Work.OddVolterra.Xi n h s)
    (hintTheta : IntervalIntegrable
      (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) volume s 1) :
    - (Work.OddVolterra.G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) 1
      = - (∫ σ in s..1,
            deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1) s)
        + (Work.OddVolterra.Qtilde n h s) 1 := by
  have h2 : (Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s)) 3
      = ((∫ σ in s..1, Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) +
          Work.OddVolterra.Xi n h s) 3 := by rw [hsys]
  rw [Pi.add_apply] at h2
  have hG : (Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s)) 3
      = - (Work.OddVolterra.G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) 1 := by
    simp [Work.OddVolterra.Godd, Work.OddVolterra.stateOf]
  have hX : (Work.OddVolterra.Xi n h s) 3 = (Work.OddVolterra.Qtilde n h s) 1 := by
    simp [Work.OddVolterra.Xi]
  have hT : (∫ σ in s..1, Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) 3
      = ∫ σ in s..1, - deriv (fun u : ℝ =>
          (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1) s := by
    rw [Work.OddBridge.intervalIntegral_apply_fin4 (i := 3) (h := hintTheta)]
    refine intervalIntegral.integral_congr (fun σ _ => ?_)
    simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
  rw [hG, hX, hT, intervalIntegral.integral_neg] at h2
  linarith [h2]

/-- **`(dvi)` for the anchor**: the two scalar rows of the system, in the manifest vocabulary. -/
theorem dvi_row_anchor (n : ℕ)
    (hsys : ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s) =
        (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) +
          Work.OddVolterra.Xi n h s)
    (hintTheta : ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1, IntervalIntegrable
      (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) volume s 1)
    (hae : ∀ s σ : ℝ, 1 / 2 ≤ s → s ≤ σ → σ ≤ 1 →
      Work.OddBridge.KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)
        = Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) :
    ∀ i : Fin 2, ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      - (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ *
          (Work.OddBridge.KvecM n h s s (x s) (y s) (deriv x s) (deriv y s)) i)
        + (∫ σ in s..1, deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
            (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ *
            (Work.OddBridge.KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) s)
      = deriv (fun u : ℝ => ∫ v in u..1,
          (Real.sqrt (v - u))⁻¹ * (Work.OddVolterra.Q n h v) i) s := by
  intro i s hs
  have hrow : - (Work.OddVolterra.G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) i
      = - (∫ σ in s..1,
            deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) s)
        + (Work.OddVolterra.Qtilde n h s) i := by
    fin_cases i
    · simpa using row_zero_anchor n (hsys s hs) (hintTheta s hs)
    · simpa using row_one_anchor n (hsys s hs) (hintTheta s hs)
  set T1 : ℝ := ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ *
    (Work.OddBridge.KvecM n h s s (x s) (y s) (deriv x s) (deriv y s)) i with hT1
  set T2 : ℝ := ∫ σ in s..1, deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
    (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ *
    (Work.OddBridge.KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) s with hT2
  set R : ℝ := deriv (fun u : ℝ => ∫ v in u..1,
    (Real.sqrt (v - u))⁻¹ * (Work.OddVolterra.Q n h v) i) s with hR
  have hdiag : (Work.OddVolterra.G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) i = T1 :=
    Work.OddBridge.G2_diag_eq n hae (le_of_lt hs.1) (le_of_lt hs.2) i
  have hsecond : (∫ σ in s..1,
        deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) s)
      = T2 := by
    refine intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs.2) (fun σ hσ => ?_)
    exact Work.OddBridge.G2_deriv_eq n hae hs.1 hσ.1 (le_of_lt hσ.2) i
  have hfunQ : (fun u : ℝ => ∫ v in u..1, (Work.OddVolterra.Q n h v) i / Real.sqrt (v - u))
      = fun u : ℝ => ∫ v in u..1, (Real.sqrt (v - u))⁻¹ * (Work.OddVolterra.Q n h v) i := by
    funext u
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [div_eq_mul_inv, mul_comm]
  have hQ : (Work.OddVolterra.Qtilde n h s) i = R := by
    have h1 : (Work.OddVolterra.Qtilde n h s) i = deriv (fun u : ℝ =>
        ∫ v in u..1, (Work.OddVolterra.Q n h v) i / Real.sqrt (v - u)) s := by
      fin_cases i <;> simp [Work.OddVolterra.Qtilde]
    rw [h1, hfunQ, hR]
  rw [hdiag, hsecond, hQ] at hrow
  linarith [hrow]

/-! ## 4. The Abel inversion `(arik)` on the anchor -/

/-- **Continuity of `Q n h` on the anchor interval.**  The two components of `Q` are
`-E1 + ∂^{n+1}(momentRHS)` and `-E2`, and `E1`, `E2` are continuous up to `s = 1`. -/
theorem q_cont_anchor (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv profileX) s| ≤ 1 / 100 ∧
      |y s - profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv profileX) s| ≤ 1 / 100) :
    ContinuousOn (Work.OddVolterra.Q n h) (Set.Icc (1 / 2) 1) := by
  have hmid := hmid_semicircle_closed hh H hclose
  obtain ⟨hE1, hE2⟩ := Work.OddVolterra.Smooth.E1_E2_continuousOn_Icc n hn hh hsupp hmid
    (a := 1 / 2) (by norm_num)
  have hmr : ContDiff ℝ (⊤ : ℕ∞) (Work.OddVolterra.momentRHS n) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => 1 + s ^ 2) := by fun_prop
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Real.sqrt (1 + s ^ 2)) :=
      ContDiff.sqrt h1 (fun x => by positivity)
    have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (Real.sqrt (1 + s ^ 2))⁻¹) :=
      ContDiff.inv h2 (fun x => by positivity)
    unfold Work.OddVolterra.momentRHS
    exact ContDiff.mul contDiff_const h3
  have hRHS : ContinuousOn
      (fun s : ℝ => iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) s)
      (Set.Icc (1 / 2) 1) := by
    have hcont : ContinuousOn (iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n))
        (Set.Icc (1 / 2) 1) := by
      rw [iteratedDeriv_eq_iterate]
      exact (ContDiff.iterate_deriv (n + 1) hmr).continuous.continuousOn
    exact hcont
  have h0 : ContinuousOn (fun y : ℝ => -Work.OddVolterra.E1 n h y +
      iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) y) (Set.Icc (1 / 2) 1) :=
    (hE1.neg.add hRHS).congr (fun y _ => by simp)
  have h1 : ContinuousOn (fun y : ℝ => -Work.OddVolterra.E2 n h y) (Set.Icc (1 / 2) 1) :=
    (hE2.neg).congr (fun y _ => by simp)
  rw [continuousOn_pi]
  intro i
  fin_cases i
  · convert h0 using 1
    funext y; simp [Work.OddVolterra.Q]
  · convert h1 using 1
    funext y; simp [Work.OddVolterra.Q]

/-- **The Abel system `(arik)` on `(1/2,1)`, from the system `(hah44)` on `(1/2,1)`.** -/
theorem harik_anchor (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv profileX) s| ≤ 1 / 100 ∧
      |y s - profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv profileX) s| ≤ 1 / 100)
    (hsys : ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s) =
        (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) +
          Work.OddVolterra.Xi n h s) :
    ∀ i : Fin 2, ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      (∫ σ in s..1, (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i /
          Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) i := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have hmid := hmid_semicircle_closed hh H hclose
  have hae := kvecM_eq_kvec_anchor n hn hh H hclose
  have hae_lt : ∀ s σ : ℝ, 1 / 2 ≤ s → s < σ → σ ≤ 1 →
      Work.OddBridge.KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)
        = Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ) :=
    fun s σ hs hsσ hσ1 => hae s σ hs (le_of_lt hsσ) hσ1
  have hintTheta : ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1, IntervalIntegrable
      (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) volume s 1 := by
    intro s hs
    exact theta_integrable_anchor n hn hh H hclose s ⟨lt_trans (by norm_num) hs.1, hs.2⟩
  have hdvi := dvi_row_anchor n hsys hintTheta hae
  have hQcont : ContinuousOn (Work.OddVolterra.Q n h) (Set.Icc (1 / 2) 1) :=
    q_cont_anchor n hn hh hsupp H hclose
  have hQcont_i : ∀ i : Fin 2, ContinuousOn (fun u : ℝ => (Work.OddVolterra.Q n h u) i)
      (Set.Icc (1 / 2) 1) := by
    intro i
    have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).continuous).comp_continuousOn hQcont
    simpa [Function.comp_def, ContinuousLinearMap.proj_apply] using h
  have hQsmooth_i : ∀ i : Fin 2, ∀ b : ℝ, (1 / 2 : ℝ) < b → b < 1 →
      ContDiffOn ℝ 2 (fun u : ℝ => (Work.OddVolterra.Q n h u) i) (Set.Icc (1 / 2) b) := by
    intro i b hab hb1
    have hsub : Set.Icc (1 / 2) b ⊆ Set.Ioo (0 : ℝ) 1 :=
      fun t ht => ⟨lt_of_lt_of_le (by norm_num) ht.1, lt_of_le_of_lt ht.2 hb1⟩
    have hQ : ContDiffOn ℝ (⊤ : ℕ∞) (Work.OddVolterra.Q n h) (Set.Icc (1 / 2) b) :=
      (Work.OddBridge.contDiffOn_Q_Ioo n hn hh hmid).mono hsub
    have hj : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Fin 2 → ℝ => v i) Set.univ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).contDiff.contDiffOn
    have hcomp := hj.comp hQ (fun u _ => Set.mem_univ _)
    refine (show ContDiffOn ℝ (⊤ : ℕ∞) (fun u : ℝ => (Work.OddVolterra.Q n h u) i)
      (Set.Icc (1 / 2) b) from ?_).of_le (WithTop.coe_le_coe.mpr le_top)
    simpa [Function.comp_def, ContinuousLinearMap.proj_apply] using hcomp
  have hbox : ∀ i : Fin 2, ContDiffOn ℝ 2
      (fun p : ℝ × ℝ => (Work.OddBridge.KvecM n h p.1 p.2 (x p.2) (y p.2)
        (deriv x p.2) (deriv y p.2)) i)
      (Set.Icc (1 / 2) 1 ×ˢ Set.Icc (1 / 2) 1) := by
    obtain ⟨hposy, hposx⟩ := Kden_pos_anchor_box hh H hclose
    have hb := Work.OddBridge.KvecM_contDiffOn_box (x := x) (y := y) n hh H.smooth_x H.smooth_y
      ha le_rfl hposy hposx
    intro i
    have hj : ContDiffOn ℝ 2 (fun v : Fin 2 → ℝ => v i) Set.univ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).contDiff.contDiffOn
    have hcomp := hj.comp hb (fun u _ => Set.mem_univ _)
    simpa [Function.comp_def, ContinuousLinearMap.proj_apply] using hcomp
  intro i s hs
  have habel := Work.OddBridge.abel_inversion_continuous_endpoint (E := ℝ)
    (K := fun s σ => (Work.OddBridge.KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i)
    (Q := fun s => (Work.OddVolterra.Q n h s) i) ha (hbox i) (hQcont_i i) (hQsmooth_i i) (by
      intro t ht
      have h := hdvi i t ht
      simpa only [smul_eq_mul] using h) s hs
  have hKi : (∫ σ in s..1, (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i /
        Real.sqrt (σ - s)) =
      (∫ σ in s..1, (Work.OddBridge.KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i /
        Real.sqrt (σ - s)) := by
    fin_cases i
    · exact (Work.OddBridge.abel_integral_Kvec_eq_KvecM n ha hae_lt (le_of_lt hs.1) (le_of_lt hs.2)).1
    · exact (Work.OddBridge.abel_integral_Kvec_eq_KvecM n ha hae_lt (le_of_lt hs.1) (le_of_lt hs.2)).2
  refine hKi.trans ?_
  exact (intervalIntegral.integral_congr
    (fun σ _ => by simp only [smul_eq_mul]; rw [div_eq_mul_inv, mul_comm])).trans habel



/-! ## 5. The two row identities `(t1)`, `(t2)` on the anchor -/

/-- **The first row identity `(t1)` on the anchor.** -/
theorem rowF_anchor (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv profileX) s| ≤ 1 / 100 ∧
      |y s - profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv profileX) s| ≤ 1 / 100) :
    ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      iteratedDeriv (n + 1)
        (fun u : ℝ => Work.OddVolterra.momentF n h x y
          (Work.OddEnvelope.envelopeProfile h x y) u) s =
        Work.OddVolterra.E1 n h s + ∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 /
            Real.sqrt (σ - s) := by
  intro s hs
  obtain ⟨S, hSn, hSa, hSc, hSh, hSx, hSy, hSf⟩ :=
    Work.OddVolterra.Existence.setup_of_envelope n hn hh H hclose
      (show (0 : ℝ) < s from by linarith [hs.1]) hs.2
  have hrow := Work.OddVolterra.RowIdentity.odd_rowF S.n S.hn S.ha S.hac S.hc1 S.hh S.hx S.hy
    S.hf S.hxy S.hxdec S.hydec S.hxb S.hyb S.hfb S.hxle S.hyle S.hord S.hint S.hKden S.hmid
    (s := s) (by simpa [hSa, hSc] using hs)
  simpa [hSn, hSh, hSx, hSy, hSf] using hrow

/-- **The second row identity `(t2)` on the anchor.** -/
theorem rowH_anchor (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv profileX) s| ≤ 1 / 100 ∧
      |y s - profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv profileX) s| ≤ 1 / 100) :
    ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      iteratedDeriv n
        (fun u : ℝ => Work.OddVolterra.momentH n h x y
          (Work.OddEnvelope.envelopeProfile h x y) u) s =
        Work.OddVolterra.E2 n h s + ∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 /
            Real.sqrt (σ - s) := by
  intro s hs
  obtain ⟨S, hSn, hSa, hSc, hSh, hSx, hSy, hSf⟩ :=
    Work.OddVolterra.Existence.setup_of_envelope n hn hh H hclose
      (show (0 : ℝ) < s from by linarith [hs.1]) hs.2
  have hrow := Work.OddVolterra.RowIdentity.odd_rowH S.n S.hn S.ha S.hac S.hc1 S.hh S.hx S.hy
    S.hf S.hxy S.hxdec S.hydec S.hxb S.hyb S.hfb S.hxle S.hyle S.hord S.hint S.hKden S.hmid
    (s := s) (by simpa [hSa, hSc] using hs)
  simpa [hSn, hSh, hSx, hSy, hSf] using hrow

/-! ## 6. The differentiated moment identities on the anchor -/

/-- **The differentiated first moment identity on the anchor**: `momentF - momentRHS` has
vanishing `(n+1)`-st derivative on `(1/2,1)`. -/
theorem hderF_anchor (n : ℕ) {h x y : ℝ → ℝ}
    (hcontF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Work.OddVolterra.momentF n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u - Work.OddVolterra.momentRHS n u)
      (Set.Ioo 0 1))
    (harik : ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      (∫ σ in s..1, (Work.OddVolterra.Kvec n h s σ (x σ) (y σ)
          (deriv x σ) (deriv y σ)) 0 / Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 0)
    (hrow : ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      iteratedDeriv (n + 1)
        (fun u : ℝ => Work.OddVolterra.momentF n h x y
          (Work.OddEnvelope.envelopeProfile h x y) u) s =
        Work.OddVolterra.E1 n h s + ∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 /
            Real.sqrt (σ - s)) :
    ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      iteratedDeriv (n + 1)
        (fun u : ℝ => Work.OddVolterra.momentF n h x y
          (Work.OddEnvelope.envelopeProfile h x y) u - Work.OddVolterra.momentRHS n u) s = 0 := by
  intro s hs
  have hs01 : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
  have hrow_s := hrow s hs
  have harik_s := harik s hs
  have hQ : (Work.OddVolterra.Q n h s) 0 =
      - Work.OddVolterra.E1 n h s + iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) s := by
    simp [Work.OddVolterra.Q]
  have hkey : iteratedDeriv (n + 1)
        (fun u : ℝ => Work.OddVolterra.momentF n h x y
          (Work.OddEnvelope.envelopeProfile h x y) u) s
      = iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) s := by
    rw [hrow_s, harik_s, hQ]; ring
  have hR : ContDiffAt ℝ (n + 1) (Work.OddVolterra.momentRHS n) s :=
    Work.OddVolterra.Bridge.contDiffAt_momentRHS n s
  have hG : ContDiffAt ℝ (n + 1)
      (fun u : ℝ => Work.OddVolterra.momentF n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u) s := by
    have h1 : ContDiffAt ℝ (n + 1)
        (fun u : ℝ => Work.OddVolterra.momentF n h x y
          (Work.OddEnvelope.envelopeProfile h x y) u - Work.OddVolterra.momentRHS n u) s := by
      apply (hcontF.contDiffAt (isOpen_Ioo.mem_nhds hs01)).of_le
      rw [← Nat.cast_add_one]
      exact WithTop.coe_le_coe.mpr le_top
    have h2 := h1.add hR
    simpa using h2
  have hsub := iteratedDeriv_sub (f := fun u : ℝ => Work.OddVolterra.momentF n h x y
      (Work.OddEnvelope.envelopeProfile h x y) u) (g := Work.OddVolterra.momentRHS n) hG hR
  change iteratedDeriv (n + 1)
    ((fun u : ℝ => Work.OddVolterra.momentF n h x y
      (Work.OddEnvelope.envelopeProfile h x y) u) - Work.OddVolterra.momentRHS n) s = 0
  rw [hsub, hkey, sub_self]

/-- **The differentiated second moment identity on the anchor**: `momentH` has vanishing
`n`-th derivative on `(1/2,1)`. -/
theorem hderH_anchor (n : ℕ) {h x y : ℝ → ℝ}
    (harik : ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      (∫ σ in s..1, (Work.OddVolterra.Kvec n h s σ (x σ) (y σ)
          (deriv x σ) (deriv y σ)) 1 / Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 1)
    (hrowH : ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      iteratedDeriv n
        (fun u : ℝ => Work.OddVolterra.momentH n h x y
          (Work.OddEnvelope.envelopeProfile h x y) u) s =
        Work.OddVolterra.E2 n h s + ∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 /
            Real.sqrt (σ - s)) :
    ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      iteratedDeriv n
        (fun u : ℝ => Work.OddVolterra.momentH n h x y
          (Work.OddEnvelope.envelopeProfile h x y) u) s = 0 := by
  intro s hs
  have hrowH_s := hrowH s hs
  have harik_s := harik s hs
  have hQ : (Work.OddVolterra.Q n h s) 1 = - Work.OddVolterra.E2 n h s := by
    simp [Work.OddVolterra.Q]
  rw [hrowH_s, harik_s, hQ]; ring

/-! ## 7. The moment identities on the tail `[1 - τ, 1]` -/

/-- **The two moment identities on the unperturbed tail**, for an envelope curve. -/
theorem moment_tail_anchor (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) :
    ∀ s ∈ Set.Icc (1 - Work.OddVolterra.tau) 1,
      Work.OddVolterra.momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) s
          = Work.OddVolterra.momentRHS n s ∧
      Work.OddVolterra.momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0 := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  have hx : Work.OddEnvelope.IsChordCurve x := H.toChordCurve_x
  have hy : Work.OddEnvelope.IsChordCurve y := H.toChordCurve_y
  have htail : ∀ u : ℝ, 1 - Work.OddVolterra.tau ≤ u → h u = 0 :=
    fun u hu => Work.OddBridge.h_eq_zero_of_tau_le hh hsupp hu
  have hspos : 0 < s := lt_of_lt_of_le Work.OddEnvelope.one_sub_tau_pos hs1
  have hxs : x s = Work.OddEnvelope.profileX s := H.x_tail s hs1
  have hys : y s = Work.OddEnvelope.profileX s := H.y_tail s hs1
  have hhs : h s = 0 := htail s hs1
  have hle : -(Work.OddEnvelope.profileX s) ≤ Work.OddEnvelope.profileX s := by
    linarith [Work.OddEnvelope.profileX_pos s]
  have hc_le : Work.OddEnvelope.profileX s ≤ Work.OddEnvelope.tStar :=
    Work.OddEnvelope.profileX_strictAntiOn.antitoneOn Work.OddEnvelope.one_sub_tau_pos hspos hs1
  have hInt : ∀ t ∈ Set.Icc (-(Work.OddEnvelope.profileX s)) (Work.OddEnvelope.profileX s),
      Work.OddEnvelope.envelopeProfile h x y t = Work.OddEnvelope.semicircle t := by
    intro t ht
    exact Work.OddVolterra.Bridge.envelopeProfile_eq_semicircle_of_tail hx hy htail
      ⟨by linarith [ht.1, hc_le], by linarith [ht.2, hc_le]⟩
  have hpsi : ∀ t ∈ Set.Icc (-(Work.OddEnvelope.profileX s)) (Work.OddEnvelope.profileX s),
      Work.OddVolterra.psi h (Work.OddEnvelope.envelopeProfile h x y) s t
        = Work.OddVolterra.psi (fun _ : ℝ => 0) Work.OddEnvelope.semicircle s t := by
    intro t ht
    show (Work.OddEnvelope.envelopeProfile h x y t) ^ 2 - (s * t + h s) ^ 2
        = (Work.OddEnvelope.semicircle t) ^ 2 - (s * t + 0) ^ 2
    rw [hInt t ht, hhs]
  have hderivh : deriv h s = 0 :=
    Work.OddVolterra.Bridge.deriv_eq_zero_of_eq_zero_on_Ici
      ((hh.differentiable (by simp)).differentiableAt) (fun t ht => htail t (le_trans hs1 ht))
  have hF : Work.OddVolterra.momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) s
      = Work.OddVolterra.momentF n (fun _ : ℝ => 0) Work.OddEnvelope.profileX
          Work.OddEnvelope.profileX Work.OddEnvelope.semicircle s := by
    unfold Work.OddVolterra.momentF Work.OddVolterra.momentIntegrand
    rw [hxs, hys]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    beta_reduce
    rw [hpsi t ht]
  have hH : Work.OddVolterra.momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) s
      = Work.OddVolterra.momentH n (fun _ : ℝ => 0) Work.OddEnvelope.profileX
          Work.OddEnvelope.profileX Work.OddEnvelope.semicircle s := by
    unfold Work.OddVolterra.momentH Work.OddVolterra.centroidIntegrand Work.OddVolterra.lineSlope
    rw [hxs, hys]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    beta_reduce
    simp only [hpsi t ht, hderivh, deriv_const, add_zero]
  exact ⟨by rw [hF]; exact Work.OddVolterra.ball_momentF n hspos,
    by rw [hH]; exact Work.OddVolterra.ball_momentH n hspos⟩

/-! ## 8. The constant-of-integration argument on `(1/2, 1)` -/

/-- **The constant-of-integration tool on the anchor interval.**  A `C^∞` function on `(1/2,1)`
whose `(n+1)`-st derivative vanishes on `(1/2,1)` and which vanishes near an interior point is
identically zero. -/
theorem eq_zero_of_iteratedDeriv_eq_zero_half (n : ℕ) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Set.Ioo (1 / 2 : ℝ) 1))
    (hd : ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1, iteratedDeriv (n + 1) F s = 0)
    {c : ℝ} (hc : c ∈ Set.Ioo (1 / 2 : ℝ) 1) (hz : F =ᶠ[𝓝 c] 0) :
    ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1, F s = 0 := by
  intro s hs
  have hmin : (1 / 2 : ℝ) < min s c := lt_min hs.1 hc.1
  have hp : (1 / 2 + min s c) / 2 < min s c := by linarith
  have hpc : (1 / 2 + min s c) / 2 < c := lt_of_lt_of_le hp (min_le_right s c)
  have hmax1 : max s c < 1 := max_lt hs.2 hc.2
  have hq : max s c < (1 + max s c) / 2 := by linarith
  have hqc : c < (1 + max s c) / 2 := lt_of_le_of_lt (le_max_right s c) hq
  have hpq : (1 / 2 + min s c) / 2 < (1 + max s c) / 2 := by
    linarith [min_le_max (a := s) (b := c)]
  have hsub : Set.Icc ((1 / 2 + min s c) / 2) ((1 + max s c) / 2) ⊆ Set.Ioo (1 / 2 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1, hp, min_le_left s c, hs.1], by linarith [hx.2, hq]⟩
  have hF' : ContDiffOn ℝ (n + 1) F
      (Set.Icc ((1 / 2 + min s c) / 2) ((1 + max s c) / 2)) := by
    apply (hF.mono hsub).of_le
    rw [← Nat.cast_add_one]
    exact WithTop.coe_le_coe.mpr le_top
  have hd' : ∀ x ∈ Set.Ioo ((1 / 2 + min s c) / 2) ((1 + max s c) / 2),
      iteratedDerivWithin (n + 1) F
        (Set.Icc ((1 / 2 + min s c) / 2) ((1 + max s c) / 2)) x = 0 := by
    intro x hx
    have hx' : x ∈ Set.Ioo (1 / 2 : ℝ) 1 := hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have huniq : UniqueDiffOn ℝ
        (Set.Icc ((1 / 2 + min s c) / 2) ((1 + max s c) / 2)) := uniqueDiffOn_Icc hpq
    have hcont : ContDiffAt ℝ (n + 1) F x := by
      apply (hF.contDiffAt (isOpen_Ioo.mem_nhds hx')).of_le
      rw [← Nat.cast_add_one]
      exact WithTop.coe_le_coe.mpr le_top
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq hcont ⟨le_of_lt hx.1, le_of_lt hx.2⟩]
    exact hd x hx'
  have hzv := Commons.Analysis.Calculus.eq_zero_of_iteratedDerivWithin_eq_zero_of_eventuallyEq_zero
    n hpc hqc hF' hd' hz
  exact hzv s ⟨by linarith [min_le_left s c, hs.1], by linarith [le_max_left s c, hs.2]⟩



/-- The two moment equations on the anchor slopes `(1/2,1]`, from the paper's system `(hah44)`
on `(1/2,1)` for the curve `(x,y)`.  Route: (i) `Work.OddVolterra.Abel.abel_form_of_volterra_form`
turns rows `2,3` of the system (which are `(dvi)`) into the Abel equation `(arik)`
`∫_s^1 Kvec/√(σ-s) = Q` on `(1/2,1)`; (ii) the row identities `(t1)`, `(t2)` are
`Work.OddVolterra.RowIdentity.odd_rowF` / `odd_rowH` with the `Setup` package, which
`Work.OddVolterra.Existence.setup_of_envelope` builds from `IsEnvelopeCurve` plus this
`C²`-closeness (copy its proof with the interval parameters `a`, `c`, `1/2 ≤ a ≤ c < 1`, so that
the identities hold on every `[a,c] ⊂ (1/2,1)`); (iii)
`Work.OddVolterra.Bridge.iteratedDeriv_momentF_sub_eq_zero_of_harik_hrow` (and the `..._momentH_`
analogue) gives `iteratedDeriv (n+1) (momentF - momentRHS) = 0`, and the constant-of-integration
statement `Work.OddVolterra.Bridge.eq_zero_of_iteratedDeriv_eq_zero_of_eventuallyEq_zero` should
be adapted from `(0,1)` to `(1/2,1)`, the initial values coming from the tail `[1-τ,1]` (there
`h` and all its derivatives vanish and the curve is the ball's, so the two expressions vanish;
re-derive the `CurveData`-based tail statement for `IsEnvelopeCurve` here); (iv) conclude on
`(1/2,1)` and extend to `s = 1` by continuity. -/
theorem moment_eqs (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hIC : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - Work.OddEnvelope.profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 100 ∧
      |y s - Work.OddEnvelope.profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 100)
    (hsystem : ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s) =
        (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) +
          Work.OddVolterra.Xi n h s) :
    (∀ s : ℝ, 1 / 2 < s → s ≤ 1 →
      Work.OddVolterra.momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
        Commons.Geometry.Ulam.oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2)) ∧
    (∀ s : ℝ, 1 / 2 < s → s ≤ 1 →
      Work.OddVolterra.momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0) := by
  have hcontF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Work.OddVolterra.momentF n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u - Work.OddVolterra.momentRHS n u)
      (Set.Ioo 0 1) :=
    Work.OddVolterra.Smooth.contDiffOn_momentF_sub n hn hIC
  have hcontH : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Work.OddVolterra.momentH n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u) (Set.Ioo 0 1) :=
    Work.OddBridge.contDiffOn_momentH_of_isEnvelopeCurve n hn hh hIC
  have hharik := harik_anchor n hn hh hsupp hIC hclose hsystem
  have hrowF := rowF_anchor n hn hh hIC hclose
  have hrowH := rowH_anchor n hn hh hIC hclose
  have hderF := hderF_anchor n hcontF (fun s hs => hharik 0 s hs) hrowF
  have hderH := hderH_anchor n (fun s hs => hharik 1 s hs) hrowH
  have htail := moment_tail_anchor n hn hh hsupp hIC
  -- the constant-of-integration step on `(1/2,1)`
  have hc : (1 - Work.OddVolterra.tau / 2) ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
    rw [Work.OddVolterra.tau]; norm_num
  have hc1 : 1 - Work.OddVolterra.tau < 1 - Work.OddVolterra.tau / 2 := by
    rw [Work.OddVolterra.tau]; norm_num
  have hc2 : 1 - Work.OddVolterra.tau / 2 < 1 := by
    rw [Work.OddVolterra.tau]; norm_num
  have hnbhd : Set.Icc (1 - Work.OddVolterra.tau) 1 ∈ 𝓝 (1 - Work.OddVolterra.tau / 2) :=
    Icc_mem_nhds hc1 hc2
  have hzF : (fun u : ℝ => Work.OddVolterra.momentF n h x y
      (Work.OddEnvelope.envelopeProfile h x y) u - Work.OddVolterra.momentRHS n u)
      =ᶠ[𝓝 (1 - Work.OddVolterra.tau / 2)] 0 := by
    filter_upwards [hnbhd] with u hu
    exact sub_eq_zero.mpr (htail u hu).1
  have hzH : (fun u : ℝ => Work.OddVolterra.momentH n h x y
      (Work.OddEnvelope.envelopeProfile h x y) u) =ᶠ[𝓝 (1 - Work.OddVolterra.tau / 2)] 0 := by
    filter_upwards [hnbhd] with u hu
    exact (htail u hu).2
  have hF0 : ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      Work.OddVolterra.momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) s
        - Work.OddVolterra.momentRHS n s = 0 :=
    eq_zero_of_iteratedDeriv_eq_zero_half n
      (hcontF.mono (fun t ht => ⟨by linarith [ht.1], ht.2⟩)) hderF hc hzF
  have hH0 : ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      Work.OddVolterra.momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0 := by
    have hder' : ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
        iteratedDeriv ((n - 1) + 1)
          (fun u : ℝ => Work.OddVolterra.momentH n h x y
            (Work.OddEnvelope.envelopeProfile h x y) u) s = 0 := by
      intro s hs
      rw [Nat.sub_add_cancel hn]
      exact hderH s hs
    exact eq_zero_of_iteratedDeriv_eq_zero_half (n - 1)
      (hcontH.mono (fun t ht => ⟨by linarith [ht.1], ht.2⟩)) hder' hc hzH
  constructor
  · intro s hs hs1
    rcases lt_or_eq_of_le hs1 with hlt | heq
    · have h := hF0 s ⟨hs, hlt⟩
      rw [sub_eq_zero] at h
      rw [h, Work.OddVolterra.momentRHS]
    · subst heq
      exact (htail 1 ⟨by norm_num [Work.OddVolterra.tau], le_rfl⟩).1
  · intro s hs hs1
    rcases lt_or_eq_of_le hs1 with hlt | heq
    · exact hH0 s ⟨hs, hlt⟩
    · subst heq
      exact (htail 1 ⟨by norm_num [Work.OddVolterra.tau], le_rfl⟩).2

end

end Work.Anchor
