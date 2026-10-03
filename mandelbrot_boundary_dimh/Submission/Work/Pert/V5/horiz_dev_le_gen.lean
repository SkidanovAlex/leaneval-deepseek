import Mathlib
import Submission.Work.Pert.V5.horiz_dev_le
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.dev_horiz_le
import Submission.Work.Pert.V5.tent_integral_gate
import Submission.Work.Pert.V5.integral_inv_exp_gate
import Submission.Work.Pert.liftF_defect_le_tau_explicit
import Submission.Work.Pert.scale_lattice
import Submission.Work.Pert.sigma_le_norm_alpha

/-!
# `Work.Pert.V5.horiz_dev_le_gen`

The **horizontal deviation bound** of the V5 layer in the *general low-margin, no-`s`* form.  Along a
horizontal corridor of length `≤ 2 M + 2 ^ 12` the gate margins are only assumed to satisfy

* `√2 · Rde ≤ min (mgA) (mgB)` — exactly the hypothesis needed to run the Fatou derivative estimate
  `hDE` with the maximal admissible radius `min (mgA) (mgB) / √2 ≥ Rde` (the ball of that radius
  around a gate point stays in the gate, `ball_in_gate`), and
* `1 ≤ min (mgA) (mgB)` — enough for the *tent* integral bound with `K = 1`.

The conclusion is the bound *without* the height `|s|` of the corridor:

`‖D (b+is) - D (a+is)‖ ≤ C₂ 2^6 (1+Ξ) (1 + log (2+M)) + 2^24 (1+1/rr) (1+Ξ) (1+1/Ξ) (1 + log (2+M))`.

This is `Work.Pert.V5.horiz_dev_le_ns` with the margin hypothesis weakened from `2 Rde + 2 ≤ …` to
`max (√2 Rde) 1 ≤ …`: every step of the proof uses the margins only through

* `Rde ≤ min (mgA) (mgB) / √2` (the hypothesis of `hDE` at the maximal radius), and
* the tent integral `∫ dx / min (mgA) (mgB) ≤ 2 log (1 + (b - a))` with `K = 1`
  (`integral_inv_min_le`, using `mgA a ≥ 1` and `mgB b ≥ 1`, which `hpos` supplies at the two
  endpoints), which is still `O (log M)` because `b - a ≤ 6 M`.

The rest of the proof — the pointwise majorant `‖Φ' - 1‖ ≤ √2 C₂ / min (mgA,mgB) + … ‖τ_f‖`,
its integration (`dev_horiz_le`), the defect estimate `liftF_defect_le_tau_explicit` and the
lattice integral `integral_inv_exp_gate` — is unchanged from `horiz_dev_le_ns`.
-/

namespace Work.Pert.V5

set_option maxHeartbeats 4000000

open Set Metric MeasureTheory
open scoped _root_.Topology

noncomputable section

/-- The `b₁`/`b₂`-margin of the gate, as a function of the real part, on a horizontal line. -/
private def mmF (Ξ : ℝ) (α : ℂ) (s x : ℝ) : ℝ :=
  min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I)) (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I))

/-- `‖1 - exp (-2πi α (x+is))‖`, the denominator of `τ_f`. -/
private def GG (α : ℂ) (s x : ℝ) : ℝ :=
  ‖(1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + (s : ℂ) * Complex.I)))‖

private lemma continuous_mmF (Ξ : ℝ) (α : ℂ) (s : ℝ) : Continuous (mmF Ξ α s) := by
  unfold mmF mgA mgB
  fun_prop

private lemma continuous_GG (α : ℂ) (s : ℝ) : Continuous (GG α s) := by
  unfold GG
  fun_prop

/-- On the gate, `1 - exp (-2πi α z) ≠ 0` (the gate avoids the poles of `τ_f`). -/
private lemma one_sub_exp_ne_zero_of_mem {Ξ : ℝ} {α : ℂ} {z : ℂ} (hΞ : 0 < Ξ)
    (hInF1 : MandelDim.InF1 α) (hz : z ∈ Work.Pert.Qm Ξ α) :
    (1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * α * z)) ≠ 0 := by
  intro h0
  have hexp : Complex.exp (-(2 * Real.pi * Complex.I * α * z)) = 1 := by
    have h := sub_eq_zero.mp h0
    exact h.symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have h2 : 2 * Real.pi = 0 := by
      have := congrArg Complex.im h
      simpa using this
    have := Real.pi_pos
    linarith
  have hαne : α ≠ 0 := by
    intro ha
    rw [ha] at hInF1
    simp [MandelDim.InF1] at hInF1
  have h4 : α * z = -(n : ℂ) := by
    have h3 : (2 * Real.pi * Complex.I) * (α * z) = (2 * Real.pi * Complex.I) * (-(n : ℂ)) := by
      linear_combination -hn
    exact mul_left_cancel₀ hpi h3
  have hz' : z = (-(n : ℂ)) / α := by
    rw [eq_div_iff hαne]
    linear_combination h4
  have hdist := (Work.Pert.scale_lattice hΞ hInF1).2 hz (-n)
  have hzero : ‖z - (((-n : ℤ)) : ℂ) / α‖ = 0 := by
    have hcast : ((((-n : ℤ)) : ℂ)) = -(n : ℂ) := by simp
    rw [hz', hcast]
    simp
  rw [hzero] at hdist
  linarith

/-- The main estimate, in the case `a ≤ b`. -/
private theorem horiz_dev_le_gen_ordered {Ξ rr M Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {s a b : ℝ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M)
    (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hDE : ∀ (Φ v : ℂ → ℂ) (z : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z R) → Set.InjOn Φ (Metric.ball z R) →
      DifferentiableOn ℂ v (Metric.ball z R) → (∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1) →
      ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (ha : (a + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α)
    (hb : (b + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α)
    (hlen : |b - a| ≤ 2 * M + 2 ^ 12) (hab : a ≤ b)
    (hlo : ∀ x ∈ Set.Icc a b,
      Real.sqrt 2 * Rde ≤ min (mgA Ξ α (x + s * Complex.I)) (mgB Ξ (x + s * Complex.I)))
    (hpos : ∀ x ∈ Set.Icc a b,
      1 ≤ min (mgA Ξ α (x + s * Complex.I)) (mgB Ξ (x + s * Complex.I))) :
    ‖(Φm ((b : ℂ) + s * Complex.I) - ((b : ℂ) + s * Complex.I))
        - (Φm ((a : ℂ) + s * Complex.I) - ((a : ℂ) + s * Complex.I))‖
      ≤ C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
        + 2 ^ 24 * (1 + 1 / rr) * (1 + Ξ) * (1 + 1 / Ξ)
            * (1 + Real.log (2 + M)) := by
  have _ := ha
  have _ := hb
  -- ## the numeric data
  have hα64 : ‖α‖ ≤ 1 / 64 := by
    have h1 : (64 : ℝ) ≤ 32 * (M + 2 + Ξ) := by linarith only [hM, hΞ]
    exact le_trans hα (one_div_le_one_div_of_le (by norm_num) h1)
  have hΞnn : 0 ≤ Ξ := le_of_lt hΞ
  -- ## the gate is open and the segment lies in it
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := by
    simpa only [Work.Pert.Qm] using
      Work.Fatou.Qreg.isOpen_Qreg (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
  have hlo' : ∀ x ∈ Set.Icc a b, Real.sqrt 2 * Rde ≤ mmF Ξ α s x := fun x hx => hlo x hx
  have hmm_ge : ∀ x ∈ Set.Icc a b, (1 : ℝ) ≤ mmF Ξ α s x := fun x hx => hpos x hx
  have hmm_pos : ∀ x ∈ Set.Icc a b, 0 < mmF Ξ α s x :=
    fun x hx => lt_of_lt_of_le (by norm_num) (hmm_ge x hx)
  have hseg : ∀ x ∈ Set.Icc a b, ((x : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
    intro x hx
    have h1 : 0 < mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I) := by
      have h := hmm_ge x hx
      have h' : mmF Ξ α s x ≤ mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I) := by
        simp only [mmF]; exact min_le_left _ _
      linarith
    have h2 : 0 < mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I) := by
      have h := hmm_ge x hx
      have h' : mmF Ξ α s x ≤ mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I) := by
        simp only [mmF]; exact min_le_right _ _
      linarith
    rw [mem_Qm_iff_mg]
    exact ⟨h1, h2⟩
  have hG_pos : ∀ x ∈ Set.Icc a b, 0 < GG α s x := by
    intro x hx
    have hne := one_sub_exp_ne_zero_of_mem hΞ hInF1 (hseg x hx)
    simpa only [GG] using norm_pos_iff.mpr hne
  -- ## the pointwise derivative bound
  have hpt : ∀ x ∈ Set.Icc a b, ‖deriv Φm ((x : ℂ) + (s : ℂ) * Complex.I) - 1‖ ≤
      (Real.sqrt 2 * C₂) * (1 / mmF Ξ α s x)
        + ((32 / 31) * (2 ^ 12 * (1 + 1 / rr))) * (‖σ‖ / GG α s x) := by
    intro x hx
    set z : ℂ := (x : ℂ) + (s : ℂ) * Complex.I with hz
    have hzQ : z ∈ Work.Pert.Qm Ξ α := hseg x hx
    have hmpos : 0 < mmF Ξ α s x := hmm_pos x hx
    have hRge : Rde ≤ mmF Ξ α s x / Real.sqrt 2 := by
      have h2R : Real.sqrt 2 * Rde ≤ mmF Ξ α s x := hlo' x hx
      rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
      linarith [h2R]
    have hball : Metric.ball z (mmF Ξ α s x / Real.sqrt 2) ⊆ Work.Pert.Qm Ξ α := by
      have h := ball_in_gate (Ξ := Ξ) (α := α) hzQ
      simpa only [mmF, hz] using h
    -- apply the Fatou derivative estimate
    have hDEz : ‖deriv Φm z
        - 1 / (Work.Pert.liftF u σ α z - z)‖ ≤ C₂ / (mmF Ξ α s x / Real.sqrt 2) :=
      hDE Φm (fun w => Work.Pert.liftF u σ α w - w) z (mmF Ξ α s x / Real.sqrt 2) hRge
        (hΦm.1.mono hball) (hΦm.2.1.mono hball)
        ((hNT.1.1.mono hball).sub differentiableOn_id)
        (fun w hw => by
          have h1 : ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32 :=
            (hNT.1.2 w (hball hw)).1
          have h2 : Work.Pert.liftF u σ α w - w - 1 = Work.Pert.liftF u σ α w - (w + 1) := by
            ring
          rw [h2]
          linarith)
        (fun w hw hfw => by
          have hwm : w ∈ Work.Pert.Qm Ξ α := hball hw
          have h1 : w + (Work.Pert.liftF u σ α w - w) = Work.Pert.liftF u σ α w := by ring
          have hfm : Work.Pert.liftF u σ α w ∈ Work.Pert.Qm Ξ α := by
            have h2 := hfw
            rw [h1] at h2
            exact hball h2
          have h := hΦm.2.2 w hwm hfm
          simpa only [h1] using h)
    -- the defect bounds
    have hd32 : ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 2 ^ 12 * (1 + 1 / rr)
        * ‖Work.Pert.tauC σ α z‖ :=
      liftF_defect_le_tau_explicit (Ξ := Ξ) (rr := rr) hΞ hrr hInF1 hα64 hσ hnorm hu hu2 hτQ
        (fun w hw => (hNT.1.2 w hw).1) z hzQ
    have hnorm_ge : (31 / 32 : ℝ) ≤ ‖Work.Pert.liftF u σ α z - z‖ := by
      have h1 : ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32 := (hNT.1.2 z hzQ).1
      have h2 : Work.Pert.liftF u σ α z - z = 1 + (Work.Pert.liftF u σ α z - (z + 1)) := by
        ring
      rw [h2]
      have h3 := norm_add_le (1 : ℂ) (Work.Pert.liftF u σ α z - (z + 1))
      have h4 : ‖(1 : ℂ)‖ = 1 := norm_one
      have h6 : (1 : ℝ) - ‖Work.Pert.liftF u σ α z - (z + 1)‖
          ≤ ‖(1 : ℂ) + (Work.Pert.liftF u σ α z - (z + 1))‖ := by
        have h10 : ‖(1 : ℂ)‖ ≤ ‖(1 : ℂ) + (Work.Pert.liftF u σ α z - (z + 1))‖
            + ‖Work.Pert.liftF u σ α z - (z + 1)‖ := by
          have h11 := norm_sub_le ((1 : ℂ) + (Work.Pert.liftF u σ α z - (z + 1)))
            (Work.Pert.liftF u σ α z - (z + 1))
          have he : (1 : ℂ) + (Work.Pert.liftF u σ α z - (z + 1))
              - (Work.Pert.liftF u σ α z - (z + 1)) = (1 : ℂ) := by ring
          rwa [he] at h11
        rw [norm_one] at h10
        linarith [h10]
      linarith [h1, h6]
    have hkey : ‖1 / (Work.Pert.liftF u σ α z - z) - 1‖
        ≤ (32 / 31) * ‖Work.Pert.liftF u σ α z - (z + 1)‖ := by
      have hne : Work.Pert.liftF u σ α z - z ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hnorm_ge
        norm_num at hnorm_ge
      rw [div_sub_one hne, norm_div]
      have hnum : 1 - (Work.Pert.liftF u σ α z - z)
          = -(Work.Pert.liftF u σ α z - (z + 1)) := by ring
      rw [hnum, norm_neg]
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖Work.Pert.liftF u σ α z - z‖)]
      have hb : ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32 := (hNT.1.2 z hzQ).1
      have h0 : (0 : ℝ) ≤ ‖Work.Pert.liftF u σ α z - (z + 1)‖ := norm_nonneg _
      nlinarith [hnorm_ge, h0, (by norm_num : (0:ℝ) < 32/31),
        (by norm_num : (32/31 : ℝ) * (31/32) = 1), hb]
    -- combine
    have htau : ‖Work.Pert.tauC σ α z‖ = ‖σ‖ / GG α s x := by
      simp only [GG, hz, Work.Pert.tauC, norm_div]
    have hmain : ‖deriv Φm z - 1‖ ≤ (Real.sqrt 2 * C₂) * (1 / mmF Ξ α s x)
        + ((32 / 31) * (2 ^ 12 * (1 + 1 / rr))) * (‖σ‖ / GG α s x) := by
      have htri : ‖deriv Φm z - 1‖ ≤ ‖deriv Φm z - 1 / (Work.Pert.liftF u σ α z - z)‖
          + ‖1 / (Work.Pert.liftF u σ α z - z) - 1‖ := by
        have he : deriv Φm z - 1 = (deriv Φm z - 1 / (Work.Pert.liftF u σ α z - z))
            + (1 / (Work.Pert.liftF u σ α z - z) - 1) := by ring
        rw [he]
        exact norm_add_le _ _
      have h1 : C₂ / (mmF Ξ α s x / Real.sqrt 2) = (Real.sqrt 2 * C₂) * (1 / mmF Ξ α s x) := by
        rw [div_div_eq_mul_div, mul_div_assoc]
        ring
      have h2 : (32 / 31) * ‖Work.Pert.liftF u σ α z - (z + 1)‖
          ≤ ((32 / 31) * (2 ^ 12 * (1 + 1 / rr))) * (‖σ‖ / GG α s x) := by
        rw [← htau]
        have h0 : (0 : ℝ) ≤ 32 / 31 := by norm_num
        have := mul_le_mul_of_nonneg_left hd32 h0
        linarith [this]
      linarith [htri, hDEz, hkey, h2, h1]
    simpa only [hz] using hmain
  -- ## the majorant is continuous on the segment
  have hgcont : ContinuousOn (fun x : ℝ => (Real.sqrt 2 * C₂) * (1 / mmF Ξ α s x)
      + ((32 / 31) * (2 ^ 12 * (1 + 1 / rr))) * (‖σ‖ / GG α s x)) (Set.Icc a b) := by
    refine ContinuousOn.add ?_ ?_
    · exact continuousOn_const.mul (ContinuousOn.div continuousOn_const
        (continuous_mmF Ξ α s).continuousOn (fun x hx => ne_of_gt (hmm_pos x hx)))
    · exact continuousOn_const.mul (ContinuousOn.div continuousOn_const
        (continuous_GG α s).continuousOn (fun x hx => ne_of_gt (hG_pos x hx)))
  -- ## the fundamental theorem of calculus
  have hdev := dev_horiz_le (Φ := Φm) (Q := Work.Pert.Qm Ξ α) (s := s) (a := a) (b := b)
    (g := fun x : ℝ => (Real.sqrt 2 * C₂) * (1 / mmF Ξ α s x)
      + ((32 / 31) * (2 ^ 12 * (1 + 1 / rr))) * (‖σ‖ / GG α s x))
    hQopen hab hseg hΦm.1 hpt hgcont
  -- ## evaluate the integral of the majorant
  have hI1 : IntervalIntegrable (fun x : ℝ => (Real.sqrt 2 * C₂) * (1 / mmF Ξ α s x))
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const
      (continuous_mmF Ξ α s).continuousOn
      (fun x hx => ne_of_gt (hmm_pos x hx)))
  have hI2 : IntervalIntegrable (fun x : ℝ => ((32 / 31) * (2 ^ 12 * (1 + 1 / rr)))
      * (‖σ‖ / GG α s x)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const
      (continuous_GG α s).continuousOn
      (fun x hx => ne_of_gt (hG_pos x hx)))
  have hsplit : ∫ x in a..b, ((Real.sqrt 2 * C₂) * (1 / mmF Ξ α s x)
        + ((32 / 31) * (2 ^ 12 * (1 + 1 / rr))) * (‖σ‖ / GG α s x))
      = (Real.sqrt 2 * C₂) * (∫ x in a..b, 1 / mmF Ξ α s x)
        + ((32 / 31) * (2 ^ 12 * (1 + 1 / rr))) * (∫ x in a..b, ‖σ‖ / GG α s x) := by
    rw [intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  -- ## the two integral bounds
  have hshort : ‖α‖ * (b - a) ≤ 1 / 2 := by
    have h1 : (b - a) ≤ 2 * M + 2 ^ 12 := by
      have := hlen
      rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at this
    have h2 : 0 < 32 * (M + 2 + Ξ) := by linarith only [hM, hΞ]
    have h3' : ‖α‖ * (b - a) ≤ (1 / (32 * (M + 2 + Ξ))) * (2 * M + 2 ^ 12) :=
      mul_le_mul hα h1 (by linarith : (0 : ℝ) ≤ b - a) (by positivity)
    have hM2 : (2 ^ 12 : ℝ) ≤ 4 * M := by
      have : (2 : ℝ) ^ 10 ≤ M := hM
      nlinarith [this]
    have h4 : (1 / (32 * (M + 2 + Ξ))) * (2 * M + 2 ^ 12) ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ h2]
      nlinarith [hM2, hM, hΞnn]
    linarith
  have hclear : ∀ x ∈ Set.Icc a b, ∀ k : ℤ,
      ‖α‖ * Ξ / 2 ≤ ‖α * ((x : ℂ) + (s : ℂ) * Complex.I) - (k : ℂ)‖ := by
    intro x hx k
    have hzQ : ((x : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := hseg x hx
    have h := (Work.Pert.scale_lattice hΞ hInF1).2 hzQ k
    have hαne : α ≠ 0 := by
      have hre : 0 < α.re := by
        have := hInF1; simp only [MandelDim.InF1] at this; linarith [abs_nonneg α.im]
      exact fun h0 => by rw [h0] at hre; simp at hre
    have hmul : α * (((x : ℂ) + (s : ℂ) * Complex.I) - (k : ℂ) / α)
        = α * ((x : ℂ) + (s : ℂ) * Complex.I) - (k : ℂ) := by
      rw [mul_sub, mul_div_cancel₀ _ hαne]
    calc ‖α‖ * Ξ / 2 = ‖α‖ * (Ξ / 2) := by ring
      _ ≤ ‖α‖ * ‖((x : ℂ) + (s : ℂ) * Complex.I) - (k : ℂ) / α‖ :=
          mul_le_mul_of_nonneg_left h (norm_nonneg α)
      _ = ‖α * (((x : ℂ) + (s : ℂ) * Complex.I) - (k : ℂ) / α)‖ := by
          rw [norm_mul]
      _ = ‖α * ((x : ℂ) + (s : ℂ) * Complex.I) - (k : ℂ)‖ := by rw [hmul]
  have htent : ∫ x in a..b, 1 / mmF Ξ α s x ≤ 2 * Real.log (1 + (b - a)) := by
    have hAc : Continuous (fun x : ℝ => mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I)) := by
      simp only [mgA]; fun_prop
    have hBc : Continuous (fun x : ℝ => mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I)) := by
      simp only [mgB]; fun_prop
    have h := integral_inv_min_le (K := (1 : ℝ)) (by norm_num) hab hAc hBc
      (le_trans (hmm_ge a ⟨le_rfl, hab⟩) (min_le_left _ _))
      (le_trans (hmm_ge b ⟨hab, le_rfl⟩) (min_le_right _ _))
      (fun x hx => by rw [mgA_line, mgA_line]; ring)
      (fun x hx => by rw [mgB_line, mgB_line]; ring)
    have h' : ∫ x in a..b, 1 / mmF Ξ α s x ≤ 2 * Real.log (1 + (b - a) / (1 : ℝ)) := by
      simpa only [mmF] using h
    simpa using h'
  have hexp : ∫ x in a..b, 1 / GG α s x
      ≤ 8 * (1 + 1 / ‖α‖) * (1 + Real.log (2 + (b - a) / Ξ)) := by
    have h := integral_inv_exp_gate (Ξ := Ξ) (α := α) (s := s) (a := a) (b := b)
      hΞ hInF1 hab hshort hclear
    simpa only [GG] using h
  -- ## assemble
  set Lg : ℝ := 1 + Real.log (2 + M) with hLg
  have hLog1 : (1 : ℝ) ≤ Lg := by
    have h0 : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
    simp only [hLg]; linarith
  have hlen6 : (b - a) ≤ 6 * M := by
    have h2 : (b - a) ≤ 2 * M + 2 ^ 12 := by
      have := hlen
      rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at this
    have h3 : (2 ^ 12 : ℝ) ≤ 4 * M := by nlinarith [hM]
    linarith
  have hlogM : Real.log M ≤ Real.log (2 + M) := Real.log_le_log (by linarith) (by linarith)
  have hlogMnn : (0 : ℝ) ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
  have hlogMle : Real.log M ≤ Lg := by simp only [hLg]; linarith
  -- ## (A) the tent logarithm: `log (1 + len) ≤ 3 Lg`
  have hLa : Real.log (1 + (b - a)) ≤ 3 * Lg := by
    have h4 : 0 < 1 + (b - a) := by linarith [hlen6]
    have h5 : 1 + (b - a) ≤ 7 * M := by linarith [hlen6, hM]
    have h6 : Real.log (1 + (b - a)) ≤ Real.log (7 * M) := Real.log_le_log h4 h5
    have h7 : Real.log (7 * M) = Real.log 7 + Real.log M :=
      Real.log_mul (by norm_num) (by linarith : M ≠ 0)
    have h8 : Real.log 7 ≤ Real.log M := Real.log_le_log (by norm_num) (by linarith [hM])
    rw [h7] at h6
    linarith [h6, h8, hlogMle, hlogMnn, hLog1]
  -- ## (B) the exponential logarithm
  have hLb : 1 + Real.log (2 + (b - a) / Ξ) ≤ 5 * (1 + Ξ) * (1 + 1 / Ξ) * Lg := by
    have hlog8 : Real.log (8 * M) ≤ 3 + Real.log M := by
      have h9 : Real.log (8 * M) = Real.log 8 + Real.log M :=
        Real.log_mul (by norm_num) (by linarith : M ≠ 0)
      have h10 : Real.log 8 ≤ 3 := by
        have h11 : Real.log 8 = 3 * Real.log 2 := by
          rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
          norm_num
        have h12 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
          linarith
        linarith [h11, h12]
      linarith [h9, h10]
    have hlogi : Real.log (1 / Ξ) ≤ 1 / Ξ := by
      have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / Ξ by positivity)
      linarith
    have hfin : 1 + Real.log (2 + (b - a) / Ξ) ≤ 4 + Lg + 1 / Ξ := by
      rcases le_total 1 Ξ with hΞ1 | hΞ1
      · have h7 : 2 + (b - a) / Ξ ≤ 8 * M := by
          have h8 : (b - a) / Ξ ≤ 6 * M := by
            rw [div_le_iff₀ hΞ]
            nlinarith [hlen6, hΞ1, hΞ]
          linarith
        have h8 : Real.log (2 + (b - a) / Ξ) ≤ Real.log (8 * M) :=
          Real.log_le_log (by positivity) h7
        have h9 : (0 : ℝ) ≤ 1 / Ξ := by positivity
        linarith [h8, hlog8, hlogMle, h9, hLog1]
      · have h7 : 2 + (b - a) / Ξ ≤ (8 * M) * (1 / Ξ) := by
          have h9 : (b - a) / Ξ ≤ 6 * M / Ξ := div_le_div_of_nonneg_right hlen6 hΞ.le
          have h10 : 6 * M / Ξ = 6 * M * (1 / Ξ) := by ring
          have h11 : 2 ≤ 2 * (1 / Ξ) := by
            have h12 : 1 ≤ 1 / Ξ := by
              rw [le_div_iff₀ hΞ]
              linarith only [hΞ1]
            linarith [h12]
          have h13 : (0 : ℝ) ≤ 1 / Ξ := by positivity
          nlinarith [h9, h10, h11, h13, hM]
        have h8 : 0 < 2 + (b - a) / Ξ := by
          have : 0 ≤ (b - a) / Ξ := by positivity
          linarith
        have h9 : Real.log (2 + (b - a) / Ξ) ≤ Real.log (8 * M) + Real.log (1 / Ξ) := by
          calc Real.log (2 + (b - a) / Ξ) ≤ Real.log ((8 * M) * (1 / Ξ)) :=
                Real.log_le_log h8 h7
            _ = Real.log (8 * M) + Real.log (1 / Ξ) :=
                Real.log_mul (by positivity) (by positivity)
        linarith [h9, hlog8, hlogMle, hlogi, hLog1]
    have hfin2 : 4 + Lg + 1 / Ξ ≤ 5 * (1 + Ξ) * (1 + 1 / Ξ) * Lg := by
      have hL : (1 : ℝ) ≤ Lg := hLog1
      have h1e : (0 : ℝ) < 1 / Ξ := by positivity
      have h2 : (1 + Ξ) * (1 + 1 / Ξ) = 2 + Ξ + 1 / Ξ := by field_simp; ring
      have h3 : 5 * (1 + Ξ) * (1 + 1 / Ξ) = 5 * (2 + Ξ + 1 / Ξ) := by
        have hassoc : 5 * (1 + Ξ) * (1 + 1 / Ξ) = 5 * ((1 + Ξ) * (1 + 1 / Ξ)) := by ring
        rw [hassoc, h2]
      rw [h3]
      nlinarith [hΞ, hΞnn, h1e, hL]
    linarith [hfin, hfin2]
  -- ## the C₂-part
  have hterm1 : (Real.sqrt 2 * C₂) * (∫ x in a..b, 1 / mmF Ξ α s x)
      ≤ C₂ * 2 ^ 6 * (1 + Ξ) * Lg := by
    have h1 : (Real.sqrt 2 * C₂) * (∫ x in a..b, 1 / mmF Ξ α s x)
        ≤ (Real.sqrt 2 * C₂) * (2 * Real.log (1 + (b - a))) := by
      apply mul_le_mul_of_nonneg_left htent
      positivity
    have h2 : (Real.sqrt 2 * C₂) * (2 * Real.log (1 + (b - a)))
        ≤ (Real.sqrt 2 * C₂) * (6 * Lg) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [hLa]
    have h3 : (Real.sqrt 2 * C₂) * (6 * Lg) ≤ C₂ * 2 ^ 6 * (1 + Ξ) * Lg := by
      have hs : Real.sqrt 2 ≤ 8 := by
        have h1 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
          rw [← pow_two]
          exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
        nlinarith [h1, Real.sqrt_nonneg 2]
      have hL : (0 : ℝ) < Lg := lt_of_lt_of_le one_pos hLog1
      have h1 : (Real.sqrt 2 * C₂) * (6 * Lg) ≤ (8 * C₂) * (6 * Lg) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hC₂.le) (by positivity)
      have h2 : (8 * C₂) * (6 * Lg) = 48 * (C₂ * Lg) := by ring
      have h4 : (0 : ℝ) ≤ C₂ * Lg := by positivity
      have h5 : (1 : ℝ) ≤ 1 + Ξ := by linarith
      have h6 : 48 * (C₂ * Lg) ≤ 64 * ((1 + Ξ) * (C₂ * Lg)) := by
        have h7 : (1 : ℝ) * (C₂ * Lg) ≤ (1 + Ξ) * (C₂ * Lg) :=
          mul_le_mul_of_nonneg_right h5 h4
        linarith [h7]
      have h8 : 64 * ((1 + Ξ) * (C₂ * Lg)) = C₂ * 2 ^ 6 * (1 + Ξ) * Lg := by norm_num; ring
      linarith [h1, h2, h6, h8]
    linarith
  -- ## the defect part
  have hterm2 : ((32 / 31) * (2 ^ 12 * (1 + 1 / rr))) * (∫ x in a..b, ‖σ‖ / GG α s x)
      ≤ 2 ^ 24 * (1 + 1 / rr) * (1 + Ξ) * (1 + 1 / Ξ) * Lg := by
    have hσb : ‖σ‖ ≤ 32 * ‖α‖ :=
      sigma_le_norm_alpha hα64 (hu2 0 (Metric.mem_ball_self hrr)).1 hnorm
    have h1 : ∫ x in a..b, ‖σ‖ / GG α s x = ‖σ‖ * (∫ x in a..b, 1 / GG α s x) := by
      have hc : ∀ x : ℝ, ‖σ‖ / GG α s x = ‖σ‖ * (1 / GG α s x) := by
        intro x; ring
      simp only [hc]
      rw [intervalIntegral.integral_const_mul]
    have h2 : ‖σ‖ * (∫ x in a..b, 1 / GG α s x)
        ≤ ‖σ‖ * (8 * (1 + 1 / ‖α‖) * (1 + Real.log (2 + (b - a) / Ξ))) :=
      mul_le_mul_of_nonneg_left hexp (norm_nonneg σ)
    have hαpos : 0 < ‖α‖ := by
      have hre : 0 < α.re := by
        have := hInF1; simp only [MandelDim.InF1] at this; linarith [abs_nonneg α.im]
      exact norm_pos_iff.mpr (by intro h0; rw [h0] at hre; simp at hre)
    have hlogpos : (0 : ℝ) ≤ 1 + Real.log (2 + (b - a) / Ξ) := by
      have h1 : (1 : ℝ) ≤ 2 + (b - a) / Ξ := by
        have : 0 ≤ (b - a) / Ξ := by positivity
        linarith
      have h2 : 0 ≤ Real.log (2 + (b - a) / Ξ) := Real.log_nonneg h1
      linarith
    have h3 : ‖σ‖ * (8 * (1 + 1 / ‖α‖)) ≤ 2 ^ 9 := by
      have hαle1 : ‖α‖ ≤ 1 := by linarith only [hα64]
      have h4 : ‖σ‖ * (1 + 1 / ‖α‖) = ‖σ‖ + ‖σ‖ / ‖α‖ := by ring
      have h5 : ‖σ‖ / ‖α‖ ≤ 32 := by
        rw [div_le_iff₀ hαpos]
        nlinarith [hσb]
      have h6 : ‖σ‖ * (1 + 1 / ‖α‖) ≤ 32 * ‖α‖ + 32 := by linarith [h4, h5, hσb]
      have h7 : 32 * ‖α‖ + 32 ≤ 64 := by linarith [hαle1]
      nlinarith [h4, h6, h7]
    have h4 : ‖σ‖ * (8 * (1 + 1 / ‖α‖)) * (1 + Real.log (2 + (b - a) / Ξ))
        ≤ 2 ^ 9 * (5 * (1 + Ξ) * (1 + 1 / Ξ) * Lg) := by
      have h8 : ‖σ‖ * (8 * (1 + 1 / ‖α‖)) * (1 + Real.log (2 + (b - a) / Ξ))
          ≤ 2 ^ 9 * (1 + Real.log (2 + (b - a) / Ξ)) :=
        mul_le_mul_of_nonneg_right h3 hlogpos
      have h9 : 2 ^ 9 * (1 + Real.log (2 + (b - a) / Ξ))
          ≤ 2 ^ 9 * (5 * (1 + Ξ) * (1 + 1 / Ξ) * Lg) :=
        mul_le_mul_of_nonneg_left hLb (by norm_num)
      linarith [h8, h9]
    have h5 : ((32 / 31) * (2 ^ 12 * (1 + 1 / rr))) * (2 ^ 9 * (5 * (1 + Ξ) * (1 + 1 / Ξ) * Lg))
        ≤ 2 ^ 24 * (1 + 1 / rr) * (1 + Ξ) * (1 + 1 / Ξ) * Lg := by
      have hrr1 : (0:ℝ) < 1 + 1 / rr := by positivity
      have hL : 0 < Lg := lt_of_lt_of_le one_pos hLog1
      have hfac : 0 ≤ (1 + Ξ) * (1 + 1 / Ξ) := by positivity
      have hstep : (32/31) * 2 ^ 12 * 2 ^ 9 * 5 ≤ 2 ^ 24 := by norm_num
      nlinarith [hstep, hrr1, hL, hfac, hΞnn]
    calc ((32 / 31) * (2 ^ 12 * (1 + 1 / rr))) * (∫ x in a..b, ‖σ‖ / GG α s x)
        = ((32 / 31) * (2 ^ 12 * (1 + 1 / rr))) * (‖σ‖ * (∫ x in a..b, 1 / GG α s x)) := by
          rw [h1]
      _ ≤ ((32 / 31) * (2 ^ 12 * (1 + 1 / rr)))
            * (‖σ‖ * (8 * (1 + 1 / ‖α‖) * (1 + Real.log (2 + (b - a) / Ξ)))) := by
          apply mul_le_mul_of_nonneg_left h2
          positivity
      _ = ((32 / 31) * (2 ^ 12 * (1 + 1 / rr)))
            * (‖σ‖ * (8 * (1 + 1 / ‖α‖)) * (1 + Real.log (2 + (b - a) / Ξ))) := by ring
      _ ≤ ((32 / 31) * (2 ^ 12 * (1 + 1 / rr))) * (2 ^ 9 * (5 * (1 + Ξ) * (1 + 1 / Ξ) * Lg)) := by
          apply mul_le_mul_of_nonneg_left h4
          positivity
      _ ≤ 2 ^ 24 * (1 + 1 / rr) * (1 + Ξ) * (1 + 1 / Ξ) * Lg := h5
  -- ## conclusion
  calc ‖(Φm ((b : ℂ) + s * Complex.I) - ((b : ℂ) + s * Complex.I))
        - (Φm ((a : ℂ) + s * Complex.I) - ((a : ℂ) + s * Complex.I))‖
      ≤ ∫ x in a..b, ((Real.sqrt 2 * C₂) * (1 / mmF Ξ α s x)
          + ((32 / 31) * (2 ^ 12 * (1 + 1 / rr))) * (‖σ‖ / GG α s x)) := hdev
    _ = (Real.sqrt 2 * C₂) * (∫ x in a..b, 1 / mmF Ξ α s x)
        + ((32 / 31) * (2 ^ 12 * (1 + 1 / rr))) * (∫ x in a..b, ‖σ‖ / GG α s x) := hsplit
    _ ≤ C₂ * 2 ^ 6 * (1 + Ξ) * Lg
        + 2 ^ 24 * (1 + 1 / rr) * (1 + Ξ) * (1 + 1 / Ξ) * Lg := add_le_add hterm1 hterm2
    _ = C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
        + 2 ^ 24 * (1 + 1 / rr) * (1 + Ξ) * (1 + 1 / Ξ)
            * (1 + Real.log (2 + M)) := by rw [hLg]

theorem horiz_dev_le_gen {Ξ rr M Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {s a b : ℝ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M)
    (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hDE : ∀ (Φ v : ℂ → ℂ) (z : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z R) → Set.InjOn Φ (Metric.ball z R) →
      DifferentiableOn ℂ v (Metric.ball z R) → (∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1) →
      ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (ha : (a + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α)
    (hb : (b + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α)
    (hlen : |b - a| ≤ 2 * M + 2 ^ 12)
    (hlo : ∀ x ∈ Set.Icc (min a b) (max a b),
      Real.sqrt 2 * Rde ≤ min (Work.Pert.V5.mgA Ξ α (x + s * Complex.I))
                               (Work.Pert.V5.mgB Ξ (x + s * Complex.I)))
    (hpos : ∀ x ∈ Set.Icc (min a b) (max a b),
      1 ≤ min (Work.Pert.V5.mgA Ξ α (x + s * Complex.I))
              (Work.Pert.V5.mgB Ξ (x + s * Complex.I))) :
    ‖(Φm ((b : ℂ) + s * Complex.I) - ((b : ℂ) + s * Complex.I))
        - (Φm ((a : ℂ) + s * Complex.I) - ((a : ℂ) + s * Complex.I))‖
      ≤ C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
        + 2 ^ 24 * (1 + 1 / rr) * (1 + Ξ) * (1 + 1 / Ξ)
            * (1 + Real.log (2 + M)) := by
  rcases le_total a b with hab | hab
  · refine horiz_dev_le_gen_ordered hΞ hrr hM hInF1 hα hRde hC₂ hσ hnorm hu hu2 hτQ hDE hNT hΦm
      ha hb hlen hab ?_ ?_
    · intro x hx
      have h := hlo x (by rw [min_eq_left hab, max_eq_right hab]; exact hx)
      simpa only [min_eq_left hab, max_eq_right hab] using h
    · intro x hx
      have h := hpos x (by rw [min_eq_left hab, max_eq_right hab]; exact hx)
      simpa only [min_eq_left hab, max_eq_right hab] using h
  · have h := horiz_dev_le_gen_ordered (a := b) (b := a) hΞ hrr hM hInF1 hα hRde hC₂ hσ hnorm
      hu hu2 hτQ hDE hNT hΦm hb ha (by rwa [abs_sub_comm] at hlen) hab ?_ ?_
    · rwa [norm_sub_rev] at h
    · intro x hx
      have h' := hlo x (by rw [min_eq_right hab, max_eq_left hab]; exact hx)
      simpa only [min_eq_right hab, max_eq_left hab] using h'
    · intro x hx
      have h' := hpos x (by rw [min_eq_right hab, max_eq_left hab]; exact hx)
      simpa only [min_eq_right hab, max_eq_left hab] using h'

end

end Work.Pert.V5
