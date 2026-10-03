import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.Fatou
import Submission.Work.Pert.Pin3.dev_deriv_le_pt
import Submission.Work.Pert.PinLogDev.ball_imag_subset_Qm
import Submission.Work.Pert.dev_base_v3
import Submission.Work.Pert.PinAux.Defs
import Submission.Work.Pert.PinAux.dev_axis_transport
import Submission.Work.Pert.Pin3.dev_seg_const

/-!
# `Submission.Work.Pert.PinLogDev.Helpers`

Toolkit for the axis transport of `Work.Pert.PinLogDev.anchor_to_all_t`:

* the two gate margins at the axis-like points `s • w`, `w = ±I` (`margA_axis_w`,
  `margB_axis_w`, `re_axis_w`, `im_axis_w`, `norm_axis_w`), and the consequence
  `QAdm_re_inv` of `QAdm`;
* the pointwise derivative estimate at such a point, obtained from the hypothesis `hDE`
  (Lemma A.2.4) through `Work.Pert.Pin3.dev_deriv_le_pt` (`deriv_axis_bound`);
* the fundamental theorem of calculus along the line `s ↦ s • w` with `‖w‖ = 1`
  (`axis_dev_le`), together with the two elementary integrals
  `∫ ds/(s - Ξ) = log((b-Ξ)/(a-Ξ))` and `∫ ds/s = log(b/a)`.
-/

namespace Work.Pert.PinLogDev

open MandelDim Complex Metric MeasureTheory
open scoped Topology

noncomputable section

/-! ## 1. Geometry of the axis points -/

/-- `QAdm` for the gate `Qm Ξ α` gives `(1/α).re > 2Ξ + 4`. -/
theorem QAdm_re_inv {Ξ : ℝ} {α : ℂ}
    (hQ : MandelDim.QAdm (some ((Ξ:ℂ) - 1/α)) (some (-(Ξ:ℂ)))) :
    2 * Ξ + 4 < (1/α).re := by
  have h := hQ ((Ξ:ℂ) - 1/α) (by simp) (-(Ξ:ℂ)) (by simp)
  have h1 : ((Ξ:ℂ) - 1/α).re = Ξ - (1/α).re := by simp
  have h2 : ((-(Ξ:ℂ)) : ℂ).re = -Ξ := by simp
  rw [h1, h2] at h
  linarith

/-- The `A`-margin at the points `s • w`, `w = ±I`. -/
theorem margA_axis_w {Ξ : ℝ} {α w : ℂ} (hw : w = Complex.I ∨ w = -Complex.I) (s : ℝ) :
    Work.Pert.margA Ξ α ((s : ℂ) * w) = (1/α).re - Ξ + |s - (-(w.im) * (1/α).im)| := by
  rcases hw with rfl | rfl
  · have h1 : ((s : ℂ) * Complex.I).re = 0 := by simp
    have h2 : ((s : ℂ) * Complex.I).im = s := by simp
    simp only [Work.Pert.margA, h1, h2, Complex.I_im, Complex.I_re]
    ring_nf
  · have h1 : ((s : ℂ) * -Complex.I).re = 0 := by simp
    have h2 : ((s : ℂ) * -Complex.I).im = -s := by simp
    have h3 : (-Complex.I : ℂ).im = -1 := by simp
    simp only [Work.Pert.margA, h1, h2, h3]
    have h4 : -s + (1/α).im = -(s - (1/α).im) := by ring
    rw [h4, abs_neg]
    ring_nf

/-- The `B`-margin at the points `s • w`, `w = ±I`, `s ≥ 0`. -/
theorem margB_axis_w {Ξ : ℝ} {α w : ℂ} (hw : w = Complex.I ∨ w = -Complex.I)
    {s : ℝ} (hs : 0 ≤ s) :
    Work.Pert.margB Ξ α ((s : ℂ) * w) = s - Ξ := by
  rcases hw with rfl | rfl
  · have h1 : ((s : ℂ) * Complex.I).re = 0 := by simp
    have h2 : ((s : ℂ) * Complex.I).im = s := by simp
    simp only [Work.Pert.margB, h1, h2, abs_of_nonneg hs]
    ring
  · have h1 : ((s : ℂ) * -Complex.I).re = 0 := by simp
    have h2 : ((s : ℂ) * -Complex.I).im = -s := by simp
    simp only [Work.Pert.margB, h1, h2, abs_neg, abs_of_nonneg hs]
    ring

/-- The imaginary part of `s • w` for `w = ±I`. -/
theorem im_axis_w {w : ℂ} (hw : w = Complex.I ∨ w = -Complex.I) (s : ℝ) :
    |((s : ℂ) * w).im| = |s| := by
  rcases hw with rfl | rfl
  · have h2 : ((s : ℂ) * Complex.I).im = s := by simp
    rw [h2]
  · have h2 : ((s : ℂ) * -Complex.I).im = -s := by simp
    rw [h2, abs_neg]

/-- The real part of `s • w` for `w = ±I`. -/
theorem re_axis_w {w : ℂ} (hw : w = Complex.I ∨ w = -Complex.I) (s : ℝ) :
    ((s : ℂ) * w).re = 0 := by
  rcases hw with rfl | rfl <;> simp

/-- The norm of `w = ±I`. -/
theorem norm_axis_w {w : ℂ} (hw : w = Complex.I ∨ w = -Complex.I) : ‖w‖ = 1 := by
  rcases hw with rfl | rfl <;> simp

/-! ## 2. The pointwise derivative bound at a point with clearance `≥ Rde` -/

/-- Pointwise form of Lemma A.2.4 at a point `z` whose ball of radius `Rde` lies in the gate
(expressed by the hypothesis `hclear` on the two margins): the deviation `Φ' - 1` is bounded by
`√2 C₂ / min margA margB` plus the `1/v`-correction `(32/31)‖F z - (z+1)‖`. -/
theorem deriv_le_of_clear {Ξ Rde C₂ : ℝ} {α : ℂ} {F Φ : ℂ → ℂ} {z : ℂ}
    (hRde : 0 < Rde)
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hclear : Real.sqrt 2 * Rde ≤ min (Work.Pert.margA Ξ α z) (Work.Pert.margB Ξ α z)) :
    ‖deriv Φ z - 1‖ ≤ Real.sqrt 2 * C₂ / min (Work.Pert.margA Ξ α z) (Work.Pert.margB Ξ α z)
      + (32 / 31) * ‖F z - (z + 1)‖ := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hmm0 : 0 < min (Work.Pert.margA Ξ α z) (Work.Pert.margB Ξ α z) := by
    nlinarith [hclear, h2, hRde]
  have hRgt : 0 < min (Work.Pert.margA Ξ α z) (Work.Pert.margB Ξ α z) / Real.sqrt 2 := by
    positivity
  have hRde' : Rde ≤ min (Work.Pert.margA Ξ α z) (Work.Pert.margB Ξ α z) / Real.sqrt 2 := by
    rw [le_div_iff₀ h2]; linarith
  have hball : Metric.ball z (min (Work.Pert.margA Ξ α z) (Work.Pert.margB Ξ α z)
      / Real.sqrt 2) ⊆ Work.Pert.Qm Ξ α := by
    refine Work.Pert.ball_subset_Qm_of_marg_le (le_of_lt hRgt) ?_
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt h2)]
  have hmain := Work.Pert.Pin3.dev_deriv_le_pt hDE hNT.1.1 (fun u hu => (hNT.1.2 u hu).1)
    hΦ.1 hΦ.2.1 hΦ.2.2 hRgt hRde' hball
  have hval : C₂ / (min (Work.Pert.margA Ξ α z) (Work.Pert.margB Ξ α z) / Real.sqrt 2)
      = Real.sqrt 2 * C₂ / min (Work.Pert.margA Ξ α z) (Work.Pert.margB Ξ α z) := by
    rw [div_div_eq_mul_div]; ring
  rwa [hval] at hmain

/-! ## 3. Transport along the line `s ↦ s • w` -/

/-- Fundamental estimate "displacement ≤ integral of the speed" along the line `s ↦ s • w`,
`‖w‖ = 1`. -/
theorem axis_dev_le {Φ : ℂ → ℂ} {w : ℂ} (hw : ‖w‖ = 1) {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hdiff : ∀ s ∈ Set.Icc a b, DifferentiableAt ℂ Φ ((s : ℂ) * w))
    (hbound : ∀ s ∈ Set.Icc a b, ‖deriv Φ ((s : ℂ) * w) - 1‖ ≤ g s)
    (hgcont : ContinuousOn g (Set.Icc a b)) :
    ‖(Φ ((b : ℂ) * w) - (b : ℂ) * w) - (Φ ((a : ℂ) * w) - (a : ℂ) * w)‖ ≤
      ∫ s in a..b, g s := by
  let γ : ℝ → ℂ := fun s => (s : ℂ) * w
  let f : ℝ → ℂ := fun s => Φ (γ s) - γ s
  have hγ : ∀ s : ℝ, HasDerivAt γ w s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) * w) (1 * w) s := h1.mul_const w
    simpa [γ, one_mul] using h2
  have hfd : ∀ s ∈ Set.Icc a b, HasDerivAt f ((deriv Φ (γ s) - 1) * w) s := by
    intro s hs
    have hcomp : HasDerivAt (fun u : ℝ => Φ (γ u)) (deriv Φ (γ s) * w) s :=
      (hdiff s hs).hasDerivAt.comp s (hγ s)
    have hsub : HasDerivAt (fun u : ℝ => Φ (γ u) - γ u) (deriv Φ (γ s) * w - w) s :=
      hcomp.sub (hγ s)
    have he : deriv Φ (γ s) * w - w = (deriv Φ (γ s) - 1) * w := by ring
    rw [he] at hsub
    simpa [f] using hsub
  have hmain := norm_sub_le_integral_of_norm_deriv_le_of_le (f := f) (B := g) (a := a) (b := b)
    hab
    (fun s hs => (hfd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hfd s (Set.Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt)
    (by
      filter_upwards with s hs
      rw [(hfd s (Set.Ioo_subset_Icc_self hs)).deriv, norm_mul, hw, mul_one]
      exact hbound s (Set.Ioo_subset_Icc_self hs))
    (by
      have h : ContinuousOn g (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
      exact h.intervalIntegrable)
  simpa only [f, γ] using hmain

/-! ## 4. Two elementary integrals -/

theorem integral_one_div_sub {Ξ a b : ℝ} (ha : Ξ < a) (hab : a ≤ b) :
    (∫ s in a..b, (1 : ℝ) / (s - Ξ)) = Real.log ((b - Ξ) / (a - Ξ)) := by
  have hderiv : ∀ s ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ => Real.log (u - Ξ)) (1 / (s - Ξ)) s := by
    intro s hs
    rw [Set.uIcc_of_le hab] at hs
    have hs1 : 0 < s - Ξ := by have := hs.1; linarith
    have h1 : HasDerivAt (fun u : ℝ => u - Ξ) 1 s := (hasDerivAt_id s).sub_const Ξ
    exact h1.log (ne_of_gt hs1)
  have hint : IntervalIntegrable (fun s : ℝ => (1 : ℝ) / (s - Ξ)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    refine ContinuousOn.div₀ continuousOn_const (continuousOn_id.sub continuousOn_const) ?_
    intro s hs
    have hs1 : 0 < s - Ξ := by have := hs.1; linarith
    exact ne_of_gt hs1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have ha1 : 0 < a - Ξ := by linarith
  have hb1 : 0 < b - Ξ := by linarith
  rw [Real.log_div (ne_of_gt hb1) (ne_of_gt ha1)]

theorem integral_one_div_self {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, (1 : ℝ) / s) = Real.log (b / a) := by
  have hderiv : ∀ s ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => Real.log u) (1 / s) s := by
    intro s hs
    rw [Set.uIcc_of_le hab] at hs
    have hs1 : 0 < s := by have := hs.1; linarith
    simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hs1)
  have hint : IntervalIntegrable (fun s : ℝ => (1 : ℝ) / s) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    refine ContinuousOn.div₀ continuousOn_const continuousOn_id ?_
    intro s hs
    have hs1 : 0 < s := by have := hs.1; linarith
    exact ne_of_gt hs1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hb1 : 0 < b := lt_of_lt_of_le ha hab
  rw [Real.log_div (ne_of_gt hb1) (ne_of_gt ha)]


/-! ## 5. The constants of `anchor_to_all_t` -/

/-- The length of the walk used to reach the corridor at the bad heights. -/
def Nlen (Rde : ℝ) : ℕ := ⌈32 * (Real.sqrt 2 * Rde + 1) / 31⌉₊

/-- An explicit bound for the deviation across the bad window. -/
def Kbad (Rde C₂ : ℝ) : ℝ :=
  (Nlen Rde : ℝ) / 16 + (C₂ / Rde + 1 / 31) * (2 * Real.sqrt 2 * Rde + (Nlen Rde : ℝ) / 8) + 1

/-- The logarithmic coefficient of the final bound. -/
def Aconst (C₂ Kd : ℝ) : ℝ := 6 * Real.sqrt 2 * C₂ + (64 / 31) * Kd + 1

/-- The constant term of the final bound. -/
def Cconst (K₁ Kb : ℝ) : ℝ := K₁ + Kb + 1

end

end Work.Pert.PinLogDev
