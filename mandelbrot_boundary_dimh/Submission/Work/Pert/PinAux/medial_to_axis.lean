import Mathlib
import Submission.Work.Pert.PinAux.Defs
import Submission.Work.Pert.PinAux.dev_vert_log_affine
import Submission.Work.Pert.PinAux.dev_vert_log_affine_dn
import Submission.Work.Pert.PinAux.near_pinch_dev_bound

namespace Work.Pert.PinAux

open MandelDim Complex Metric
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

/-- The triangle inequality in the `‖a - b‖` form with an intermediate point. -/
theorem norm_sub_sub_le (a b c : ℂ) : ‖a - b‖ ≤ ‖a - c‖ + ‖c - b‖ := by
  have h := dist_triangle a c b
  simpa [dist_eq_norm] using h

/-- Pointwise derivative bound at a point of the gate with an inscribed ball of radius `R`. -/
theorem deriv_bound_at {F Φ : ℂ → ℂ} {Ξ Rde C₂ cc K R : ℝ} {α : ℂ} {w : ℂ}
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hsharp : ∀ w ∈ Work.Pert.Qm Ξ α, ‖F w - (w + 1)‖ ≤ K / ‖w‖ + cc)
    (hR : 0 < R) (hRde : Rde ≤ R) (hball : Metric.ball w R ⊆ Work.Pert.Qm Ξ α) :
    ‖deriv Φ w - 1‖ ≤ C₂ / R + (32 / 31) * (K / ‖w‖ + cc) := by
  have h1 := Work.Pert.Pin3.dev_deriv_le_pt hDE hNT.1.1 (fun z hz => (hNT.1.2 z hz).1) hΦ.1 hΦ.2.1 hΦ.2.2 hR hRde hball
  have h2 : ‖F w - (w + 1)‖ ≤ K / ‖w‖ + cc := hsharp w (hball (Metric.mem_ball_self hR))
  have h33 : (0 : ℝ) ≤ 32 / 31 := by norm_num
  calc ‖deriv Φ w - 1‖ ≤ C₂ / R + 32 / 31 * ‖F w - (w + 1)‖ := h1
    _ ≤ C₂ / R + 32 / 31 * (K / ‖w‖ + cc) := by
        have := mul_le_mul_of_nonneg_left h2 h33
        linarith

/-- **Upper-wing walk bound.**  For `t ≥ Tu` (with `Tu` a base height in the upper wing, strictly
above the pinch and at clearance at least `Rde`), the deviation between `med Ξ α t` and
`med Ξ α Tu` is bounded by the integral of the majorant along the vertical medial line. -/
theorem walk_up {F Φ : ℂ → ℂ} {α : ℂ} {Ξ Rde C₂ c K Tu t : ℝ}
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hsharp : ∀ w ∈ Work.Pert.Qm Ξ α, ‖F w - (w + 1)‖ ≤ K / ‖w‖ + c)
    (hK : 0 ≤ K) (hc0 : 0 ≤ c) (hC₂ : 0 ≤ C₂)
    (hTu0 : 0 < Tu) (hTug : -(1 / α).im ≤ Tu) (hTut : tPlus Ξ α < Tu)
    (hTuc : Real.sqrt 2 * Rde ≤ Tu - tPlus Ξ α) (hht : Tu ≤ t) :
    ‖Dev Φ (med Ξ α t) - Dev Φ (med Ξ α Tu)‖
      ≤ C₂ * Real.sqrt 2 * Real.log ((t - tPlus Ξ α) / (Tu - tPlus Ξ α))
        + (32 / 31) * K * Real.log (t / Tu) + (32 / 31) * c * (t - Tu) := by
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have ht0 : 0 ≤ t := le_of_lt (lt_of_lt_of_le hTu0 hht)
  have htg : -(1 / α).im ≤ t := le_trans hTug hht
  -- pointwise derivative bound along the segment
  have hbound : ∀ s ∈ Set.Icc Tu t,
      ‖deriv Φ ((xInf α : ℂ) + (s : ℂ) * Complex.I) - 1‖
        ≤ C₂ * Real.sqrt 2 / (s - tPlus Ξ α) + (32 / 31) * K / s + (32 / 31) * c := by
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt (lt_of_lt_of_le hTu0 hs.1)
    have hsg : -(1 / α).im ≤ s := le_trans hTug hs.1
    have hst : tPlus Ξ α < s := lt_of_lt_of_le hTut hs.1
    have hspos : 0 < s - tPlus Ξ α := by linarith
    have hRpos : 0 < (s - tPlus Ξ α) / Real.sqrt 2 := div_pos hspos hs2
    have hRde : Rde ≤ (s - tPlus Ξ α) / Real.sqrt 2 := by
      rw [le_div_iff₀ hs2]
      have h1 : (Tu - tPlus Ξ α) ≤ s - tPlus Ξ α := by linarith [hs.1]
      linarith [hTuc]
    have hball : Metric.ball ((xInf α : ℂ) + (s : ℂ) * Complex.I) ((s - tPlus Ξ α) / Real.sqrt 2)
        ⊆ Work.Pert.Qm Ξ α := ball_xInf_subset_Qm hs0 hsg hst
    have h1 := deriv_bound_at hDE hNT hΦ hsharp hRpos hRde hball
    have h2 : 1 / ‖(xInf α : ℂ) + (s : ℂ) * Complex.I‖ ≤ 1 / s := by
      have hle : s ≤ ‖(xInf α : ℂ) + (s : ℂ) * Complex.I‖ := by
        have him : ((xInf α : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
        calc s = |((xInf α : ℂ) + (s : ℂ) * Complex.I).im| := by rw [him, abs_of_nonneg hs0]
          _ ≤ ‖(xInf α : ℂ) + (s : ℂ) * Complex.I‖ := abs_im_le_norm _
      exact one_div_le_one_div_of_le (lt_of_lt_of_le hTu0 hs.1) hle
    have h3 : C₂ / ((s - tPlus Ξ α) / Real.sqrt 2) = C₂ * Real.sqrt 2 / (s - tPlus Ξ α) := by
      field_simp
    have h4 : (32 / 31) * (K / ‖(xInf α : ℂ) + (s : ℂ) * Complex.I‖ + c)
        ≤ (32 / 31) * K / s + (32 / 31) * c := by
      have h32 : (0 : ℝ) ≤ 32 / 31 := by norm_num
      have h5 : K / ‖(xInf α : ℂ) + (s : ℂ) * Complex.I‖ ≤ K / s := by
        simp only [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using h2) hK
      have h6 : (32 / 31) * (K / ‖(xInf α : ℂ) + (s : ℂ) * Complex.I‖ + c)
          ≤ (32 / 31) * (K / s + c) := mul_le_mul_of_nonneg_left (by linarith) h32
      have h7 : (32 / 31) * (K / s + c) = (32 / 31) * K / s + (32 / 31) * c := by ring
      rw [h7] at h6
      exact h6
    rw [h3] at h1
    linarith
  -- differentiability along the segment
  have hdiff : ∀ s ∈ Set.Icc Tu t, DifferentiableAt ℂ Φ ((xInf α : ℂ) + (s : ℂ) * Complex.I) := by
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt (lt_of_lt_of_le hTu0 hs.1)
    have hsg : -(1 / α).im ≤ s := le_trans hTug hs.1
    have hst : tPlus Ξ α < s := lt_of_lt_of_le hTut hs.1
    exact hΦ.1.differentiableAt ((isOpen_Qm Ξ α).mem_nhds (mem_Qm_xInf hs0 hsg hst))
  have hA : (0 : ℝ) ≤ C₂ * Real.sqrt 2 := mul_nonneg hC₂ (Real.sqrt_nonneg 2)
  have hB : (0 : ℝ) ≤ (32 / 31) * K := by positivity
  have hCc : (0 : ℝ) ≤ (32 / 31) * c := by positivity
  have hwalk := dev_vert_log_affine (Φ := Φ) (x := xInf α) (t₀ := tPlus Ξ α) (T := Tu) (M := t)
    (A := C₂ * Real.sqrt 2) (B := (32 / 31) * K) (cc := (32 / 31) * c)
    hht hTut hTu0 hdiff hbound hA hB hCc
  -- rewrite the endpoints as medial points
  rw [← med_eq_xInf ht0 htg, ← med_eq_xInf (le_of_lt hTu0) hTug] at hwalk
  exact hwalk

/-- **Lower-wing walk bound.**  For `t ≤ -Tl` (with `Tl` a base height in the lower wing, strictly
above the pinch in absolute value and at clearance at least `Rde`). -/
theorem walk_dn {F Φ : ℂ → ℂ} {α : ℂ} {Ξ Rde C₂ c K Tl t : ℝ}
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hsharp : ∀ w ∈ Work.Pert.Qm Ξ α, ‖F w - (w + 1)‖ ≤ K / ‖w‖ + c)
    (hK : 0 ≤ K) (hc0 : 0 ≤ c) (hC₂ : 0 ≤ C₂)
    (hTl0 : 0 < Tl) (hTlg : (1 / α).im ≤ Tl) (hTlt : tMinus Ξ α < Tl)
    (hTlc : Real.sqrt 2 * Rde ≤ Tl - tMinus Ξ α) (hlt : t ≤ -Tl) :
    ‖Dev Φ (med Ξ α t) - Dev Φ (med Ξ α (-Tl))‖
      ≤ C₂ * Real.sqrt 2 * Real.log ((|t| - tMinus Ξ α) / (Tl - tMinus Ξ α))
        + (32 / 31) * K * Real.log (|t| / Tl) + (32 / 31) * c * (|t| - Tl) := by
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have ht0 : t ≤ 0 := le_trans hlt (by linarith)
  have htg : t ≤ -(1 / α).im := le_trans hlt (by linarith)
  have htabs : |t| = -t := abs_of_nonpos ht0
  -- pointwise derivative bound along the segment
  have hbound : ∀ s ∈ Set.Icc t (-Tl),
      ‖deriv Φ ((xInfNeg α : ℂ) + (s : ℂ) * Complex.I) - 1‖
        ≤ C₂ * Real.sqrt 2 / (-tMinus Ξ α - s) + (32 / 31) * K / (-s) + (32 / 31) * c := by
    intro s hs
    have hs0 : s ≤ 0 := le_trans hs.2 (by linarith)
    have hsg : s ≤ -(1 / α).im := le_trans hs.2 (by linarith)
    have hst : s < -tMinus Ξ α := lt_of_le_of_lt hs.2 (by linarith)
    have hspos : 0 < -s - tMinus Ξ α := by linarith [hst]
    have hneg : 0 < -s := by linarith [hs.2, hTl0]
    have hRpos : 0 < (-s - tMinus Ξ α) / Real.sqrt 2 := div_pos hspos hs2
    have hRde : Rde ≤ (-s - tMinus Ξ α) / Real.sqrt 2 := by
      rw [le_div_iff₀ hs2]
      have h1 : (Tl - tMinus Ξ α) ≤ -s - tMinus Ξ α := by linarith [hs.2]
      linarith [hTlc]
    have hball : Metric.ball ((xInfNeg α : ℂ) + (s : ℂ) * Complex.I)
        ((-s - tMinus Ξ α) / Real.sqrt 2) ⊆ Work.Pert.Qm Ξ α :=
      ball_xInfNeg_subset_Qm hs0 hsg hst
    have h1 := deriv_bound_at hDE hNT hΦ hsharp hRpos hRde hball
    have h2 : 1 / ‖(xInfNeg α : ℂ) + (s : ℂ) * Complex.I‖ ≤ 1 / (-s) := by
      have hle : -s ≤ ‖(xInfNeg α : ℂ) + (s : ℂ) * Complex.I‖ := by
        have him : ((xInfNeg α : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
        calc -s = |((xInfNeg α : ℂ) + (s : ℂ) * Complex.I).im| := by
              rw [him, abs_of_nonpos hs0]
          _ ≤ ‖(xInfNeg α : ℂ) + (s : ℂ) * Complex.I‖ := abs_im_le_norm _
      exact one_div_le_one_div_of_le hneg hle
    have h3 : C₂ / ((-s - tMinus Ξ α) / Real.sqrt 2) = C₂ * Real.sqrt 2 / (-tMinus Ξ α - s) := by
      rw [div_div_eq_mul_div]
      congr 1
      ring
    have h4 : (32 / 31) * (K / ‖(xInfNeg α : ℂ) + (s : ℂ) * Complex.I‖ + c)
        ≤ (32 / 31) * K / (-s) + (32 / 31) * c := by
      have h32 : (0 : ℝ) ≤ 32 / 31 := by norm_num
      have h5 : K / ‖(xInfNeg α : ℂ) + (s : ℂ) * Complex.I‖ ≤ K / (-s) := by
        simp only [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using h2) hK
      have h6 : (32 / 31) * (K / ‖(xInfNeg α : ℂ) + (s : ℂ) * Complex.I‖ + c)
          ≤ (32 / 31) * (K / (-s) + c) := mul_le_mul_of_nonneg_left (by linarith) h32
      have h7 : (32 / 31) * (K / (-s) + c) = (32 / 31) * K / (-s) + (32 / 31) * c := by ring
      rw [h7] at h6
      exact h6
    rw [h3] at h1
    linarith
  -- differentiability along the segment
  have hdiff : ∀ s ∈ Set.Icc t (-Tl),
      DifferentiableAt ℂ Φ ((xInfNeg α : ℂ) + (s : ℂ) * Complex.I) := by
    intro s hs
    have hs0 : s ≤ 0 := le_trans hs.2 (by linarith)
    have hsg : s ≤ -(1 / α).im := le_trans hs.2 (by linarith)
    have hst : s < -tMinus Ξ α := lt_of_le_of_lt hs.2 (by linarith)
    exact hΦ.1.differentiableAt ((isOpen_Qm Ξ α).mem_nhds (mem_Qm_xInfNeg hs0 hsg hst))
  have hA : (0 : ℝ) ≤ C₂ * Real.sqrt 2 := mul_nonneg hC₂ (Real.sqrt_nonneg 2)
  have hB : (0 : ℝ) ≤ (32 / 31) * K := by positivity
  have hCc : (0 : ℝ) ≤ (32 / 31) * c := by positivity
  have hwalk := dev_vert_log_affine_dn (Φ := Φ) (x := xInfNeg α) (t₀ := -tMinus Ξ α)
    (T := t) (M := -Tl) (A := C₂ * Real.sqrt 2) (B := (32 / 31) * K) (cc := (32 / 31) * c)
    (by linarith) (by linarith : -Tl < -tMinus Ξ α) (by linarith) hdiff hbound hA hB hCc
  -- rewrite the arguments in the stated form
  have e1 : -tMinus Ξ α - t = |t| - tMinus Ξ α := by rw [htabs]; ring
  have e2 : -tMinus Ξ α - (-Tl) = Tl - tMinus Ξ α := by ring
  have e3 : t / (-Tl) = |t| / Tl := by rw [htabs]; ring
  have e4 : -Tl - t = |t| - Tl := by rw [htabs]; ring
  rw [e1, e2, e3, e4] at hwalk
  -- rewrite the endpoints as medial points
  have hM : med Ξ α (-Tl) = (xInfNeg α : ℂ) + (((-Tl) : ℝ) : ℂ) * Complex.I :=
    med_eq_xInfNeg (by linarith) (by linarith)
  have hT : med Ξ α t = (xInfNeg α : ℂ) + (t : ℂ) * Complex.I := med_eq_xInfNeg ht0 htg
  rw [← hM, ← hT] at hwalk
  rwa [norm_sub_rev] at hwalk

theorem medial_to_axis {F Φ : ℂ → ℂ} {α : ℂ} {Ξ c Y₀ R₁ : ℝ}
    (hΞ : 0 < Ξ) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 256) (hY₀ : 0 < Y₀) (hR₁ : 0 < R₁)
    (hDE : MandelDim.FatouDerivEstimate)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hsharp : ∃ K : ℝ, 0 < K ∧ ∀ w ∈ Work.Pert.Qm Ξ α,
      ‖F w - (w + 1)‖ ≤ K / ‖w‖ + c) :
    ∃ C Λ : ℝ, 0 < C ∧ 0 ≤ Λ ∧ Λ ≤ 2 * (c / (1 - c)) ∧
      ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α → Metric.ball z R₁ ⊆ Work.Pert.Qm Ξ α →
        ∃ T : ℝ, Y₀ ≤ T ∧ T ≤ Y₀ + 1 ∧
          (‖Work.Pert.PinAux.Dev Φ (Work.Pert.PinAux.med Ξ α z.im) - Work.Pert.PinAux.Dev Φ (T * Complex.I)‖
              ≤ C * (1 + Real.log (2 + ‖z‖)) + Λ * (|z.im - T| + 1) ∧
           ‖Work.Pert.PinAux.Dev Φ (Work.Pert.PinAux.med Ξ α z.im) - Work.Pert.PinAux.Dev Φ (-(T * Complex.I))‖
              ≤ C * (1 + Real.log (2 + ‖z‖)) + Λ * (|z.im + T| + 1)) := by
  obtain ⟨K, hKpos, hsharp⟩ := hsharp
  obtain ⟨Rde, C₁, C₂, hRdepos, hC₁pos, hC₂pos, hDE⟩ := hDE
  have hK : 0 ≤ K := le_of_lt hKpos
  have hC₂ : 0 ≤ C₂ := le_of_lt hC₂pos
  set Tu : ℝ := max (max 0 (-(1 / α).im)) (max (tPlus Ξ α + Real.sqrt 2 * Rde) 0) + 1 with hTu
  set Tl : ℝ := max (max 0 ((1 / α).im)) (max (tMinus Ξ α + Real.sqrt 2 * Rde) 0) + 1 with hTl
  set Tmax : ℝ := max Tu Tl with hTmax
  set Tref : ℝ := Y₀ + 1 with hTref
  set Λ : ℝ := 2 * (c / (1 - c)) with hΛ
  have hTu0 : 0 < Tu := by rw [hTu]; positivity
  have hTug : -(1 / α).im ≤ Tu := by
    rw [hTu]
    have h1 : -(1 / α).im ≤ max 0 (-(1 / α).im) := le_max_right _ _
    have h2 : max 0 (-(1 / α).im) ≤ max (max 0 (-(1 / α).im))
        (max (tPlus Ξ α + Real.sqrt 2 * Rde) 0) := le_max_left _ _
    linarith
  have hTut : tPlus Ξ α < Tu := by
    rw [hTu]
    have h1 : tPlus Ξ α + Real.sqrt 2 * Rde ≤ max (tPlus Ξ α + Real.sqrt 2 * Rde) 0 :=
      le_max_left _ _
    have h2 : max (tPlus Ξ α + Real.sqrt 2 * Rde) 0 ≤ max (max 0 (-(1 / α).im))
        (max (tPlus Ξ α + Real.sqrt 2 * Rde) 0) := le_max_right _ _
    have hs : 0 < Real.sqrt 2 * Rde := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hRdepos
    linarith
  have hTuc : Real.sqrt 2 * Rde ≤ Tu - tPlus Ξ α := by
    rw [hTu]
    have h1 : tPlus Ξ α + Real.sqrt 2 * Rde ≤ max (tPlus Ξ α + Real.sqrt 2 * Rde) 0 :=
      le_max_left _ _
    have h2 : max (tPlus Ξ α + Real.sqrt 2 * Rde) 0 ≤ max (max 0 (-(1 / α).im))
        (max (tPlus Ξ α + Real.sqrt 2 * Rde) 0) := le_max_right _ _
    linarith
  have hTl0 : 0 < Tl := by rw [hTl]; positivity
  have hTlg : (1 / α).im ≤ Tl := by
    rw [hTl]
    have h1 : (1 / α).im ≤ max 0 ((1 / α).im) := le_max_right _ _
    have h2 : max 0 ((1 / α).im) ≤ max (max 0 ((1 / α).im))
        (max (tMinus Ξ α + Real.sqrt 2 * Rde) 0) := le_max_left _ _
    linarith
  have hTlt : tMinus Ξ α < Tl := by
    rw [hTl]
    have h1 : tMinus Ξ α + Real.sqrt 2 * Rde ≤ max (tMinus Ξ α + Real.sqrt 2 * Rde) 0 :=
      le_max_left _ _
    have h2 : max (tMinus Ξ α + Real.sqrt 2 * Rde) 0 ≤ max (max 0 ((1 / α).im))
        (max (tMinus Ξ α + Real.sqrt 2 * Rde) 0) := le_max_right _ _
    have hs : 0 < Real.sqrt 2 * Rde := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hRdepos
    linarith
  have hTlc : Real.sqrt 2 * Rde ≤ Tl - tMinus Ξ α := by
    rw [hTl]
    have h1 : tMinus Ξ α + Real.sqrt 2 * Rde ≤ max (tMinus Ξ α + Real.sqrt 2 * Rde) 0 :=
      le_max_left _ _
    have h2 : max (tMinus Ξ α + Real.sqrt 2 * Rde) 0 ≤ max (max 0 ((1 / α).im))
        (max (tMinus Ξ α + Real.sqrt 2 * Rde) 0) := le_max_right _ _
    linarith
  have hTu1 : 1 ≤ Tu := by
    rw [hTu]
    have h1 : max 0 (-(1 / α).im) ≤ max (max 0 (-(1 / α).im)) (max (tPlus Ξ α + Real.sqrt 2 * Rde) 0) :=
      le_max_left _ _
    have h2 : (0 : ℝ) ≤ max 0 (-(1 / α).im) := le_max_left _ _
    linarith
  have hTl1 : 1 ≤ Tl := by
    rw [hTl]
    have h1 : max 0 ((1 / α).im) ≤ max (max 0 ((1 / α).im)) (max (tMinus Ξ α + Real.sqrt 2 * Rde) 0) :=
      le_max_left _ _
    have h2 : (0 : ℝ) ≤ max 0 ((1 / α).im) := le_max_left _ _
    linarith
  have hTuTmax : Tu ≤ Tmax := by rw [hTmax]; exact le_max_left _ _
  have hTlTmax : Tl ≤ Tmax := by rw [hTmax]; exact le_max_right _ _
  obtain ⟨M₀, hM₀pos, hM₀⟩ :=
    near_pinch_dev_bound (Φ := Φ) (Ξ := Ξ) (α := α) (R₁ := R₁) (Tmax := Tmax) hR₁ hΦ.1
  set LUp : ℝ := C₂ * Real.sqrt 2 * (Real.log (1 + |tPlus Ξ α|) + |Real.log (Tu - tPlus Ξ α)|)
    with hLUp
  set LDown : ℝ := C₂ * Real.sqrt 2 * (Real.log (1 + |tMinus Ξ α|) + |Real.log (Tl - tMinus Ξ α)|)
    with hLDown
  set Dref : ℝ := ‖Dev Φ (med Ξ α Tu)‖ + ‖Dev Φ (med Ξ α (-Tl))‖ + ‖Dev Φ (Tref * Complex.I)‖
    + ‖Dev Φ (-(Tref * Complex.I))‖ with hDref
  set C : ℝ := max 1 (C₂ * Real.sqrt 2 + (32 / 31) * K + LUp + LDown + (32 / 31) * c * Tref
    + Dref + M₀) with hC
  have hCpos : 0 < C := by rw [hC]; exact lt_of_lt_of_le one_pos (le_max_left 1 _)
  have hCge1 : (1 : ℝ) ≤ C := by rw [hC]; exact le_max_left 1 _
  have hCge : C₂ * Real.sqrt 2 + (32 / 31) * K + LUp + LDown + (32 / 31) * c * Tref + Dref + M₀ ≤ C := by
    rw [hC]; exact le_max_right 1 _
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; exact mul_nonneg (by norm_num) (div_nonneg hc0 (by linarith))
  have hΛle : Λ ≤ 2 * (c / (1 - c)) := by rw [hΛ]
  -- `(32/31) c ≤ Λ`
  have hCc_le_Λ : (32 / 31) * c ≤ Λ := by
    rw [hΛ]
    have h1 : 0 < 1 - c := by linarith
    rw [show (2 : ℝ) * (c / (1 - c)) = 2 * c / (1 - c) by ring]
    rw [le_div_iff₀ h1]
    nlinarith [hc0, hc]
  have hA₁ : (0 : ℝ) ≤ C₂ * Real.sqrt 2 := mul_nonneg hC₂ (Real.sqrt_nonneg 2)
  have hB₁ : (0 : ℝ) ≤ (32 / 31) * K := by positivity
  have hCc : (0 : ℝ) ≤ (32 / 31) * c := by positivity
  have hlogUnn : 0 ≤ Real.log (1 + |tPlus Ξ α|) + |Real.log (Tu - tPlus Ξ α)| := by
    have h1 : 0 ≤ Real.log (1 + |tPlus Ξ α|) :=
      Real.log_nonneg (by linarith [abs_nonneg (tPlus Ξ α)])
    have h2 : 0 ≤ |Real.log (Tu - tPlus Ξ α)| := abs_nonneg _
    linarith
  have hlogDnn : 0 ≤ Real.log (1 + |tMinus Ξ α|) + |Real.log (Tl - tMinus Ξ α)| := by
    have h1 : 0 ≤ Real.log (1 + |tMinus Ξ α|) :=
      Real.log_nonneg (by linarith [abs_nonneg (tMinus Ξ α)])
    have h2 : 0 ≤ |Real.log (Tl - tMinus Ξ α)| := abs_nonneg _
    linarith
  have hLUpnn : 0 ≤ LUp := by rw [hLUp]; exact mul_nonneg hA₁ hlogUnn
  have hLDownnn : 0 ≤ LDown := by rw [hLDown]; exact mul_nonneg hA₁ hlogDnn
  have hDrefnn : 0 ≤ Dref := by
    rw [hDref]
    have h1 : 0 ≤ ‖Dev Φ (med Ξ α Tu)‖ := norm_nonneg _
    have h2 : 0 ≤ ‖Dev Φ (med Ξ α (-Tl))‖ := norm_nonneg _
    have h3 : 0 ≤ ‖Dev Φ (Tref * Complex.I)‖ := norm_nonneg _
    have h4 : 0 ≤ ‖Dev Φ (-(Tref * Complex.I))‖ := norm_nonneg _
    linarith
  have hTrefpos : 0 < Tref := by rw [hTref]; linarith
  have hcoef_le : C₂ * Real.sqrt 2 + (32 / 31) * K ≤ C := by
    linarith [hCge, hLUpnn, hLDownnn, hCc, le_of_lt hM₀pos, hDrefnn,
      mul_nonneg hCc (le_of_lt hTrefpos)]
  have hconst_le : LUp + (32 / 31) * c * Tref + Dref ≤ C := by
    have h2 : 0 ≤ M₀ := le_of_lt hM₀pos
    linarith [hCge, hA₁, hB₁, hLUpnn, hLDownnn, mul_nonneg hCc (le_of_lt hTrefpos)]
  have hconst_le_dn : LDown + (32 / 31) * c * Tref + Dref ≤ C := by
    have h2 : 0 ≤ M₀ := le_of_lt hM₀pos
    linarith [hCge, hA₁, hB₁, hLUpnn, hLDownnn, mul_nonneg hCc (le_of_lt hTrefpos)]
  have hTref1 : Y₀ ≤ Tref := by rw [hTref]; linarith
  have hTref2 : Tref ≤ Y₀ + 1 := by rw [hTref]
  refine ⟨C, Λ, hCpos, hΛ0, hΛle, ?_⟩
  intro z hzQ hzball
  have hmed_ge := marg_med_ge_of_ball (Ξ := Ξ) (R₁ := R₁) (α := α) (z := z) hR₁ hzball
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have him_le : z.im ≤ ‖z‖ := le_trans (le_abs_self _) (Complex.abs_im_le_norm z)
  have habs_le : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hlognn : (0 : ℝ) ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith)
  have hmain : (‖Work.Pert.PinAux.Dev Φ (Work.Pert.PinAux.med Ξ α z.im) - Work.Pert.PinAux.Dev Φ (Tref * Complex.I)‖
          ≤ C * (1 + Real.log (2 + ‖z‖)) + Λ * (|z.im - Tref| + 1)) ∧
        (‖Work.Pert.PinAux.Dev Φ (Work.Pert.PinAux.med Ξ α z.im) - Work.Pert.PinAux.Dev Φ (-(Tref * Complex.I))‖
          ≤ C * (1 + Real.log (2 + ‖z‖)) + Λ * (|z.im + Tref| + 1)) := by
    -- generic endgame: turn `A log + K + Λ u` into the target shape
    have hfinish : ∀ (A K u : ℝ), A ≤ C → K ≤ C → 0 ≤ u →
        A * Real.log (2 + ‖z‖) + K + Λ * u ≤ C * (1 + Real.log (2 + ‖z‖)) + Λ * (u + 1) := by
      intro A K u hA hK hu
      have h3 : 0 ≤ Λ * (u + 1) := mul_nonneg hΛ0 (by linarith)
      have h4 : Λ * (u + 1) = Λ * u + Λ := by ring
      nlinarith [hlognn, hCge1, h3, h4]
    have hcoefA : (0 : ℝ) ≤ C₂ * Real.sqrt 2 + (32 / 31) * K := by linarith [hA₁, hB₁]
    by_cases hup : Tu ≤ z.im
    · -- ================= UPPER WING =================
      have ht0 : 0 ≤ z.im := le_of_lt (lt_of_lt_of_le hTu0 hup)
      have htg : -(1 / α).im ≤ z.im := le_trans hTug hup
      have hwalk := walk_up (fun Φ' v z' R h1 h2 h3 h4 h5 h6 => (hDE Φ' v z' R h1 h2 h3 h4 h5 h6).2)
        hNT hΦ hsharp hK hc0 hC₂ hTu0 hTug hTut hTuc hup
      have ht0' : 0 < z.im - tPlus Ξ α := by linarith
      have hTup : 0 < Tu - tPlus Ξ α := by linarith
      have hkey : z.im - tPlus Ξ α ≤ (2 + ‖z‖) * (1 + |tPlus Ξ α|) := by
        have h2 : tPlus Ξ α ≤ |tPlus Ξ α| := le_abs_self _
        have h3 : -(tPlus Ξ α) ≤ |tPlus Ξ α| := neg_le_abs _
        nlinarith [him_le, hznn, abs_nonneg (tPlus Ξ α)]
      have hlog1 : Real.log ((z.im - tPlus Ξ α) / (Tu - tPlus Ξ α))
          ≤ Real.log (2 + ‖z‖) + (Real.log (1 + |tPlus Ξ α|) + |Real.log (Tu - tPlus Ξ α)|) := by
        rw [Real.log_div (ne_of_gt ht0') (ne_of_gt hTup)]
        have h5 : Real.log (z.im - tPlus Ξ α) ≤ Real.log (2 + ‖z‖) + Real.log (1 + |tPlus Ξ α|) := by
          have h := Real.log_le_log ht0' hkey
          rw [Real.log_mul (by linarith) (by positivity)] at h
          exact h
        have h6 : -Real.log (Tu - tPlus Ξ α) ≤ |Real.log (Tu - tPlus Ξ α)| := neg_le_abs _
        linarith
      have hlog2 : Real.log (z.im / Tu) ≤ Real.log (2 + ‖z‖) := by
        have h1 : Real.log (z.im / Tu) ≤ Real.log z.im := by
          rw [Real.log_div (ne_of_gt (lt_of_lt_of_le hTu0 hup)) (ne_of_gt hTu0)]
          have h2 : 0 ≤ Real.log Tu := Real.log_nonneg hTu1
          linarith
        have h3 : Real.log z.im ≤ Real.log (2 + ‖z‖) :=
          Real.log_le_log (lt_of_lt_of_le hTu0 hup) (by linarith)
        linarith
      have hlogmain : C₂ * Real.sqrt 2 * Real.log ((z.im - tPlus Ξ α) / (Tu - tPlus Ξ α))
          + (32 / 31) * K * Real.log (z.im / Tu)
          ≤ (C₂ * Real.sqrt 2 + (32 / 31) * K) * Real.log (2 + ‖z‖) + LUp := by
        have h1 : C₂ * Real.sqrt 2 * Real.log ((z.im - tPlus Ξ α) / (Tu - tPlus Ξ α))
            ≤ C₂ * Real.sqrt 2 * Real.log (2 + ‖z‖) + LUp := by
          have hh := mul_le_mul_of_nonneg_left hlog1 hA₁
          have he : C₂ * Real.sqrt 2 * (Real.log (2 + ‖z‖)
              + (Real.log (1 + |tPlus Ξ α|) + |Real.log (Tu - tPlus Ξ α)|))
              = C₂ * Real.sqrt 2 * Real.log (2 + ‖z‖) + LUp := by rw [hLUp]; ring
          linarith [he ▸ hh]
        have h2 : (32 / 31) * K * Real.log (z.im / Tu)
            ≤ (32 / 31) * K * Real.log (2 + ‖z‖) := mul_le_mul_of_nonneg_left hlog2 hB₁
        nlinarith [h1, h2]
      have hstep3 : (32 / 31) * c * (z.im - Tu) ≤ Λ * |z.im - Tref| + (32 / 31) * c * Tref := by
        have h1 : (32 / 31) * c * (z.im - Tu) ≤ (32 / 31) * c * z.im :=
          mul_le_mul_of_nonneg_left (by linarith) hCc
        have h2 : z.im ≤ |z.im - Tref| + Tref := by
          have := le_abs_self (z.im - Tref)
          linarith
        have h3 : (32 / 31) * c * (|z.im - Tref| + Tref)
            = (32 / 31) * c * |z.im - Tref| + (32 / 31) * c * Tref := by ring
        have h4 : (32 / 31) * c * |z.im - Tref| ≤ Λ * |z.im - Tref| :=
          mul_le_mul_of_nonneg_right hCc_le_Λ (abs_nonneg _)
        have h5 := mul_le_mul_of_nonneg_left h2 hCc
        linarith [h1, h5, h3, h4]
      have hstep3' : (32 / 31) * c * (z.im - Tu) ≤ Λ * |z.im + Tref| + (32 / 31) * c * Tref := by
        have h1 : (32 / 31) * c * (z.im - Tu) ≤ (32 / 31) * c * z.im :=
          mul_le_mul_of_nonneg_left (by linarith) hCc
        have h2 : z.im ≤ |z.im + Tref| + Tref := by
          have h6 : |z.im + Tref| = z.im + Tref := abs_of_nonneg (by linarith)
          linarith
        have h3 : (32 / 31) * c * (|z.im + Tref| + Tref)
            = (32 / 31) * c * |z.im + Tref| + (32 / 31) * c * Tref := by ring
        have h4 : (32 / 31) * c * |z.im + Tref| ≤ Λ * |z.im + Tref| :=
          mul_le_mul_of_nonneg_right hCc_le_Λ (abs_nonneg _)
        have h5 := mul_le_mul_of_nonneg_left h2 hCc
        linarith [h1, h5, h3, h4]
      have hD1 : ‖Dev Φ (med Ξ α Tu) - Dev Φ (Tref * Complex.I)‖ ≤ Dref := by
        have h := norm_sub_le (Dev Φ (med Ξ α Tu)) (Dev Φ (Tref * Complex.I))
        rw [hDref]; linarith [norm_nonneg (Dev Φ (med Ξ α (-Tl))),
          norm_nonneg (Dev Φ (-(Tref * Complex.I)))]
      have hD2 : ‖Dev Φ (med Ξ α Tu) - Dev Φ (-(Tref * Complex.I))‖ ≤ Dref := by
        have h := norm_sub_le (Dev Φ (med Ξ α Tu)) (Dev Φ (-(Tref * Complex.I)))
        rw [hDref]; linarith [norm_nonneg (Dev Φ (med Ξ α (-Tl))),
          norm_nonneg (Dev Φ (Tref * Complex.I))]
      constructor
      · calc ‖Dev Φ (med Ξ α z.im) - Dev Φ (Tref * Complex.I)‖
            ≤ (C₂ * Real.sqrt 2 + (32 / 31) * K) * Real.log (2 + ‖z‖)
                + (LUp + (32 / 31) * c * Tref + Dref) + Λ * |z.im - Tref| := by
              have ht := norm_sub_sub_le (Dev Φ (med Ξ α z.im)) (Dev Φ (Tref * Complex.I))
                (Dev Φ (med Ξ α Tu))
              linarith [ht, hwalk, hD1, hlogmain, hstep3]
          _ ≤ C * (1 + Real.log (2 + ‖z‖)) + Λ * (|z.im - Tref| + 1) :=
              hfinish (C₂ * Real.sqrt 2 + (32 / 31) * K) (LUp + (32 / 31) * c * Tref + Dref)
                |z.im - Tref| hcoef_le hconst_le (abs_nonneg _)
      · calc ‖Dev Φ (med Ξ α z.im) - Dev Φ (-(Tref * Complex.I))‖
            ≤ (C₂ * Real.sqrt 2 + (32 / 31) * K) * Real.log (2 + ‖z‖)
                + (LUp + (32 / 31) * c * Tref + Dref) + Λ * |z.im + Tref| := by
              have ht := norm_sub_sub_le (Dev Φ (med Ξ α z.im)) (Dev Φ (-(Tref * Complex.I)))
                (Dev Φ (med Ξ α Tu))
              linarith [ht, hwalk, hD2, hlogmain, hstep3']
          _ ≤ C * (1 + Real.log (2 + ‖z‖)) + Λ * (|z.im + Tref| + 1) :=
              hfinish (C₂ * Real.sqrt 2 + (32 / 31) * K) (LUp + (32 / 31) * c * Tref + Dref)
                |z.im + Tref| hcoef_le hconst_le (abs_nonneg _)
    · by_cases hdn : z.im ≤ -Tl
      · -- ================= LOWER WING =================
        have ht0 : z.im ≤ 0 := le_trans hdn (by linarith)
        have htg : z.im ≤ -(1 / α).im := le_trans hdn (by linarith)
        have htabs : |z.im| = -z.im := abs_of_nonpos ht0
        have hwalk := walk_dn (fun Φ' v z' R h1 h2 h3 h4 h5 h6 => (hDE Φ' v z' R h1 h2 h3 h4 h5 h6).2)
          hNT hΦ hsharp hK hc0 hC₂ hTl0 hTlg hTlt hTlc hdn
        have hkey : |z.im| - tMinus Ξ α ≤ (2 + ‖z‖) * (1 + |tMinus Ξ α|) := by
          have h2 : tMinus Ξ α ≤ |tMinus Ξ α| := le_abs_self _
          have h3 : -(tMinus Ξ α) ≤ |tMinus Ξ α| := neg_le_abs _
          nlinarith [habs_le, hznn, abs_nonneg (tMinus Ξ α)]
        have hpos1 : 0 < |z.im| - tMinus Ξ α := by rw [htabs]; linarith [hTlt]
        have hpos2 : 0 < Tl - tMinus Ξ α := by linarith [hTlt]
        have hlog1 : Real.log ((|z.im| - tMinus Ξ α) / (Tl - tMinus Ξ α))
            ≤ Real.log (2 + ‖z‖) + (Real.log (1 + |tMinus Ξ α|) + |Real.log (Tl - tMinus Ξ α)|) := by
          rw [Real.log_div (ne_of_gt hpos1) (ne_of_gt hpos2)]
          have h5 : Real.log (|z.im| - tMinus Ξ α)
              ≤ Real.log (2 + ‖z‖) + Real.log (1 + |tMinus Ξ α|) := by
            have h := Real.log_le_log hpos1 hkey
            rw [Real.log_mul (by linarith) (by positivity)] at h
            exact h
          have h6 : -Real.log (Tl - tMinus Ξ α) ≤ |Real.log (Tl - tMinus Ξ α)| := neg_le_abs _
          linarith
        have hlog2 : Real.log (|z.im| / Tl) ≤ Real.log (2 + ‖z‖) := by
          have h1 : Real.log (|z.im| / Tl) ≤ Real.log |z.im| := by
            rw [Real.log_div (ne_of_gt (by rw [htabs]; linarith)) (ne_of_gt hTl0)]
            have h2 : 0 ≤ Real.log Tl := Real.log_nonneg hTl1
            linarith
          have h3 : Real.log |z.im| ≤ Real.log (2 + ‖z‖) := by
            have hzpos : 0 < |z.im| := abs_pos.mpr (by intro h0; rw [h0] at hdn; linarith)
            exact Real.log_le_log hzpos (by linarith)
          linarith
        have hlogmain : C₂ * Real.sqrt 2 * Real.log ((|z.im| - tMinus Ξ α) / (Tl - tMinus Ξ α))
            + (32 / 31) * K * Real.log (|z.im| / Tl)
            ≤ (C₂ * Real.sqrt 2 + (32 / 31) * K) * Real.log (2 + ‖z‖) + LDown := by
          have h1 : C₂ * Real.sqrt 2 * Real.log ((|z.im| - tMinus Ξ α) / (Tl - tMinus Ξ α))
              ≤ C₂ * Real.sqrt 2 * Real.log (2 + ‖z‖) + LDown := by
            have hh := mul_le_mul_of_nonneg_left hlog1 hA₁
            have he : C₂ * Real.sqrt 2 * (Real.log (2 + ‖z‖)
                + (Real.log (1 + |tMinus Ξ α|) + |Real.log (Tl - tMinus Ξ α)|))
                = C₂ * Real.sqrt 2 * Real.log (2 + ‖z‖) + LDown := by rw [hLDown]; ring
            linarith [he ▸ hh]
          have h2 : (32 / 31) * K * Real.log (|z.im| / Tl)
              ≤ (32 / 31) * K * Real.log (2 + ‖z‖) := mul_le_mul_of_nonneg_left hlog2 hB₁
          nlinarith [h1, h2]
        have hstep3 : (32 / 31) * c * (|z.im| - Tl) ≤ Λ * |z.im - Tref| + (32 / 31) * c * Tref := by
          have h1 : (32 / 31) * c * (|z.im| - Tl) ≤ (32 / 31) * c * |z.im| :=
            mul_le_mul_of_nonneg_left (by linarith) hCc
          have h2 : |z.im| ≤ |z.im - Tref| + Tref := by
            rw [htabs]
            have h7 := neg_le_abs (z.im - Tref)
            linarith [le_of_lt hTrefpos]
          have h3 : (32 / 31) * c * (|z.im - Tref| + Tref)
              = (32 / 31) * c * |z.im - Tref| + (32 / 31) * c * Tref := by ring
          have h4 : (32 / 31) * c * |z.im - Tref| ≤ Λ * |z.im - Tref| :=
            mul_le_mul_of_nonneg_right hCc_le_Λ (abs_nonneg _)
          have h5 := mul_le_mul_of_nonneg_left h2 hCc
          linarith [h1, h5, h3, h4]
        have hstep3' : (32 / 31) * c * (|z.im| - Tl) ≤ Λ * |z.im + Tref| + (32 / 31) * c * Tref := by
          have h1 : (32 / 31) * c * (|z.im| - Tl) ≤ (32 / 31) * c * |z.im| :=
            mul_le_mul_of_nonneg_left (by linarith) hCc
          have h2 : |z.im| ≤ |z.im + Tref| + Tref := by
            rw [htabs]
            have h7 := neg_le_abs (z.im + Tref)
            linarith [le_of_lt hTrefpos]
          have h3 : (32 / 31) * c * (|z.im + Tref| + Tref)
              = (32 / 31) * c * |z.im + Tref| + (32 / 31) * c * Tref := by ring
          have h4 : (32 / 31) * c * |z.im + Tref| ≤ Λ * |z.im + Tref| :=
            mul_le_mul_of_nonneg_right hCc_le_Λ (abs_nonneg _)
          have h5 := mul_le_mul_of_nonneg_left h2 hCc
          linarith [h1, h5, h3, h4]
        have hD1 : ‖Dev Φ (med Ξ α (-Tl)) - Dev Φ (Tref * Complex.I)‖ ≤ Dref := by
          have h := norm_sub_le (Dev Φ (med Ξ α (-Tl))) (Dev Φ (Tref * Complex.I))
          rw [hDref]; linarith [norm_nonneg (Dev Φ (med Ξ α Tu)),
            norm_nonneg (Dev Φ (-(Tref * Complex.I)))]
        have hD2 : ‖Dev Φ (med Ξ α (-Tl)) - Dev Φ (-(Tref * Complex.I))‖ ≤ Dref := by
          have h := norm_sub_le (Dev Φ (med Ξ α (-Tl))) (Dev Φ (-(Tref * Complex.I)))
          rw [hDref]; linarith [norm_nonneg (Dev Φ (med Ξ α Tu)),
            norm_nonneg (Dev Φ (Tref * Complex.I))]
        refine ⟨?_, ?_⟩
        · calc ‖Dev Φ (med Ξ α z.im) - Dev Φ (Tref * Complex.I)‖
              ≤ (C₂ * Real.sqrt 2 + (32 / 31) * K) * Real.log (2 + ‖z‖)
                  + (LDown + (32 / 31) * c * Tref + Dref) + Λ * |z.im - Tref| := by
                have ht := norm_sub_sub_le (Dev Φ (med Ξ α z.im)) (Dev Φ (Tref * Complex.I))
                  (Dev Φ (med Ξ α (-Tl)))
                linarith [ht, hwalk, hD1, hlogmain, hstep3]
            _ ≤ C * (1 + Real.log (2 + ‖z‖)) + Λ * (|z.im - Tref| + 1) :=
                hfinish (C₂ * Real.sqrt 2 + (32 / 31) * K) (LDown + (32 / 31) * c * Tref + Dref)
                  |z.im - Tref| hcoef_le hconst_le_dn (abs_nonneg _)
        · calc ‖Dev Φ (med Ξ α z.im) - Dev Φ (-(Tref * Complex.I))‖
              ≤ (C₂ * Real.sqrt 2 + (32 / 31) * K) * Real.log (2 + ‖z‖)
                  + (LDown + (32 / 31) * c * Tref + Dref) + Λ * |z.im + Tref| := by
                have ht := norm_sub_sub_le (Dev Φ (med Ξ α z.im)) (Dev Φ (-(Tref * Complex.I)))
                  (Dev Φ (med Ξ α (-Tl)))
                linarith [ht, hwalk, hD2, hlogmain, hstep3']
            _ ≤ C * (1 + Real.log (2 + ‖z‖)) + Λ * (|z.im + Tref| + 1) :=
                hfinish (C₂ * Real.sqrt 2 + (32 / 31) * K) (LDown + (32 / 31) * c * Tref + Dref)
                  |z.im + Tref| hcoef_le hconst_le_dn (abs_nonneg _)
      · -- ================= MIDDLE (near pinch) =================
        have hmid : |z.im| ≤ Tmax := by
          by_cases h : 0 ≤ z.im
          · rw [abs_of_nonneg h]; linarith [not_le.mp hup, hTuTmax]
          · rw [abs_of_neg (not_le.mp h)]; linarith [not_le.mp hdn, hTlTmax]
        have hM₀z : ‖Dev Φ (med Ξ α z.im)‖ ≤ M₀ := hM₀ z.im hmid z rfl hzQ hzball
        have hDT : ‖Dev Φ (Tref * Complex.I)‖ ≤ Dref := by
          rw [hDref]; linarith [norm_nonneg (Dev Φ (med Ξ α Tu)),
            norm_nonneg (Dev Φ (med Ξ α (-Tl))), norm_nonneg (Dev Φ (-(Tref * Complex.I)))]
        have hDT2 : ‖Dev Φ (-(Tref * Complex.I))‖ ≤ Dref := by
          rw [hDref]; linarith [norm_nonneg (Dev Φ (med Ξ α Tu)),
            norm_nonneg (Dev Φ (med Ξ α (-Tl))), norm_nonneg (Dev Φ (Tref * Complex.I))]
        have hCD : M₀ + Dref ≤ C := by
          linarith [hCge, hA₁, hB₁, hLUpnn, hLDownnn, hCc, mul_nonneg hCc (le_of_lt hTrefpos)]
        refine ⟨?_, ?_⟩
        · calc ‖Dev Φ (med Ξ α z.im) - Dev Φ (Tref * Complex.I)‖
              ≤ M₀ + Dref := by
                have ht := norm_sub_le (Dev Φ (med Ξ α z.im)) (Dev Φ (Tref * Complex.I))
                linarith [ht, hM₀z, hDT]
            _ ≤ C * (1 + Real.log (2 + ‖z‖)) + Λ * (|z.im - Tref| + 1) :=
                le_trans (show M₀ + Dref ≤ M₀ + Dref + Λ * |z.im - Tref| by
                  linarith [mul_nonneg hΛ0 (abs_nonneg (z.im - Tref))])
                  (by
                    have hh := hfinish 0 (M₀ + Dref) |z.im - Tref| (by linarith [hCpos.le]) hCD
                      (abs_nonneg _)
                    simpa using hh)
        · calc ‖Dev Φ (med Ξ α z.im) - Dev Φ (-(Tref * Complex.I))‖
              ≤ M₀ + Dref := by
                have ht := norm_sub_le (Dev Φ (med Ξ α z.im)) (Dev Φ (-(Tref * Complex.I)))
                linarith [ht, hM₀z, hDT2]
            _ ≤ C * (1 + Real.log (2 + ‖z‖)) + Λ * (|z.im + Tref| + 1) :=
                le_trans (show M₀ + Dref ≤ M₀ + Dref + Λ * |z.im + Tref| by
                  linarith [mul_nonneg hΛ0 (abs_nonneg (z.im + Tref))])
                  (by
                    have hh := hfinish 0 (M₀ + Dref) |z.im + Tref| (by linarith [hCpos.le]) hCD
                      (abs_nonneg _)
                    simpa using hh)
  exact ⟨Tref, hTref1, hTref2, hmain⟩

end

end Work.Pert.PinAux
