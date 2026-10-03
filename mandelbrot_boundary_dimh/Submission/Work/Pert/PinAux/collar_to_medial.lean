import Mathlib
import Submission.Work.Pert.PinAux.CollarDefs
import Submission.Work.Pert.Pin3.dev_horiz_log
import Submission.Work.Pert.PinAux.good_deriv_bound
import Submission.Work.Pert.PinAux.collar_minmarg
import Submission.Work.Pert.PinAux.bad_deriv_bound_thin
import Submission.Work.Pert.PinAux.bad_deriv_bound_fat
import Submission.Work.Pert.PinAux.integral_inv_norm_le
import Submission.Work.Pert.PinAux.integral_minmarg
import Submission.Work.Pert.PinAux.collar_arith_fixed

/-!
# `Work.Pert.PinAux.collar_to_medial`

The deviation `Dev Φ = Φ - id` of a Fatou coordinate `Φ` of a near-translation `F` on the gate
`Qm Ξ α`, compared at a point `z` (whose `R₁`-ball lies in the gate) with the *medial* point
`med Ξ α z.im` of the slice at the same height:

  `‖Dev Φ z - Dev Φ (med Ξ α z.im)‖ ≤ Λ (1 + log (2 + ‖z‖))
      + (c/(1-c)) (‖z - med Ξ α z.im‖ + 1)`.

The proof transports the deviation along the horizontal segment from `z` to the medial point,
with the majorant

  `G x = A * (1 / minmarg Ξ α (x + i z.im)) + c/(1-c) + 4 K * (1 / ‖x + i z.im‖)`,
  `A = C₂√2 + D √2 Rde`,

where `D` is the uniform bound on `‖Φ' - 1‖` supplied by the two "bad region" lemmas
(`bad_deriv_bound_fat` on the part where the slice is wide, `bad_deriv_bound_thin` by compactness
where it is narrow).  The three terms integrate to `A log(minmarg(med)/minmarg z)`
(`integral_minmarg`), the target's linear term `(c/(1-c)) (hi - lo)`, and
`4K (2 + 2 log (max (max |lo| |hi|) (Ξ/2) / (Ξ/2)))` (`integral_inv_norm_le`); the final
arithmetic is `collar_arith3`.
-/

namespace Work.Pert.PinAux

open MandelDim Complex Metric MeasureTheory
open scoped Topology

noncomputable section

/-- The width of a slice is the sum of the two margins of any of its points. -/
lemma width_eq_marg_add (Ξ : ℝ) (α : ℂ) (z : ℂ) :
    width Ξ α z.im = margA Ξ α z + margB Ξ α z := by
  rw [Work.Pert.marg_add, width_eq Ξ α z.im]

theorem collar_to_medial {F Φ : ℂ → ℂ} {α : ℂ} {Ξ c Y₀ R₁ : ℝ}
    (hΞ : 0 < Ξ) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 256) (hY₀ : 0 < Y₀) (hR₁ : 0 < R₁)
    (hDE : MandelDim.FatouDerivEstimate)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hsharp : ∃ K : ℝ, 0 < K ∧ ∀ w ∈ Work.Pert.Qm Ξ α,
      ‖F w - (w + 1)‖ ≤ K / ‖w‖ + c) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α →
      Metric.ball z R₁ ⊆ Work.Pert.Qm Ξ α →
      ‖Work.Pert.PinAux.Dev Φ z - Work.Pert.PinAux.Dev Φ (Work.Pert.PinAux.med Ξ α z.im)‖
        ≤ Λ * (1 + Real.log (2 + ‖z‖))
          + (c / (1 - c)) * (‖z - Work.Pert.PinAux.med Ξ α z.im‖ + 1) := by
  have hDEcopy : MandelDim.FatouDerivEstimate := hDE
  obtain ⟨Rde, C₁, C₂, hRdepos, hC₁pos, hC₂pos, hDEall⟩ := hDE
  obtain ⟨K, hKpos, hsh⟩ := hsharp
  have hDEest : ∀ (Φ' v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z₀ R) → Set.InjOn Φ' (Metric.ball z₀ R) →
      DifferentiableOn ℂ v (Metric.ball z₀ R) → (∀ z ∈ Metric.ball z₀ R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z₀ R, z + v z ∈ Metric.ball z₀ R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z₀ - 1 / v z₀‖ ≤ C₂ / R :=
    fun Φ' v z₀ R hR h1 h2 h3 h4 h5 => (hDEall Φ' v z₀ R hR h1 h2 h3 h4 h5).2
  obtain ⟨Df, hDfpos, hDf⟩ := bad_deriv_bound_fat (Ξ := Ξ) (c := c) (ρ := R₁) (Rde := Rde)
    (C₂ := C₂) hΞ hc0 hR₁ hRdepos hC₂pos hDEest hNT hΦ
  obtain ⟨Dt, hDtpos, hDt⟩ := bad_deriv_bound_thin (Ξ := Ξ) (c := c) (ρ := R₁) (Rde := Rde)
    hΞ hc0 hR₁ hRdepos hDEcopy hNT hΦ
  set D : ℝ := max Df Dt with hDdef
  have hDpos : 0 < D := lt_max_of_lt_left hDfpos
  have hbad : ∀ w : ℂ, w ∈ Work.Pert.Qm Ξ α → R₁ ≤ minmarg Ξ α w → ‖deriv Φ w - 1‖ ≤ D := by
    intro w hw hρ
    rcases lt_or_ge (minmarg Ξ α (med Ξ α w.im)) (Real.sqrt 2 * Rde) with hlt | hge
    · exact le_trans (hDt w hw hρ hlt) (le_max_right _ _)
    · exact le_trans (hDf w hw hρ hge) (le_max_left _ _)
  set A : ℝ := C₂ * Real.sqrt 2 + D * Real.sqrt 2 * Rde with hAdef
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hApos : 0 < A := by
    rw [hAdef]
    have h3 : 0 < C₂ * Real.sqrt 2 := by positivity
    have h4 : 0 < D * Real.sqrt 2 * Rde := by positivity
    linarith
  obtain ⟨Λa, hΛapos, hΛa⟩ := collar_arith2_fixed A K c R₁ Ξ α hΞ hR₁ hApos hc0 hc (le_of_lt hKpos)
  refine ⟨Λa, hΛapos, ?_⟩
  intro z hz hball
  have hρ : R₁ ≤ minmarg Ξ α z := collar_minmarg hR₁ hz hball
  have hρpos : 0 < minmarg Ξ α z := lt_of_lt_of_le hR₁ hρ
  have hmono : ∀ x ∈ Set.Icc (min z.re (med Ξ α z.im).re) (max z.re (med Ξ α z.im).re),
      R₁ ≤ minmarg Ξ α (x + z.im * Complex.I) := fun x hx => le_trans hρ (minmarg_on_seg hx)
  have hmem : ∀ x ∈ Set.Icc (min z.re (med Ξ α z.im).re) (max z.re (med Ξ α z.im).re),
      (x : ℂ) + z.im * Complex.I ∈ Qm Ξ α := by
    intro x hx
    rw [mem_Qm_iff_minmarg_pos]
    exact lt_of_lt_of_le hρpos (minmarg_on_seg hx)
  have hdiff : ∀ x ∈ Set.Icc (min z.re (med Ξ α z.im).re) (max z.re (med Ξ α z.im).re),
      DifferentiableAt ℂ Φ ((x : ℂ) + z.im * Complex.I) := by
    intro x hx
    exact hΦ.1.differentiableAt ((Work.Pert.isOpen_Qm_ Ξ α).mem_nhds (hmem x hx))
  -- continuity facts for the majorant
  have hcontMin : Continuous (fun x : ℝ => minmarg Ξ α ((x : ℂ) + z.im * Complex.I)) :=
    (continuous_minmarg Ξ α).comp (by fun_prop)
  have hcontNrm : Continuous (fun x : ℝ => ‖(x : ℂ) + z.im * Complex.I‖) :=
    continuous_norm.comp (by fun_prop)
  have hne1 : ∀ x : ℝ, max (minmarg Ξ α ((x : ℂ) + z.im * Complex.I)) R₁ ≠ 0 := by
    intro x h0
    have h : R₁ ≤ max (minmarg Ξ α ((x : ℂ) + z.im * Complex.I)) R₁ := le_max_right _ _
    rw [h0] at h; linarith
  have hne2 : ∀ x : ℝ, max ‖(x : ℂ) + z.im * Complex.I‖ (Ξ / 2) ≠ 0 := by
    intro x h0
    have h : Ξ / 2 ≤ max ‖(x : ℂ) + z.im * Complex.I‖ (Ξ / 2) := le_max_right _ _
    rw [h0] at h; linarith
  have hcont1 : Continuous (fun x : ℝ =>
      A * (1 / max (minmarg Ξ α ((x : ℂ) + z.im * Complex.I)) R₁)) :=
    continuous_const.mul (Continuous.div continuous_const (hcontMin.max continuous_const) hne1)
  have hcont3 : Continuous (fun x : ℝ =>
      4 * K * (1 / max ‖(x : ℂ) + z.im * Complex.I‖ (Ξ / 2))) :=
    continuous_const.mul (Continuous.div continuous_const (hcontNrm.max continuous_const) hne2)
  set G : ℝ → ℝ := fun x => A * (1 / max (minmarg Ξ α ((x : ℂ) + z.im * Complex.I)) R₁)
      + c / (1 - c) + 4 * K * (1 / max ‖(x : ℂ) + z.im * Complex.I‖ (Ξ / 2)) with hGdef
  have hGcont : Continuous G := by
    rw [hGdef]
    exact (hcont1.add continuous_const).add hcont3
  -- the pointwise majorant
  have hGpoint : ∀ x ∈ Set.Icc (min z.re (med Ξ α z.im).re) (max z.re (med Ξ α z.im).re),
      ‖deriv Φ ((x : ℂ) + z.im * Complex.I) - 1‖ ≤ G x := by
    intro x hx
    have h1 : max (minmarg Ξ α ((x : ℂ) + z.im * Complex.I)) R₁
        = minmarg Ξ α ((x : ℂ) + z.im * Complex.I) := max_eq_left (hmono x hx)
    have h2 : max ‖(x : ℂ) + z.im * Complex.I‖ (Ξ / 2) = ‖(x : ℂ) + z.im * Complex.I‖ :=
      max_eq_left (norm_ge_half_of_mem hΞ (hmem x hx))
    change ‖deriv Φ ((x : ℂ) + z.im * Complex.I) - 1‖
      ≤ A * (1 / max (minmarg Ξ α ((x : ℂ) + z.im * Complex.I)) R₁) + c / (1 - c)
        + 4 * K * (1 / max ‖(x : ℂ) + z.im * Complex.I‖ (Ξ / 2))
    rw [h1, h2]
    rcases lt_or_ge (Real.sqrt 2 * Rde) (minmarg Ξ α ((x : ℂ) + z.im * Complex.I)) with hgood | hb2
    · have hb := good_deriv_bound hRdepos hC₂pos hc0 hc hKpos hDEest hNT hΦ hsh
        ((x : ℂ) + z.im * Complex.I) (hmem x hx) (le_of_lt hgood)
      have hAle : C₂ * Real.sqrt 2 ≤ A := by
        rw [hAdef]
        have h2' : 0 ≤ D * Real.sqrt 2 * Rde := by positivity
        linarith
      have hmpos : 0 < minmarg Ξ α ((x : ℂ) + z.im * Complex.I) := minmarg_pos_of_mem (hmem x hx)
      have hdiv : C₂ * Real.sqrt 2 / minmarg Ξ α ((x : ℂ) + z.im * Complex.I)
          ≤ A / minmarg Ξ α ((x : ℂ) + z.im * Complex.I) :=
        div_le_div_of_nonneg_right hAle (le_of_lt hmpos)
      rw [mul_one_div, mul_one_div]
      have hnn : 0 ≤ 4 * K / ‖(x : ℂ) + z.im * Complex.I‖ := by positivity
      linarith [hb, hdiv, hnn]
    · have hb := hbad _ (hmem x hx) (hmono x hx)
      have hmpos : 0 < minmarg Ξ α ((x : ℂ) + z.im * Complex.I) := minmarg_pos_of_mem (hmem x hx)
      have hkey : D ≤ A / minmarg Ξ α ((x : ℂ) + z.im * Complex.I) := by
        rw [le_div_iff₀ hmpos]
        have hle : D * minmarg Ξ α ((x : ℂ) + z.im * Complex.I) ≤ D * (Real.sqrt 2 * Rde) :=
          mul_le_mul_of_nonneg_left (hb2) (le_of_lt hDpos)
        have hAeq : A = C₂ * Real.sqrt 2 + D * Real.sqrt 2 * Rde := hAdef
        nlinarith [hle, hDpos, hs2, hRdepos, hC₂pos]
      rw [mul_one_div, mul_one_div]
      have hcf : 0 ≤ c / (1 - c) := div_nonneg hc0 (by linarith)
      have hnn : 0 ≤ 4 * K / ‖(x : ℂ) + z.im * Complex.I‖ := by positivity
      linarith [hb, hkey, hcf, hnn]
  -- the transport
  have htrans : ‖Dev Φ (med Ξ α z.im) - Dev Φ z‖
      ≤ ∫ x in (min z.re (med Ξ α z.im).re)..(max z.re (med Ξ α z.im).re), G x := by
    have hz1 : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := by simp
    have hm1 : (((med Ξ α z.im).re : ℂ) + (z.im : ℂ) * Complex.I) = med Ξ α z.im := by
      apply Complex.ext <;> simp [med_re, med_im]
    rcases le_total z.re ((med Ξ α z.im).re) with h | h
    · have hdiff' : ∀ x ∈ Set.Icc z.re (med Ξ α z.im).re,
          DifferentiableAt ℂ Φ ((x : ℂ) + z.im * Complex.I) := by
        intro x hx
        exact hdiff x (by rw [min_eq_left h, max_eq_right h]; exact hx)
      have hpoint' : ∀ x ∈ Set.Icc z.re (med Ξ α z.im).re,
          ‖deriv Φ ((x : ℂ) + z.im * Complex.I) - 1‖ ≤ G x := by
        intro x hx
        exact hGpoint x (by rw [min_eq_left h, max_eq_right h]; exact hx)
      have hres := Work.Pert.Pin3.dev_horiz_le_of_diffAt (Φ := Φ) (s := z.im)
        (a := z.re) (b := (med Ξ α z.im).re) (g := G) h hdiff' hpoint' hGcont.continuousOn
      rw [min_eq_left h, max_eq_right h]
      rwa [hz1, hm1] at hres
    · have hdiff' : ∀ x ∈ Set.Icc (med Ξ α z.im).re z.re,
          DifferentiableAt ℂ Φ ((x : ℂ) + z.im * Complex.I) := by
        intro x hx
        exact hdiff x (by rw [min_eq_right h, max_eq_left h]; exact hx)
      have hpoint' : ∀ x ∈ Set.Icc (med Ξ α z.im).re z.re,
          ‖deriv Φ ((x : ℂ) + z.im * Complex.I) - 1‖ ≤ G x := by
        intro x hx
        exact hGpoint x (by rw [min_eq_right h, max_eq_left h]; exact hx)
      have hres := Work.Pert.Pin3.dev_horiz_le_of_diffAt (Φ := Φ) (s := z.im)
        (a := (med Ξ α z.im).re) (b := z.re) (g := G) h hdiff' hpoint' hGcont.continuousOn
      rw [hz1, hm1] at hres
      rw [min_eq_right h, max_eq_left h]
      simp only [Dev_apply] at hres ⊢
      rw [norm_sub_rev] at hres
      exact hres
  -- integrals
  have hint1 : (∫ x in (min z.re (med Ξ α z.im).re)..(max z.re (med Ξ α z.im).re),
      1 / minmarg Ξ α (x + z.im * Complex.I))
      = Real.log (minmarg Ξ α (med Ξ α z.im) / minmarg Ξ α z) := integral_minmarg hρpos
  have hint2 : (∫ x in (min z.re (med Ξ α z.im).re)..(max z.re (med Ξ α z.im).re),
      1 / ‖(x : ℂ) + z.im * Complex.I‖)
      ≤ 2 + 2 * Real.log (max (max |min z.re (med Ξ α z.im).re|
          |max z.re (med Ξ α z.im).re|) (Ξ / 2) / (Ξ / 2)) :=
    integral_inv_norm_le (by linarith) min_le_max (fun x hx => norm_ge_half_of_mem hΞ (hmem x hx))
  have hGint : (∫ x in (min z.re (med Ξ α z.im).re)..(max z.re (med Ξ α z.im).re), G x)
      = A * (∫ x in (min z.re (med Ξ α z.im).re)..(max z.re (med Ξ α z.im).re),
            1 / minmarg Ξ α (x + z.im * Complex.I))
        + (c / (1 - c)) * ((max z.re (med Ξ α z.im).re) - min z.re (med Ξ α z.im).re)
        + 4 * K * (∫ x in (min z.re (med Ξ α z.im).re)..(max z.re (med Ξ α z.im).re),
            1 / ‖(x : ℂ) + z.im * Complex.I‖) := by
    set lo : ℝ := min z.re (med Ξ α z.im).re with hlodef
    set hi : ℝ := max z.re (med Ξ α z.im).re with bhdef
    have hIf : IntervalIntegrable (fun x : ℝ =>
        A * (1 / max (minmarg Ξ α ((x : ℂ) + z.im * Complex.I)) R₁)) volume lo hi :=
      hcont1.intervalIntegrable lo hi
    have hIg : IntervalIntegrable (fun x : ℝ => c / (1 - c)) volume lo hi := intervalIntegrable_const
    have hIh : IntervalIntegrable (fun x : ℝ =>
        4 * K * (1 / max ‖(x : ℂ) + z.im * Complex.I‖ (Ξ / 2))) volume lo hi :=
      hcont3.intervalIntegrable lo hi
    rw [intervalIntegral.integral_add (hIf.add hIg) hIh,
      intervalIntegral.integral_add hIf hIg,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    rw [hlodef, bhdef]
    have h1 : (∫ x in min z.re (med Ξ α z.im).re..max z.re (med Ξ α z.im).re,
        1 / minmarg Ξ α (x + z.im * Complex.I))
        = (∫ x in min z.re (med Ξ α z.im).re..max z.re (med Ξ α z.im).re,
        1 / minmarg Ξ α (x + z.im * Complex.I)) := rfl
    have h2 : (∫ x in min z.re (med Ξ α z.im).re..max z.re (med Ξ α z.im).re,
        1 / max (minmarg Ξ α ((x : ℂ) + z.im * Complex.I)) R₁)
        = (∫ x in min z.re (med Ξ α z.im).re..max z.re (med Ξ α z.im).re,
        1 / minmarg Ξ α (x + z.im * Complex.I)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (min_le_max)] at hx
      change 1 / max (minmarg Ξ α ((x : ℂ) + z.im * Complex.I)) R₁
        = 1 / minmarg Ξ α ((x : ℂ) + z.im * Complex.I)
      rw [max_eq_left (hmono x hx)]
    have h3 : (∫ x in min z.re (med Ξ α z.im).re..max z.re (med Ξ α z.im).re,
        1 / max ‖(x : ℂ) + z.im * Complex.I‖ (Ξ / 2))
        = (∫ x in min z.re (med Ξ α z.im).re..max z.re (med Ξ α z.im).re,
        1 / ‖(x : ℂ) + z.im * Complex.I‖) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (min_le_max)] at hx
      change 1 / max ‖(x : ℂ) + z.im * Complex.I‖ (Ξ / 2)
        = 1 / ‖(x : ℂ) + z.im * Complex.I‖
      rw [max_eq_left (norm_ge_half_of_mem hΞ (hmem x hx))]
    rw [h2, h3]
    ring
  -- endpoint bounds for the arithmetic
  have hM : minmarg Ξ α (med Ξ α z.im)
      ≤ |z.im| + (|(1 / α).re| + 2 * Ξ + |(1 / α).im|) / 2 := by
    rw [minmarg_med]
    have hw := width_le Ξ α z.im (le_of_lt hΞ)
    linarith
  have hlo : max |min z.re (med Ξ α z.im).re| |max z.re (med Ξ α z.im).re|
      ≤ 2 * ‖z‖ + (|(1 / α).re| + |(1 / α).im|) + Ξ := by
    have h4 : |(med Ξ α z.im).re| ≤ |z.im| + (|(1 / α).re| + |(1 / α).im|) / 2 + Ξ := by
      rw [med_re]
      have h5 := xMid_abs_le Ξ α z.im
      have h6 : |Ξ| = Ξ := abs_of_nonneg (le_of_lt hΞ)
      linarith [h5, h6]
    have h5 : |z.re| ≤ |z.im| + (|(1 / α).re| + |(1 / α).im|) + Ξ := by
      have hA := (Work.Pert.mem_Qm_iff_marg Ξ α z).mp hz |>.1
      have hB := (Work.Pert.mem_Qm_iff_marg Ξ α z).mp hz |>.2
      have hA' : z.re > Ξ - (1 / α).re - |z.im + (1 / α).im| := by
        simp only [Work.Pert.margA] at hA; linarith
      have hB' : z.re < |z.im| - Ξ := by
        simp only [Work.Pert.margB] at hB; linarith
      have h6 : |z.im + (1 / α).im| ≤ |z.im| + |(1 / α).im| := abs_add_le _ _
      have h7 : -z.re ≤ |z.im| + |(1 / α).im| + |(1 / α).re| - Ξ := by
        have := le_abs_self ((1 / α).re)
        linarith [hA', h6]
      have h8 : z.re ≤ |z.im| + |(1 / α).im| + |(1 / α).re| + Ξ := by
        have := abs_nonneg ((1 / α).re)
        have := abs_nonneg ((1 / α).im)
        linarith [hB']
      rw [abs_le]
      exact ⟨by linarith [h7], by linarith [h8]⟩
    have h6 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    refine max_le ?_ ?_
    · rcases le_total z.re ((med Ξ α z.im).re) with h | h
      · rw [min_eq_left h]; linarith [h5, h6, norm_nonneg z]
      · rw [min_eq_right h]
        exact le_trans h4 (by
          linarith [h6, norm_nonneg z, abs_nonneg ((1 / α).re), abs_nonneg ((1 / α).im)])
    · rcases le_total z.re ((med Ξ α z.im).re) with h | h
      · rw [max_eq_right h]
        exact le_trans h4 (by
          linarith [h6, norm_nonneg z, abs_nonneg ((1 / α).re), abs_nonneg ((1 / α).im)])
      · rw [max_eq_left h]; linarith [h5, h6, norm_nonneg z]
  have hhi : 0 ≤ (max z.re (med Ξ α z.im).re) - min z.re (med Ξ α z.im).re := by
    have := min_le_max (a := z.re) (b := (med Ξ α z.im).re); linarith
  have hstep1 : ‖Dev Φ (med Ξ α z.im) - Dev Φ z‖
      ≤ A * Real.log (minmarg Ξ α (med Ξ α z.im) / minmarg Ξ α z)
        + (c / (1 - c)) * ((max z.re (med Ξ α z.im).re) - min z.re (med Ξ α z.im).re)
        + 4 * K * (2 + 2 * Real.log (max (max |min z.re (med Ξ α z.im).re|
            |max z.re (med Ξ α z.im).re|) (Ξ / 2) / (Ξ / 2))) := by
    rw [hGint] at htrans
    have h4 : A * (∫ x in (min z.re (med Ξ α z.im).re)..(max z.re (med Ξ α z.im).re),
        1 / minmarg Ξ α (x + z.im * Complex.I))
        = A * Real.log (minmarg Ξ α (med Ξ α z.im) / minmarg Ξ α z) := by rw [hint1]
    have h5 : 4 * K * (∫ x in (min z.re (med Ξ α z.im).re)..(max z.re (med Ξ α z.im).re),
        1 / ‖(x : ℂ) + z.im * Complex.I‖)
        ≤ 4 * K * (2 + 2 * Real.log (max (max |min z.re (med Ξ α z.im).re|
            |max z.re (med Ξ α z.im).re|) (Ξ / 2) / (Ξ / 2))) :=
      mul_le_mul_of_nonneg_left hint2 (by positivity)
    linarith [htrans, h4, h5]
  have hMpos : 0 < minmarg Ξ α (med Ξ α z.im) := by
    rw [minmarg_med, width_eq_marg_add]
    have h1 := minmarg_pos_of_mem hz
    have h2 : minmarg Ξ α z ≤ margA Ξ α z := minmarg_le_margA Ξ α z
    have h3 : minmarg Ξ α z ≤ margB Ξ α z := minmarg_le_margB Ξ α z
    linarith
  have hfinal := hΛa z (minmarg Ξ α (med Ξ α z.im)) (minmarg Ξ α z)
    (min z.re (med Ξ α z.im).re) (max z.re (med Ξ α z.im).re) hρ hρpos hMpos hM hlo hhi
  have hnorm : (max z.re (med Ξ α z.im).re) - min z.re (med Ξ α z.im).re
      = ‖z - med Ξ α z.im‖ := by
    have h1 : max z.re (med Ξ α z.im).re - min z.re (med Ξ α z.im).re
        = |z.re - (med Ξ α z.im).re| := by
      rw [max_sub_min_eq_abs, abs_sub_comm]
    have hd : z - med Ξ α z.im = (((z.re - (med Ξ α z.im).re) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [med_im]
    rw [h1, hd, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at hfinal hstep1
  rw [norm_sub_rev (Dev Φ z) (Dev Φ (med Ξ α z.im))]
  exact le_trans hstep1 hfinal

end

end Work.Pert.PinAux
