import Mathlib
import Submission.Work.Pert.PinLogDev.anchor_to_all_t
import Submission.Work.Pert.PinLogDev.axis_good_transport_eps
import Submission.Work.Pert.PinLogDev.log_bound_arith_eps

/-!
# `Work.Pert.PinLogDev.anchor_to_all_t_const`

`anchor_to_all_t` with a constant slack `ε` on the defect decay of the *lower* axis:
the hypotheses there are `‖F (-i s) - (-i s + 1)‖ ≤ Kd / s + ε` with `0 ≤ ε ≤ 1/128`
(which is the form delivered by `Work.Pert.PinLogDev.axis_decay_budget`; the lower axis
does **not** have a decaying defect: `F (-i s) - (-i s + 1) → c₀ - 1 ≠ 0`).

The transport of the deviation `Dev Φ = Φ - id` along the axis is the same as in
`anchor_to_all_t`, except that the constant `ε` of the defect is integrated over the
transported interval, contributing `(32/31) ε (b - a) ≤ (32/31) ε t ≤ t/64`
(here `ε ≤ 1/128`, so `(32/31) ε ≤ 1/124 ≤ 1/64`); the `t/64` slack of the final bound
absorbs it.  The two pieces used are the `ε`-variants of `axis_good_transport` and of
`log_bound_arith`, proved in the sibling files `axis_good_transport_eps` and
`log_bound_arith_eps` of this directory.
-/

namespace Work.Pert.PinLogDev

set_option maxHeartbeats 4000000

open MandelDim Complex Metric MeasureTheory
open scoped Topology

noncomputable section

/-- The main transport statement, for one of the two half-axes `s ↦ s • w`, `w = ±I`,
with the constant slack `ε` on the defect decay. -/
private theorem key_axis_bound_eps (Ξ Rde C₂ K₁ Kd ε : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ)
    (hRde : 0 < Rde) (hC₂ : 0 ≤ C₂) (hK₁ : 0 ≤ K₁) (hKd : 0 ≤ Kd)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 128)
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    {α : ℂ} {Y₀ : ℝ} (hY : Ξ + 4 * (Rde + C₂ + 2) + 10 ≤ Y₀)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    {F Φ : ℂ → ℂ} (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    {w : ℂ} (hw : w = Complex.I ∨ w = -Complex.I)
    (hdec : ∀ s : ℝ, Y₀ ≤ s → ‖F ((s : ℂ) * w) - ((s : ℂ) * w + 1)‖ ≤ Kd / s + ε)
    (hanc : ‖Φ ((Y₀ : ℂ) * w) - (Y₀ : ℂ) * w‖ ≤ K₁)
    {t : ℝ} (ht : Y₀ ≤ t) :
    ‖Φ ((t : ℂ) * w) - (t : ℂ) * w‖
      ≤ Aconst C₂ Kd * Real.log (t + 2) + Cconst K₁ (Kbad Rde C₂) + t / 64 := by
  -------------------------------------------------------------------------------------
  -- basic constants
  -------------------------------------------------------------------------------------
  set Cα : ℝ := (1 / α).re - Ξ with hCαdef
  set M : ℝ := -(w.im) * (1 / α).im with hMdef
  set δ₀ : ℝ := Real.sqrt 2 * Rde - Cα with hδdef
  have hΞ0 : 0 < Ξ := by have := Real.pi_pos; linarith
  have hCα4 : Ξ + 4 ≤ Cα := by
    have := QAdm_re_inv hQAdm
    rw [hCαdef]; linarith
  have hCα0 : 0 < Cα := by linarith
  have hY0 : 0 < Y₀ := by linarith
  have hRde2 : Rde ≤ 2 * Rde := by linarith
  -- `hgeo`
  have hNpos : (0 : ℝ) ≤ 32 * (Real.sqrt 2 * Rde + 1) / 31 := by positivity
  have hNlt : (Nlen Rde : ℝ) < 32 * (Real.sqrt 2 * Rde + 1) / 31 + 1 := by
    have h := Nat.ceil_lt_add_one hNpos
    simpa [Nlen] using h
  have hsqrt2 : Real.sqrt 2 < 3 / 2 := Real.sqrt_two_lt_three_halves
  have hYdew : 4 * (Rde + C₂ + 2) + 10 ≤ Y₀ - Ξ := by linarith
  have hgeo : 34 * (Nlen Rde : ℝ) + 32 + 32 * Real.sqrt 2 * Rde ≤ 32 * (Y₀ - Ξ) := by
    nlinarith [hNlt, hsqrt2, hYdew, hRde, hC₂]
  have hNle : Real.sqrt 2 * Rde + 1 ≤ 31 * (Nlen Rde : ℝ) / 32 := by
    have h := Nat.le_ceil (32 * (Real.sqrt 2 * Rde + 1) / 31 : ℝ)
    have h' : (32 * (Real.sqrt 2 * Rde + 1) / 31 : ℝ) ≤ (Nlen Rde : ℝ) := by simpa [Nlen] using h
    linarith
  -------------------------------------------------------------------------------------
  -- the walk hypothesis
  -------------------------------------------------------------------------------------
  have hmargA : ∀ s : ℝ, 0 ≤ s → Work.Pert.margA Ξ α ((s : ℂ) * w) = Cα + |s - M| := by
    intro s hs
    have h := margA_axis_w (Ξ := Ξ) (α := α) (w := w) hw s
    rw [hCαdef, hMdef]
    exact h
  have hmargB : ∀ s : ℝ, 0 ≤ s → Work.Pert.margB Ξ α ((s : ℂ) * w) = s - Ξ := by
    intro s hs
    exact margB_axis_w (Ξ := Ξ) (α := α) (w := w) hw hs
  have hmemw : ∀ s : ℝ, Y₀ ≤ s → (s : ℂ) * w ∈ Work.Pert.Qm Ξ α := by
    intro s hs
    rw [Work.Pert.mem_Qm_iff_marg]
    have hs0 : 0 ≤ s := by linarith
    rw [hmargA s hs0, hmargB s hs0]
    have : |s - M| ≥ 0 := abs_nonneg _
    constructor <;> linarith
  have hwalk : ∀ β : ℝ, Y₀ ≤ β →
      (∀ j : ℕ, j ≤ Nlen Rde → F^[j] ((β : ℂ) * w) ∈ Work.Pert.Qm Ξ α) ∧
      (∀ j : ℕ, j ≤ Nlen Rde → 31 * (j : ℝ) / 32 ≤ (F^[j] ((β : ℂ) * w)).re) ∧
      (∀ j : ℕ, j ≤ Nlen Rde → (F^[j] ((β : ℂ) * w)).re ≤ 33 * (j : ℝ) / 32) ∧
      (∀ j : ℕ, j ≤ Nlen Rde →
        |(F^[j] ((β : ℂ) * w)).im - ((β : ℂ) * w).im| ≤ (j : ℝ) / 32) ∧
      ‖Work.Pert.PinAux.Dev Φ (F^[Nlen Rde] ((β : ℂ) * w))
          - Work.Pert.PinAux.Dev Φ ((β : ℂ) * w)‖ ≤ (Nlen Rde : ℝ) / 32 := by
    intro β hβ
    refine walk_gate_drift_dev (n := Nlen Rde) (Ξ := Ξ) (α := α)
      (w₀ := (β : ℂ) * w) (β := β) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · have hCre : Ξ + 4 ≤ (1 / α).re := by
        have h1 := hCα4
        rw [hCαdef] at h1
        linarith
      exact hCre
    · linarith
    · exact re_axis_w hw β
    · rw [im_axis_w hw β, abs_of_nonneg (by linarith : (0:ℝ) ≤ β)]
    · have h32 : 34 * (Nlen Rde : ℝ) + 32 ≤ 32 * (β - Ξ) := by
        have : 34 * (Nlen Rde : ℝ) + 32 ≤ 32 * (Y₀ - Ξ) := by
          nlinarith [hgeo, Real.sqrt_nonneg 2, hRde]
        nlinarith [this, hβ, hY]
      exact h32
    · exact hmemw β hβ
    · intro u hu
      exact (hNT.1.2 u hu).1
    · exact hΦ
  -------------------------------------------------------------------------------------
  -- the split
  -------------------------------------------------------------------------------------
  set c₁ : ℝ := min t (max Y₀ (M - δ₀)) with hc₁def
  set c₂ : ℝ := max c₁ (min t (M + δ₀)) with hc₂def
  have hc1Y : Y₀ ≤ c₁ := by
    rw [hc₁def]
    calc Y₀ = min t Y₀ := (min_eq_right ht).symm
      _ ≤ min t (max Y₀ (M - δ₀)) := min_le_min_left _ (le_max_left _ _)
  have hc12 : c₁ ≤ c₂ := by rw [hc₂def]; exact le_max_left _ _
  have hc2t : c₂ ≤ t := by
    rw [hc₂def]
    refine max_le ?_ (min_le_left _ _)
    rw [hc₁def]
    exact min_le_left _ _
  -- goodness of the two outer intervals
  have hgood1 : c₁ = Y₀ ∨ ∀ s ∈ Set.Icc Y₀ c₁, δ₀ ≤ |s - M| := by
    by_cases hδ : δ₀ ≤ 0
    · refine Or.inr ?_
      intro s _
      linarith [abs_nonneg (s - M)]
    push_neg at hδ
    by_cases h : c₁ = Y₀
    · exact Or.inl h
    refine Or.inr ?_
    have hc1le : c₁ ≤ M - δ₀ := by
      have hmax : max Y₀ (M - δ₀) = M - δ₀ := by
        rcases le_total Y₀ (M - δ₀) with hle | hle
        · exact max_eq_right hle
        · exact absurd (by rw [hc₁def, max_eq_left hle, min_eq_right ht]) h
      rw [hc₁def, hmax]
      exact min_le_right _ _
    intro s hs
    have hsM : s ≤ M := by linarith [hs.2, hc1le]
    rw [abs_of_nonpos (by linarith : s - M ≤ 0)]
    linarith [hs.2, hc1le]
  have hc1t : c₁ ≤ t := by rw [hc₁def]; exact min_le_left _ _
  have hgood2 : c₂ = t ∨ ∀ s ∈ Set.Icc c₂ t, δ₀ ≤ |s - M| := by
    by_cases hδ : δ₀ ≤ 0
    · refine Or.inr ?_
      intro s _
      linarith [abs_nonneg (s - M)]
    push_neg at hδ
    by_cases h : c₂ = t
    · exact Or.inl h
    refine Or.inr ?_
    have hc2ge : M + δ₀ ≤ c₂ := by
      have hmin : min t (M + δ₀) = M + δ₀ := by
        rcases le_total t (M + δ₀) with hle | hle
        · exact absurd (by rw [hc₂def, min_eq_left hle, max_eq_right hc1t]) h
        · exact min_eq_right hle
      rw [hc₂def, hmin]
      exact le_max_right _ _
    intro s hs
    have hsM : M ≤ s := by linarith [hs.1, hc2ge]
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s - M)]
    linarith [hs.1, hc2ge]
  -------------------------------------------------------------------------------------
  -- the three pieces
  -------------------------------------------------------------------------------------
  have hYde : Real.sqrt 2 * Rde ≤ Y₀ - Ξ := by
    nlinarith [hYdew, hRde, hC₂, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  have hpiece1 : ‖Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((Y₀ : ℂ) * w)‖
      ≤ Real.sqrt 2 * C₂ * (Real.log ((t - Ξ) / (Y₀ - Ξ))
          + 2 * Real.log (1 + (t - Y₀) / (2 * Cα)))
        + (32 / 31) * Kd * Real.log (t / Y₀) + (32 / 31) * ε * (c₁ - Y₀) := by
    rcases hgood1 with h | h
    · rw [h]
      have h0 : ‖Work.Pert.PinAux.Dev Φ ((Y₀ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((Y₀ : ℂ) * w)‖
          = 0 := by simp
      rw [h0]
      have hlog1 : 0 ≤ Real.log ((t - Ξ) / (Y₀ - Ξ)) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ (by linarith : (0:ℝ) < Y₀ - Ξ)]
        linarith
      have hlog2 : 0 ≤ Real.log (1 + (t - Y₀) / (2 * Cα)) := by
        apply Real.log_nonneg
        have : 0 ≤ (t - Y₀) / (2 * Cα) := by positivity
        linarith
      have hlog3 : 0 ≤ Real.log (t / Y₀) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ hY0]; linarith
      have hbr : 0 ≤ Real.log ((t - Ξ) / (Y₀ - Ξ)) + 2 * Real.log (1 + (t - Y₀) / (2 * Cα)) := by
        linarith
      have h1 : (0:ℝ) ≤ Real.sqrt 2 * C₂ * (Real.log ((t - Ξ) / (Y₀ - Ξ))
          + 2 * Real.log (1 + (t - Y₀) / (2 * Cα))) :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hC₂) hbr
      have h2 : (0:ℝ) ≤ (32 / 31) * Kd * Real.log (t / Y₀) :=
        mul_nonneg (mul_nonneg (by norm_num) hKd) hlog3
      have h3 : (32 / 31) * ε * ((Y₀ : ℝ) - Y₀) = 0 := by ring
      linarith
    · -- nondegenerate: transport, then bound the kink integral and the logarithms
      have ht1 := axis_good_transport_eps (Ξ := Ξ) (Rde := Rde) (C₂ := C₂) (Kd := Kd)
        (Cα := Cα) (M := M) (δ₀ := δ₀) (Y₀ := Y₀) (a := Y₀) (b := c₁) (ε := ε)
        (α := α) (F := F) (Φ := Φ) (w := w)
        hRde hC₂ hKd hε0 hDE hNT hΦ hw rfl rfl rfl hCα0 hΞ0 hY0 hYde le_rfl hc1Y h
        (fun s hs => hdec s (by linarith [hs.1]))
      have hkink : (∫ s in Y₀..c₁, (1 : ℝ) / (Cα + |s - M|))
          ≤ 2 * Real.log (1 + (t - Y₀) / (2 * Cα)) := by
        have hI := integral_one_div_add_abs_le Cα M Y₀ c₁ hCα0 hc1Y
        have hfrac : (c₁ - Y₀) / (2 * Cα) ≤ (t - Y₀) / (2 * Cα) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith [hc2t]
        have hmono : Real.log (1 + (c₁ - Y₀) / (2 * Cα)) ≤ Real.log (1 + (t - Y₀) / (2 * Cα)) := by
          apply Real.log_le_log (by positivity)
          linarith [hfrac]
        linarith [hI, hmono]
      have hlogA : Real.log ((c₁ - Ξ) / (Y₀ - Ξ)) ≤ Real.log ((t - Ξ) / (Y₀ - Ξ)) := by
        apply Real.log_le_log (div_pos (by linarith [hc1Y]) (by linarith))
        apply div_le_div_of_nonneg_right _ (by linarith : (0:ℝ) ≤ Y₀ - Ξ)
        linarith [hc2t]
      have hlogB : Real.log (c₁ / Y₀) ≤ Real.log (t / Y₀) := by
        apply Real.log_le_log (div_pos (by linarith [hc1Y]) hY0)
        apply div_le_div_of_nonneg_right _ (by linarith : (0:ℝ) ≤ Y₀)
        linarith [hc2t]
      have h1 : Real.sqrt 2 * C₂ * (Real.log ((c₁ - Ξ) / (Y₀ - Ξ))
            + ∫ s in Y₀..c₁, (1 : ℝ) / (Cα + |s - M|))
          ≤ Real.sqrt 2 * C₂ * (Real.log ((t - Ξ) / (Y₀ - Ξ))
            + 2 * Real.log (1 + (t - Y₀) / (2 * Cα))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hkink, hlogA]
      have h2 : (32 / 31) * (Kd * Real.log (c₁ / Y₀) + ε * (c₁ - Y₀))
          ≤ (32 / 31) * Kd * Real.log (t / Y₀) + (32 / 31) * ε * (c₁ - Y₀) := by
        have h4 : (32 / 31) * (Kd * Real.log (c₁ / Y₀)) ≤ (32 / 31) * (Kd * Real.log (t / Y₀)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogB hKd) (by norm_num)
        linarith [h4]
      linarith [ht1, h1, h2]
  have hpiece2 : ‖Work.Pert.PinAux.Dev Φ ((t : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w)‖
      ≤ Real.sqrt 2 * C₂ * (Real.log ((t - Ξ) / (Y₀ - Ξ))
          + 2 * Real.log (1 + (t - Y₀) / (2 * Cα)))
        + (32 / 31) * Kd * Real.log (t / Y₀) + (32 / 31) * ε * (t - c₂) := by
    rcases hgood2 with h | h
    · rw [h]
      have h0 : ‖Work.Pert.PinAux.Dev Φ ((t : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((t : ℂ) * w)‖
          = 0 := by simp
      rw [h0]
      have hlog1 : 0 ≤ Real.log ((t - Ξ) / (Y₀ - Ξ)) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ (by linarith : (0:ℝ) < Y₀ - Ξ)]
        linarith
      have hlog2 : 0 ≤ Real.log (1 + (t - Y₀) / (2 * Cα)) := by
        apply Real.log_nonneg
        have : 0 ≤ (t - Y₀) / (2 * Cα) := by positivity
        linarith
      have hlog3 : 0 ≤ Real.log (t / Y₀) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ hY0]; linarith
      have hbr : 0 ≤ Real.log ((t - Ξ) / (Y₀ - Ξ)) + 2 * Real.log (1 + (t - Y₀) / (2 * Cα)) := by
        linarith
      have h1 : (0:ℝ) ≤ Real.sqrt 2 * C₂ * (Real.log ((t - Ξ) / (Y₀ - Ξ))
          + 2 * Real.log (1 + (t - Y₀) / (2 * Cα))) :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hC₂) hbr
      have h2 : (0:ℝ) ≤ (32 / 31) * Kd * Real.log (t / Y₀) :=
        mul_nonneg (mul_nonneg (by norm_num) hKd) hlog3
      have h3 : (32 / 31) * ε * (t - (t : ℝ)) = 0 := by ring
      linarith
    · have ht2 := axis_good_transport_eps (Ξ := Ξ) (Rde := Rde) (C₂ := C₂) (Kd := Kd)
        (Cα := Cα) (M := M) (δ₀ := δ₀) (Y₀ := Y₀) (a := c₂) (b := t) (ε := ε)
        (α := α) (F := F) (Φ := Φ) (w := w)
        hRde hC₂ hKd hε0 hDE hNT hΦ hw rfl rfl rfl hCα0 hΞ0 hY0 hYde
        (le_trans hc1Y hc12) hc2t h (fun s hs => hdec s (by linarith [hs.1]))
      have hkink : (∫ s in c₂..t, (1 : ℝ) / (Cα + |s - M|))
          ≤ 2 * Real.log (1 + (t - Y₀) / (2 * Cα)) := by
        have hI := integral_one_div_add_abs_le Cα M c₂ t hCα0 hc2t
        have hfrac : (t - c₂) / (2 * Cα) ≤ (t - Y₀) / (2 * Cα) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith [hc1Y]
        have hmono : Real.log (1 + (t - c₂) / (2 * Cα)) ≤ Real.log (1 + (t - Y₀) / (2 * Cα)) := by
          apply Real.log_le_log (by positivity)
          linarith [hfrac]
        linarith [hI, hmono]
      have hlogA : Real.log ((t - Ξ) / (c₂ - Ξ)) ≤ Real.log ((t - Ξ) / (Y₀ - Ξ)) := by
        apply Real.log_le_log (div_pos (by linarith [hc2t]) (by linarith [hc1Y]))
        apply div_le_div_of_nonneg_left (by linarith : (0:ℝ) ≤ t - Ξ)
          (by linarith : (0:ℝ) < Y₀ - Ξ)
        linarith [hc1Y]
      have hlogB : Real.log (t / c₂) ≤ Real.log (t / Y₀) := by
        apply Real.log_le_log (div_pos (by linarith [hc2t]) (by linarith [hc1Y]))
        apply div_le_div_of_nonneg_left (by linarith : (0:ℝ) ≤ t)
          (by linarith : (0:ℝ) < Y₀)
        linarith [hc1Y]
      have h1 : Real.sqrt 2 * C₂ * (Real.log ((t - Ξ) / (c₂ - Ξ))
            + ∫ s in c₂..t, (1 : ℝ) / (Cα + |s - M|))
          ≤ Real.sqrt 2 * C₂ * (Real.log ((t - Ξ) / (Y₀ - Ξ))
            + 2 * Real.log (1 + (t - Y₀) / (2 * Cα))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hkink, hlogA]
      have h2 : (32 / 31) * (Kd * Real.log (t / c₂) + ε * (t - c₂))
          ≤ (32 / 31) * Kd * Real.log (t / Y₀) + (32 / 31) * ε * (t - c₂) := by
        have h4 : (32 / 31) * (Kd * Real.log (t / c₂)) ≤ (32 / 31) * (Kd * Real.log (t / Y₀)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogB hKd) (by norm_num)
        linarith [h4]
      linarith [ht2, h1, h2]
  have hpiece3 : ‖Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w)‖
      ≤ Kbad Rde C₂ := by
    rcases eq_or_lt_of_le hc12 with h | h
    · rw [h]
      have h0 : ‖Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w)‖
          = 0 := by simp
      rw [h0]
      have h1 : (0:ℝ) ≤ (Nlen Rde : ℝ) / 16 := by positivity
      have h2 : (0:ℝ) ≤ (C₂ / Rde + 1/31) * (2 * Real.sqrt 2 * Rde + (Nlen Rde : ℝ) / 8) := by
        apply mul_nonneg <;> positivity
      rw [Kbad]
      linarith
    · have hc2eq : c₂ = min t (M + δ₀) := by
        rcases max_choice c₁ (min t (M + δ₀)) with he | he
        · exact absurd he (by linarith)
        · exact he
      have hw₂ : c₂ ≤ M + δ₀ := by rw [hc2eq]; exact min_le_right _ _
      have hw₁ : M - δ₀ ≤ c₁ := by
        by_contra hcon
        rw [not_le] at hcon
        rcases min_choice t (max Y₀ (M - δ₀)) with hc | hc
        · have hc2c1 : c₂ ≤ c₁ := by
            rw [hc₁def, hc]
            exact hc2t
          linarith [h, hc2c1]
        · rw [hc₁def, hc] at hcon
          linarith [le_max_right Y₀ (M - δ₀)]
      exact bad_window_dev_le_v2 (Ξ := Ξ) (Rde := Rde) (C₂ := C₂) (Cα := Cα) (M := M)
        (δ₀ := δ₀) (Y₀ := Y₀) (t := t) (α := α) (F := F) (Φ := Φ) (w := w)
        (c₁ := c₁) (c₂ := c₂) hRde hC₂ hDE hNT hΦ hw rfl rfl rfl hCα4 hCα0 hΞ0 hwalk hgeo
        hc1Y hc12 hc2t hw₁ hw₂
  have htri : ‖Work.Pert.PinAux.Dev Φ ((t : ℂ) * w)‖
      ≤ ‖Work.Pert.PinAux.Dev Φ ((Y₀ : ℂ) * w)‖
        + ‖Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((Y₀ : ℂ) * w)‖
        + ‖Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w)‖
        + ‖Work.Pert.PinAux.Dev Φ ((t : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w)‖ := by
    have h1 : ‖Work.Pert.PinAux.Dev Φ ((t : ℂ) * w)‖
        ≤ ‖Work.Pert.PinAux.Dev Φ ((t : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w)‖
          + ‖Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w)‖ := by
      have h := norm_add_le
        (Work.Pert.PinAux.Dev Φ ((t : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w))
        (Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w))
      have he : (Work.Pert.PinAux.Dev Φ ((t : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w))
          + Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w)
          = Work.Pert.PinAux.Dev Φ ((t : ℂ) * w) := by ring
      rwa [he] at h
    have h2 : ‖Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w)‖
        ≤ ‖Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w)‖
          + ‖Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w)‖ := by
      have h := norm_add_le
        (Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w))
        (Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w))
      have he : (Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w))
          + Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w)
          = Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) := by ring
      rwa [he] at h
    have h3 : ‖Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w)‖
        ≤ ‖Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((Y₀ : ℂ) * w)‖
          + ‖Work.Pert.PinAux.Dev Φ ((Y₀ : ℂ) * w)‖ := by
      have h := norm_add_le
        (Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((Y₀ : ℂ) * w))
        (Work.Pert.PinAux.Dev Φ ((Y₀ : ℂ) * w))
      have he : (Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((Y₀ : ℂ) * w))
          + Work.Pert.PinAux.Dev Φ ((Y₀ : ℂ) * w)
          = Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w) := by ring
      rwa [he] at h
    linarith [h1, h2, h3]
  have hancY : ‖Work.Pert.PinAux.Dev Φ ((Y₀ : ℂ) * w)‖ ≤ K₁ := by
    simpa [Work.Pert.PinAux.Dev] using hanc
  have hKb0 : 0 ≤ Kbad Rde C₂ := by
    rw [Kbad]
    have h1 : (0:ℝ) ≤ (Nlen Rde : ℝ) / 16 := by positivity
    have h2 : 0 ≤ (C₂ / Rde + 1/31) * (2 * Real.sqrt 2 * Rde + (Nlen Rde : ℝ) / 8) := by
      apply mul_nonneg <;> positivity
    linarith
  have htarget : ‖Work.Pert.PinAux.Dev Φ ((t : ℂ) * w)‖ ≤ K₁ + Kbad Rde C₂
      + 2 * (Real.sqrt 2 * C₂ * (Real.log ((t - Ξ) / (Y₀ - Ξ))
            + 2 * Real.log (1 + (t - Y₀) / (2 * Cα)))
          + (32 / 31) * Kd * Real.log (t / Y₀))
      + (32 / 31) * ε * (c₁ - Y₀) + (32 / 31) * ε * (t - c₂) := by
    linarith [htri, hancY, hpiece1, hpiece2, hpiece3]
  -- the two `ε` contributions together are at most `(32/31) ε t`
  have hεc : (32 / 31) * ε * (c₁ - Y₀) + (32 / 31) * ε * (t - c₂) ≤ (32 / 31) * ε * t := by
    have hsum : c₁ - Y₀ + (t - c₂) ≤ t := by linarith [hc12, hY0]
    nlinarith [hsum, hε0]
  have hstep : K₁ + Kbad Rde C₂
      + 2 * (Real.sqrt 2 * C₂ * (Real.log ((t - Ξ) / (Y₀ - Ξ))
            + 2 * Real.log (1 + (t - Y₀) / (2 * Cα)))
          + (32 / 31) * Kd * Real.log (t / Y₀))
      + (32 / 31) * ε * (c₁ - Y₀) + (32 / 31) * ε * (t - c₂)
      ≤ K₁ + Kbad Rde C₂
      + 2 * (Real.sqrt 2 * C₂ * (Real.log ((t - Ξ) / (Y₀ - Ξ))
            + 2 * Real.log (1 + (t - Y₀) / (2 * Cα)))
          + (32 / 31) * Kd * Real.log (t / Y₀)) + (32 / 31) * ε * t := by
    linarith [hεc]
  have harith : K₁ + Kbad Rde C₂
      + 2 * (Real.sqrt 2 * C₂ * (Real.log ((t - Ξ) / (Y₀ - Ξ))
            + 2 * Real.log (1 + (t - Y₀) / (2 * Cα)))
          + (32 / 31) * Kd * Real.log (t / Y₀)) + (32 / 31) * ε * t
      ≤ Aconst C₂ Kd * Real.log (t + 2) + Cconst K₁ (Kbad Rde C₂) + t / 64 :=
    log_bound_arith_eps (Ξ := Ξ) (Rde := Rde) (C₂ := C₂) (K₁ := K₁) (Kd := Kd)
      (Kb := Kbad Rde C₂) (Cα := Cα) (Y₀ := Y₀) (t := t) (ε := ε)
      hΞ hRde hC₂ hK₁ hKd hKb0 hCα4 hε0 hε hY ht
  have hconv : ‖Φ ((t : ℂ) * w) - (t : ℂ) * w‖ = ‖Work.Pert.PinAux.Dev Φ ((t : ℂ) * w)‖ := by
    rw [Work.Pert.PinAux.Dev]
  rw [hconv]
  exact le_trans (le_trans htarget hstep) harith

theorem anchor_to_all_t_const (Ξ Rde C₂ K₁ Kd ε : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ)
    (hRde : 0 < Rde) (hC₂ : 0 ≤ C₂) (hK₁ : 0 ≤ K₁) (hKd : 0 ≤ Kd)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 128)
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧
      ∀ {α : ℂ} {Y₀ : ℝ}, Ξ + 4 * (Rde + C₂ + 2) + 10 ≤ Y₀ →
      MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
      ∀ {F Φ : ℂ → ℂ}, MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α) →
      MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α) →
      (∀ s : ℝ, Y₀ ≤ s → ‖F ((s : ℂ) * Complex.I) - ((s : ℂ) * Complex.I + 1)‖ ≤ Kd / s) →
      (∀ s : ℝ, Y₀ ≤ s → ‖F (-((s : ℂ) * Complex.I)) - (-((s : ℂ) * Complex.I) + 1)‖ ≤ Kd / s + ε) →
      ‖Φ ((Y₀ : ℂ) * Complex.I) - (Y₀ : ℂ) * Complex.I‖ ≤ K₁ →
      ‖Φ (-((Y₀ : ℂ) * Complex.I)) + (Y₀ : ℂ) * Complex.I‖ ≤ K₁ →
      ∀ t : ℝ, Y₀ ≤ t →
        ‖Φ ((t : ℂ) * Complex.I) - (t : ℂ) * Complex.I‖ ≤ A * Real.log (t + 2) + C + t / 64 ∧
        ‖Φ (-((t : ℂ) * Complex.I)) + (t : ℂ) * Complex.I‖ ≤ A * Real.log (t + 2) + C + t / 64 := by
  refine ⟨Aconst C₂ Kd, Cconst K₁ (Kbad Rde C₂), ?_, ?_, ?_⟩
  · rw [Aconst]
    nlinarith [hC₂, hKd, Real.sqrt_nonneg 2]
  · rw [Cconst]
    have h1 : (0:ℝ) ≤ (Nlen Rde : ℝ) / 16 := by positivity
    have h2 : 0 ≤ (C₂ / Rde + 1/31) * (2 * Real.sqrt 2 * Rde + (Nlen Rde : ℝ) / 8) := by
      apply mul_nonneg <;> positivity
    have hKb0 : 0 ≤ Kbad Rde C₂ := by rw [Kbad]; linarith
    linarith
  · intro α Y₀ hY hQAdm F Φ hNT hΦ hdec1 hdec2 hanc1 hanc2 t ht
    constructor
    · exact key_axis_bound_eps Ξ Rde C₂ K₁ Kd 0 hΞ hRde hC₂ hK₁ hKd (le_refl 0) (by norm_num)
        hDE hY hQAdm hNT hΦ (Or.inl rfl)
        (fun s hs => by simpa using hdec1 s hs) hanc1 ht
    · have hanc2' : ‖Φ ((Y₀ : ℂ) * (-Complex.I)) - (Y₀ : ℂ) * (-Complex.I)‖ ≤ K₁ := by
        have he : (Y₀ : ℂ) * (-Complex.I) = -((Y₀ : ℂ) * Complex.I) := by ring
        rw [he]
        simpa using hanc2
      have hdec2' : ∀ s : ℝ, Y₀ ≤ s →
          ‖F ((s : ℂ) * -Complex.I) - ((s : ℂ) * -Complex.I + 1)‖ ≤ Kd / s + ε := by
        intro s hs
        have he : (s : ℂ) * (-Complex.I) = -((s : ℂ) * Complex.I) := by ring
        rw [he]
        exact hdec2 s hs
      have hkey := key_axis_bound_eps Ξ Rde C₂ K₁ Kd ε hΞ hRde hC₂ hK₁ hKd hε0 hε
        hDE hY hQAdm hNT hΦ (Or.inr rfl) hdec2' hanc2' ht
      have he : (t : ℂ) * (-Complex.I) = -((t : ℂ) * Complex.I) := by ring
      rw [he] at hkey
      simpa only [sub_neg_eq_add] using hkey

end

end Work.Pert.PinLogDev
