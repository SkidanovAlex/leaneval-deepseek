import Mathlib
import Submission.Work.Pert.PinLogDev.Helpers
import Submission.Work.Pert.PinLogDev.walk_gate_drift_dev
import Submission.Work.Pert.PinLogDev.axis_seg_dist
import Submission.Work.Pert.PinLogDev.seg_margin_ge
import Submission.Work.Pert.Pin3.dev_seg_const

namespace Work.Pert.PinLogDev

open MandelDim Complex Metric Set
open scoped Topology

noncomputable section

/-! ## The transport estimate along the segment joining the two walked endpoints -/

/-- Pointwise derivative bound `‖Φ' - 1‖ ≤ C₂/Rde + 1/31` at every point of the segment joining
`z₁` and `z₂`, and the resulting displacement bound for `Dev Φ = Φ - id`. -/
private theorem dev_seg_bound
    {Ξ Rde C₂ Cα Y₀ c₁ c₂ : ℝ} {α w z₁ z₂ : ℂ} {F Φ : ℂ → ℂ}
    (hRde : 0 < Rde) (hC₂ : 0 ≤ C₂) (hΞ0 : 0 < Ξ) (hCα0 : 0 < Cα)
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hCα : Cα = (1 / α).re - Ξ)
    (hwim : |w.im| = 1)
    (hgeo : 34 * (Nlen Rde : ℝ) + 32 + 32 * Real.sqrt 2 * Rde ≤ 32 * (Y₀ - Ξ))
    (hY1 : Y₀ ≤ c₁) (hY2 : Y₀ ≤ c₂)
    (hre1 : 31 * (Nlen Rde : ℝ) / 32 ≤ z₁.re)
    (hre1' : z₁.re ≤ 33 * (Nlen Rde : ℝ) / 32)
    (hre2 : 31 * (Nlen Rde : ℝ) / 32 ≤ z₂.re)
    (hre2' : z₂.re ≤ 33 * (Nlen Rde : ℝ) / 32)
    (him1 : |z₁.im - c₁ * w.im| ≤ (Nlen Rde : ℝ) / 32)
    (him2 : |z₂.im - c₂ * w.im| ≤ (Nlen Rde : ℝ) / 32) :
    ‖Work.Pert.PinAux.Dev Φ z₂ - Work.Pert.PinAux.Dev Φ z₁‖
      ≤ (C₂ / Rde + 1 / 31) * ‖z₂ - z₁‖ := by
  have hball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Metric.ball (z₁ + s • (z₂ - z₁)) Rde ⊆ Work.Pert.Qm Ξ α := by
    intro s hs
    exact Work.Pert.ball_subset_Qm_of_marg_le (le_of_lt hRde)
      (seg_margin_ge hRde hΞ0 hCα0 hCα hwim hgeo hY1 hY2 hre1 hre1' hre2 hre2' him1 him2 hs)
  have hdiff : ∀ s ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℂ Φ (z₁ + s • (z₂ - z₁)) := by
    intro s hs
    have hmem : z₁ + s • (z₂ - z₁) ∈ Work.Pert.Qm Ξ α := hball s hs (Metric.mem_ball_self hRde)
    exact (hΦ.1 _ hmem).differentiableAt ((Work.Pert.isOpen_Qm_ Ξ α).mem_nhds hmem)
  have hbd : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖deriv Φ (z₁ + s • (z₂ - z₁)) - 1‖ ≤ C₂ / Rde + 1 / 31 := by
    intro s hs
    have hb : Metric.ball (z₁ + s • (z₂ - z₁)) Rde ⊆ Work.Pert.Qm Ξ α := hball s hs
    have hmem : z₁ + s • (z₂ - z₁) ∈ Work.Pert.Qm Ξ α := hb (Metric.mem_ball_self hRde)
    have hDEapp : ‖deriv Φ (z₁ + s • (z₂ - z₁))
        - 1 / (F (z₁ + s • (z₂ - z₁)) - (z₁ + s • (z₂ - z₁)))‖ ≤ C₂ / Rde :=
      hDE Φ (fun u => F u - u) (z₁ + s • (z₂ - z₁)) Rde le_rfl
        (hΦ.1.mono hb) (hΦ.2.1.mono hb)
        ((hNT.1.1.mono hb).sub differentiableOn_id)
        (fun u hu => by
          have h1 : ‖F u - (u + 1)‖ ≤ (1 / 32 : ℝ) := (hNT.1.2 u (hb hu)).1
          have he : F u - u - 1 = F u - (u + 1) := by ring
          rw [he]; linarith)
        (fun u hu hFu => by
          have he : u + (F u - u) = F u := by ring
          rw [he] at hFu ⊢
          exact hΦ.2.2 u (hb hu) (hb hFu))
    have hone : ‖1 / (F (z₁ + s • (z₂ - z₁)) - (z₁ + s • (z₂ - z₁))) - 1‖ ≤ 1 / 31 := by
      have h1 : ‖F (z₁ + s • (z₂ - z₁)) - ((z₁ + s • (z₂ - z₁)) + 1)‖ ≤ (1 / 32 : ℝ) :=
        (hNT.1.2 _ hmem).1
      set e : ℂ := F (z₁ + s • (z₂ - z₁)) - ((z₁ + s • (z₂ - z₁)) + 1) with he_def
      have hele : ‖e‖ ≤ (1 / 32 : ℝ) := h1
      have heq : F (z₁ + s • (z₂ - z₁)) - (z₁ + s • (z₂ - z₁)) = 1 + e := by
        rw [he_def]; ring
      rw [heq]
      have hden : (31 : ℝ) / 32 ≤ ‖(1 : ℂ) + e‖ := by
        have h := norm_add_le ((1 : ℂ) + e) (-e)
        have he : ((1 : ℂ) + e) + (-e) = (1 : ℂ) := by ring
        rw [he, norm_one, norm_neg] at h
        linarith
      have hdenpos : 0 < ‖(1 : ℂ) + e‖ := lt_of_lt_of_le (by norm_num) hden
      have hne : (1 : ℂ) + e ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hden; norm_num at hden
      have halg : 1 / ((1 : ℂ) + e) - 1 = -e / (1 + e) := by
        rw [eq_div_iff hne]
        rw [sub_mul, one_div, inv_mul_cancel₀ hne, one_mul]
        ring
      rw [halg, norm_div, norm_neg]
      rw [div_le_iff₀ hdenpos]
      linarith
    have hsplit : ‖deriv Φ (z₁ + s • (z₂ - z₁)) - 1‖
        ≤ ‖deriv Φ (z₁ + s • (z₂ - z₁))
              - 1 / (F (z₁ + s • (z₂ - z₁)) - (z₁ + s • (z₂ - z₁)))‖
          + ‖1 / (F (z₁ + s • (z₂ - z₁)) - (z₁ + s • (z₂ - z₁))) - 1‖ := by
      have h := norm_add_le
        (deriv Φ (z₁ + s • (z₂ - z₁))
          - 1 / (F (z₁ + s • (z₂ - z₁)) - (z₁ + s • (z₂ - z₁))))
        (1 / (F (z₁ + s • (z₂ - z₁)) - (z₁ + s • (z₂ - z₁))) - 1)
      have he : (deriv Φ (z₁ + s • (z₂ - z₁))
              - 1 / (F (z₁ + s • (z₂ - z₁)) - (z₁ + s • (z₂ - z₁))))
            + (1 / (F (z₁ + s • (z₂ - z₁)) - (z₁ + s • (z₂ - z₁))) - 1)
          = deriv Φ (z₁ + s • (z₂ - z₁)) - 1 := by ring
      rwa [he] at h
    linarith
  have hΛ0 : (0 : ℝ) ≤ C₂ / Rde + 1 / 31 := by
    have : 0 ≤ C₂ / Rde := div_nonneg hC₂ (le_of_lt hRde)
    linarith
  have hmain := Work.Pert.Pin3.dev_seg_const (Φ := Φ) (p := z₁) (q := z₂)
    (Λ := C₂ / Rde + 1 / 31) hΛ0 hdiff hbd
  simpa [Work.Pert.PinAux.Dev] using hmain

/-! ## The deviation across the bad window -/

theorem bad_window_dev_le_v2
    {Ξ Rde C₂ Cα M δ₀ Y₀ t : ℝ} {α : ℂ} {F Φ : ℂ → ℂ} {w : ℂ} {c₁ c₂ : ℝ}
    (hRde : 0 < Rde) (hC₂ : 0 ≤ C₂)
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hw : w = Complex.I ∨ w = -Complex.I)
    (hCα : Cα = (1 / α).re - Ξ) (hM : M = -(w.im) * (1 / α).im)
    (hδ : δ₀ = Real.sqrt 2 * Rde - Cα)
    (hCα4 : Ξ + 4 ≤ Cα) (hCα0 : 0 < Cα) (hΞ0 : 0 < Ξ)
    (hwalk : ∀ β : ℝ, Y₀ ≤ β →
      (∀ j : ℕ, j ≤ Work.Pert.PinLogDev.Nlen Rde → F^[j] ((β : ℂ) * w) ∈ Work.Pert.Qm Ξ α) ∧
      (∀ j : ℕ, j ≤ Work.Pert.PinLogDev.Nlen Rde →
        31 * (j : ℝ) / 32 ≤ (F^[j] ((β : ℂ) * w)).re) ∧
      (∀ j : ℕ, j ≤ Work.Pert.PinLogDev.Nlen Rde →
        (F^[j] ((β : ℂ) * w)).re ≤ 33 * (j : ℝ) / 32) ∧
      (∀ j : ℕ, j ≤ Work.Pert.PinLogDev.Nlen Rde →
        |(F^[j] ((β : ℂ) * w)).im - ((β : ℂ) * w).im| ≤ (j : ℝ) / 32) ∧
      ‖Work.Pert.PinAux.Dev Φ (F^[Work.Pert.PinLogDev.Nlen Rde] ((β : ℂ) * w))
          - Work.Pert.PinAux.Dev Φ ((β : ℂ) * w)‖ ≤ (Work.Pert.PinLogDev.Nlen Rde : ℝ) / 32)
    (hgeo : 34 * (Work.Pert.PinLogDev.Nlen Rde : ℝ) + 32 + 32 * Real.sqrt 2 * Rde ≤ 32 * (Y₀ - Ξ))
    (h1 : Y₀ ≤ c₁) (h12 : c₁ ≤ c₂) (h2 : c₂ ≤ t)
    (hw₁ : M - δ₀ ≤ c₁) (hw₂ : c₂ ≤ M + δ₀) :
    ‖Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w)‖
      ≤ Work.Pert.PinLogDev.Kbad Rde C₂ := by
  have hNnn : (0 : ℝ) ≤ (Nlen Rde : ℝ) := Nat.cast_nonneg _
  have hY0pos : 0 < Y₀ := by
    have h32 : (32 : ℝ) ≤ 32 * (Y₀ - Ξ) := by
      nlinarith [hgeo, hNnn, hRde, Real.sqrt_nonneg 2]
    linarith
  have hY2 : Y₀ ≤ c₂ := le_trans h1 h12
  have hwim : |w.im| = 1 := by
    rcases hw with h | h <;> (rw [h]; norm_num)
  obtain ⟨hw1a, hw1b, hw1c, hw1d, hw1e⟩ := hwalk c₁ h1
  obtain ⟨hw2a, hw2b, hw2c, hw2d, hw2e⟩ := hwalk c₂ hY2
  set z₁ : ℂ := F^[Nlen Rde] ((c₁ : ℂ) * w) with hz₁
  set z₂ : ℂ := F^[Nlen Rde] ((c₂ : ℂ) * w) with hz₂
  have hz1re_lo : 31 * (Nlen Rde : ℝ) / 32 ≤ z₁.re := hw1b _ le_rfl
  have hz1re_hi : z₁.re ≤ 33 * (Nlen Rde : ℝ) / 32 := hw1c _ le_rfl
  have hz2re_lo : 31 * (Nlen Rde : ℝ) / 32 ≤ z₂.re := hw2b _ le_rfl
  have hz2re_hi : z₂.re ≤ 33 * (Nlen Rde : ℝ) / 32 := hw2c _ le_rfl
  have hz1im : |z₁.im - c₁ * w.im| ≤ (Nlen Rde : ℝ) / 32 := by
    have h := hw1d _ le_rfl
    have he : (((c₁ : ℂ) * w)).im = c₁ * w.im := by simp
    rwa [he] at h
  have hz2im : |z₂.im - c₂ * w.im| ≤ (Nlen Rde : ℝ) / 32 := by
    have h := hw2d _ le_rfl
    have he : (((c₂ : ℂ) * w)).im = c₂ * w.im := by simp
    rwa [he] at h
  -- the vertical width of the window
  have hδle : δ₀ ≤ Real.sqrt 2 * Rde := by
    rw [hδ]; linarith [hCα0]
  have hcc : c₂ - c₁ ≤ 2 * Real.sqrt 2 * Rde := by
    have h : c₂ - c₁ ≤ (M + δ₀) - (M - δ₀) := by linarith [hw₁, hw₂]
    linarith [h, hδle]
  have hdist : ‖z₂ - z₁‖ ≤ 2 * Real.sqrt 2 * Rde + (Nlen Rde : ℝ) / 8 := by
    have h := axis_seg_dist (n := (Nlen Rde : ℝ)) (c₁ := c₁) (c₂ := c₂)
      (w := w) (z₁ := z₁) (z₂ := z₂) hwim h12 hz1re_lo hz1re_hi hz2re_lo hz2re_hi hz1im hz2im
    linarith [h, hcc]
  have hseg : ‖Work.Pert.PinAux.Dev Φ z₂ - Work.Pert.PinAux.Dev Φ z₁‖
      ≤ (C₂ / Rde + 1 / 31) * (2 * Real.sqrt 2 * Rde + (Nlen Rde : ℝ) / 8) := by
    have h := dev_seg_bound hRde hC₂ hΞ0 hCα0 hDE hNT hΦ hCα hwim hgeo h1 hY2
      hz1re_lo hz1re_hi hz2re_lo hz2re_hi hz1im hz2im
    have hΛ : (0 : ℝ) ≤ C₂ / Rde + 1 / 31 := by
      have : 0 ≤ C₂ / Rde := div_nonneg hC₂ (le_of_lt hRde)
      linarith
    exact le_trans h (mul_le_mul_of_nonneg_left hdist hΛ)
  -- the two walk corrections
  have htri : ‖Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w)‖
      ≤ (Nlen Rde : ℝ) / 16 + ‖Work.Pert.PinAux.Dev Φ z₂ - Work.Pert.PinAux.Dev Φ z₁‖ := by
    have hdec : Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w)
        = (Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ z₂)
          + (Work.Pert.PinAux.Dev Φ z₂ - Work.Pert.PinAux.Dev Φ z₁)
          + (Work.Pert.PinAux.Dev Φ z₁ - Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w)) := by ring
    rw [hdec]
    have hA : ‖Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ z₂‖
        ≤ (Nlen Rde : ℝ) / 32 := by
      rw [norm_sub_rev]; exact hw2e
    have h1' : ‖(Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ z₂)
        + (Work.Pert.PinAux.Dev Φ z₂ - Work.Pert.PinAux.Dev Φ z₁)‖
        ≤ ‖Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ z₂‖
          + ‖Work.Pert.PinAux.Dev Φ z₂ - Work.Pert.PinAux.Dev Φ z₁‖ := norm_add_le _ _
    calc ‖(Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ z₂)
          + (Work.Pert.PinAux.Dev Φ z₂ - Work.Pert.PinAux.Dev Φ z₁)
          + (Work.Pert.PinAux.Dev Φ z₁ - Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w))‖
        ≤ ‖(Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ z₂)
            + (Work.Pert.PinAux.Dev Φ z₂ - Work.Pert.PinAux.Dev Φ z₁)‖
          + ‖Work.Pert.PinAux.Dev Φ z₁ - Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w)‖ :=
          norm_add_le _ _
      _ ≤ ((Nlen Rde : ℝ) / 32 + ‖Work.Pert.PinAux.Dev Φ z₂ - Work.Pert.PinAux.Dev Φ z₁‖)
          + (Nlen Rde : ℝ) / 32 := by linarith [h1', hA, hw1e]
      _ = (Nlen Rde : ℝ) / 16
          + ‖Work.Pert.PinAux.Dev Φ z₂ - Work.Pert.PinAux.Dev Φ z₁‖ := by ring
  have hmain : ‖Work.Pert.PinAux.Dev Φ ((c₂ : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((c₁ : ℂ) * w)‖
      ≤ (Nlen Rde : ℝ) / 16
        + (C₂ / Rde + 1 / 31) * (2 * Real.sqrt 2 * Rde + (Nlen Rde : ℝ) / 8) := by
    linarith [htri, hseg]
  have hKbad : (Nlen Rde : ℝ) / 16
        + (C₂ / Rde + 1 / 31) * (2 * Real.sqrt 2 * Rde + (Nlen Rde : ℝ) / 8) ≤ Kbad Rde C₂ := by
    rw [Kbad]; linarith
  linarith [hmain, hKbad]

end

end Work.Pert.PinLogDev
