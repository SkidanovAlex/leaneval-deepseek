import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Interfaces.FatouNarrow

/-!
# `Work.Pert.deriv_Phi_close_on_gate`

`Φ' ≈ 1` on the gate.  `FatouDerivEstimate` (`MandelDim.FatouDerivEstimate`) applies to the
vertical displacement map `v := F - id` of the near-translation `F` (so `z + v z = F z` and the
Abel equation `Φ (z + v z) = Φ z + 1` is the defining property of the Fatou coordinate), and gives
`‖Φ' z - 1/v z‖ ≤ C₂/R` on every ball `ball z R ⊆ Qm` with `R ≥ Rde`.  On such a ball
`‖v z - 1‖ ≤ 1/32`, hence `‖1/v z - 1‖ ≤ 1/31`; the two together give `‖Φ' z - 1‖ ≤ 1/64 + 1/31 < 1/2`
once `R ≥ 64 C₂`.

This is the input `(B)` of `NOTES_PERT_assembly.md` §I.1 (used by `Work.Pert.image_cover` and
`Work.Pert.image_segment_of_walk`).
-/

namespace Work.Pert

open MandelDim Complex Set Metric

theorem deriv_Phi_close_on_gate (hDE : MandelDim.FatouDerivEstimate)
    {F Φ : ℂ → ℂ} {α : ℂ} {ξ₁ : ℝ}
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm ξ₁ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm ξ₁ α)) :
    ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ z : ℂ, ∀ R : ℝ, R₁ ≤ R → Metric.ball z R ⊆ Work.Pert.Qm ξ₁ α →
      ‖deriv Φ z - 1‖ ≤ 1 / 2 := by
  obtain ⟨Rde, C₁, C₂, hRde, hC₁', hC₂, hDE'⟩ := hDE
  refine ⟨max Rde (64 * C₂), lt_max_iff.mpr (Or.inl hRde), ?_⟩
  intro z R hR hball
  have hRQ : Rde ≤ R := le_trans (le_max_left _ _) hR
  have hRpos : 0 < R := lt_of_lt_of_le (lt_max_iff.mpr (Or.inl hRde)) hR
  have hzball : z ∈ Metric.ball z R := by rw [Metric.mem_ball]; simpa using hRpos
  have hzQ : z ∈ Work.Pert.Qm ξ₁ α := hball hzball
  -- the vertical displacement map `v = F - id`
  set v : ℂ → ℂ := fun w => F w - w with hv
  have hvdiff : DifferentiableOn ℂ v (Metric.ball z R) := by
    have h1 : DifferentiableOn ℂ (fun w : ℂ => F w - w) (Metric.ball z R) :=
      (hNT.1.1.mono hball).sub differentiableOn_id
    simpa [v] using h1
  have hvnear : ∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4 := by
    intro w hw
    have hwQ : w ∈ Work.Pert.Qm ξ₁ α := hball hw
    have hbound : ‖v w - 1‖ ≤ 1 / 32 := by
      have heq : v w - 1 = F w - (w + 1) := by simp only [v]; ring
      rw [heq]; exact (hNT.1.2 w hwQ).1
    linarith
  have habel : ∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1 := by
    intro w hw hwv
    have hwQ : w ∈ Work.Pert.Qm ξ₁ α := hball hw
    have heq : w + v w = F w := by simp only [v]; ring
    have hFQ : F w ∈ Work.Pert.Qm ξ₁ α := by rw [← heq]; exact hball hwv
    have h := hΦ.2.2 w hwQ hFQ
    rwa [heq]
  have hΦdiff : DifferentiableOn ℂ Φ (Metric.ball z R) := hΦ.1.mono hball
  have hΦinj : Set.InjOn Φ (Metric.ball z R) := hΦ.2.1.mono hball
  obtain ⟨_, hb2⟩ := hDE' Φ v z R hRQ hΦdiff hΦinj hvdiff hvnear habel
  -- `C₂ / R ≤ 1/64`
  have hC2R : C₂ / R ≤ 1 / 64 := by
    rw [div_le_iff₀ hRpos]
    nlinarith [le_trans (le_max_right (Rde : ℝ) (64 * C₂)) hR]
  -- `‖1/v z - 1‖ ≤ 1/31`, since `‖v z - 1‖ ≤ 1/32`
  have hvinv : ‖1 / v z - 1‖ ≤ 1 / 31 := by
    have hvz : ‖v z - 1‖ ≤ 1 / 32 := by
      have heq : v z - 1 = F z - (z + 1) := by simp only [v]; ring
      rw [heq]; exact (hNT.1.2 z hzQ).1
    have h1a : ‖1 - v z‖ ≤ 1 / 32 := by
      rw [norm_sub_rev (1 : ℂ) (v z)]; exact hvz
    have hanorm : (31 : ℝ) / 32 ≤ ‖v z‖ := by
      have h1 : (1 : ℝ) ≤ ‖v z‖ + ‖1 - v z‖ := by
        have he : (1 : ℂ) = v z + (1 - v z) := by ring
        calc (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
          _ = ‖v z + (1 - v z)‖ := congrArg (fun x : ℂ => ‖x‖) he
          _ ≤ ‖v z‖ + ‖1 - v z‖ := norm_add_le _ _
      linarith
    have hne : v z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hanorm
      norm_num at hanorm
    rw [div_sub_one hne, norm_div]
    calc ‖1 - v z‖ / ‖v z‖ ≤ (1 / 32) / (31 / 32) :=
          div_le_div₀ (by norm_num) h1a (by norm_num) hanorm
      _ = 1 / 31 := by norm_num
  have htri : ‖deriv Φ z - 1‖ ≤ ‖deriv Φ z - 1 / v z‖ + ‖1 / v z - 1‖ := by
    have he : deriv Φ z - 1 = (deriv Φ z - 1 / v z) + (1 / v z - 1) := by ring
    rw [he]; exact norm_add_le _ _
  linarith [hb2, hC2R, hvinv, htri]

end Work.Pert
