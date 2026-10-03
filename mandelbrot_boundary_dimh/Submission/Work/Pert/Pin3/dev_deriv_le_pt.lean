import Mathlib
import Submission.Work.Pert.Pin3.dev_deriv_le

namespace Work.Pert.Pin3

/-- Pointwise-hypothesis form of `Work.Pert.Pin3.dev_deriv_le`: instead of bundling a
near-translation and a Fatou coordinate we are handed `F` close to `z ↦ z + 1` and a
shift-equivariant injective holomorphic `Φ` directly.  The proof is the same computation:
apply the derivative estimate at `z` with the displacement `v = F - id`, then replace
`1/(F z - z)` by `1` at the cost of `(32/31)‖F z - (z+1)‖`. -/
theorem dev_deriv_le_pt {F Φ : ℂ → ℂ} {Ξ : ℝ} {β : ℂ} {Rde C₂ : ℝ}
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    (hFdiff : DifferentiableOn ℂ F (Work.Pert.Qm Ξ β))
    (hFclose : ∀ z ∈ Work.Pert.Qm Ξ β, ‖F z - (z + 1)‖ ≤ 1 / 32)
    (hΦdiff : DifferentiableOn ℂ Φ (Work.Pert.Qm Ξ β))
    (hΦinj : Set.InjOn Φ (Work.Pert.Qm Ξ β))
    (hΦrel : ∀ z ∈ Work.Pert.Qm Ξ β, F z ∈ Work.Pert.Qm Ξ β → Φ (F z) = Φ z + 1)
    {z : ℂ} {R : ℝ} (hRpos : 0 < R) (hRde : Rde ≤ R)
    (hball : Metric.ball z R ⊆ Work.Pert.Qm Ξ β) :
    ‖deriv Φ z - 1‖ ≤ C₂ / R + (32 / 31) * ‖F z - (z + 1)‖ := by
  -- `v := F - id` is holomorphic on the ball and within `1/4` of `1` there.
  have hFdiff' : DifferentiableOn ℂ F (Metric.ball z R) := hFdiff.mono hball
  have hv_diff : DifferentiableOn ℂ (fun w : ℂ => F w - w) (Metric.ball z R) :=
    hFdiff'.sub differentiableOn_id
  have hzball : z ∈ Metric.ball z R := Metric.mem_ball_self hRpos
  have hv_close : ∀ w ∈ Metric.ball z R, ‖(fun w : ℂ => F w - w) w - 1‖ < 1 / 4 := by
    intro w hw
    have h := hFclose w (hball hw)
    have h1 : ‖F w - w - 1‖ = ‖F w - (w + 1)‖ := by congr 1; ring
    rw [h1]; linarith
  -- Shift-invariance of `Φ` for the displacement `v = F - id`.
  have hv_rel : ∀ w ∈ Metric.ball z R, w + (fun w : ℂ => F w - w) w ∈ Metric.ball z R →
      Φ (w + (fun w : ℂ => F w - w) w) = Φ w + 1 := by
    intro w hw hwb
    have hwv : w + (F w - w) = F w := by ring
    rw [hwv] at hwb ⊢
    exact hΦrel w (hball hw) (hball hwb)
  -- The derivative estimate at `z`.
  have hres : ‖deriv Φ z - 1 / (F z - z)‖ ≤ C₂ / R :=
    hDE Φ (fun w : ℂ => F w - w) z R hRde (hΦdiff.mono hball) (hΦinj.mono hball)
      hv_diff hv_close hv_rel
  -- `F z - z` is within `1/32` of `1`, hence invertible with
  -- `‖1/(F z - z) - 1‖ ≤ (32/31)‖F z - z - 1‖`.
  have hzQ : z ∈ Work.Pert.Qm Ξ β := hball hzball
  have hδ : ‖F z - (z + 1)‖ ≤ 1 / 32 := hFclose z hzQ
  have hu_close : ‖(F z - z) - 1‖ ≤ 1 / 32 := by
    have h1 : (F z - z) - 1 = F z - (z + 1) := by ring
    rw [h1]; exact hδ
  have hnorm_lower : (31 : ℝ) / 32 ≤ ‖F z - z‖ := by
    have h := norm_sub_le (F z - z) ((F z - z) - 1)
    have h2 : (F z - z) - ((F z - z) - 1) = (1 : ℂ) := by ring
    rw [h2, norm_one] at h
    linarith
  have hkey : ‖1 / (F z - z) - 1‖ ≤ (32 / 31) * ‖F z - (z + 1)‖ := by
    have hne : F z - z ≠ 0 := by
      intro h0
      have : ‖F z - z‖ = 0 := by rw [h0, norm_zero]
      linarith
    have heq : 1 / (F z - z) - 1 = (1 - (F z - z)) / (F z - z) := by field_simp
    rw [heq, norm_div]
    have hnum : ‖1 - (F z - z)‖ = ‖F z - (z + 1)‖ := by
      have h1 : (1 : ℂ) - (F z - z) = -(F z - (z + 1)) := by ring
      rw [h1, norm_neg]
    rw [hnum]
    have hd0 : 0 ≤ ‖F z - (z + 1)‖ := norm_nonneg _
    have hc0 : (0 : ℝ) < 31 / 32 := by norm_num
    have h1 : ‖F z - (z + 1)‖ / ‖F z - z‖ ≤ ‖F z - (z + 1)‖ / (31 / 32) :=
      div_le_div_of_nonneg_left hd0 hc0 hnorm_lower
    have h2 : ‖F z - (z + 1)‖ / (31 / 32) = (32 / 31) * ‖F z - (z + 1)‖ := by ring
    linarith
  have htri : ‖deriv Φ z - 1‖ ≤
      ‖deriv Φ z - 1 / (F z - z)‖ + ‖1 / (F z - z) - 1‖ := by
    have hsplit : deriv Φ z - 1 =
        (deriv Φ z - 1 / (F z - z)) + (1 / (F z - z) - 1) := by ring
    calc ‖deriv Φ z - 1‖
        = ‖(deriv Φ z - 1 / (F z - z)) + (1 / (F z - z) - 1)‖ := by rw [hsplit]
      _ ≤ _ := norm_add_le _ _
  linarith

end Work.Pert.Pin3
