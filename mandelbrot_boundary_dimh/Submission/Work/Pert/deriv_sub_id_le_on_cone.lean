import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Pert.Setup
import Submission.Work.Pert.cone_subset_Qm
import Submission.Work.Pert.closedBall_subset_Qm

namespace Work.Pert

/-- **Derivative of the deviation on the deep cone.**  On the deep cone
`{|Re z| ≤ |Im z|/2}` of the gate `Qm ξ₁ α`, the derivative of `Φ - id` is bounded by
`C / |Im z| + 1/31`.  Proof (the child should follow `Work.Pert.deriv_Phi_close_on_gate`):
apply the second conjunct of `MandelDim.FatouDerivEstimate` to `v := fun w => F w - w` on the ball of
radius `R := |z.im| / 8` around `z` (which lies in `Qm ξ₁ α` by `Pert/closedBall_subset_Qm`, since
`|Re z| ≤ |Im z|/2`, once `|Im z| ≥ T`), giving `‖deriv Φ z - 1 / (F z - z)‖ ≤ C₂ / R = 8 * C₂ / |z.im|`;
and bound `‖1 / (F z - z) - 1‖ ≤ 1/31` from `‖(F z - z) - 1‖ ≤ 1/32` (`NearTranslationL1` gives
`NearTranslationOn`).  Conclude by the triangle inequality and `deriv (fun w => Φ w - w) z = deriv Φ z - 1`.
No pinning, no `FatouEnds`, no end asymptotics are used. -/
theorem deriv_sub_id_le_on_cone (hDE : MandelDim.FatouDerivEstimate)
    {F Φ : ℂ → ℂ} {ξ₁ : ℝ} {α : ℂ}
    (hNT : MandelDim.NearTranslationL1 F (Qm ξ₁ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Qm ξ₁ α)) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ z : ℂ, T ≤ |z.im| → |z.re| ≤ |z.im| / 2 →
      ‖deriv (fun w => Φ w - w) z‖ ≤ C / |z.im| + 1 / 31 := by
  obtain ⟨Rde, _C₁, C₂, hRde, _hC₁, hC₂, hDE'⟩ := hDE
  obtain ⟨T₁, hT₁pos, hT₁⟩ := cone_subset_Qm (ξ₁ := ξ₁) (α := α)
  obtain ⟨T₀, hT₀pos, hT₀⟩ := closedBall_subset_Qm (ξ₁ := ξ₁) (α := α)
  refine ⟨8 * C₂, max (max (8 * Rde) (8 * T₀)) T₁, by linarith, ?_, ?_⟩
  · exact lt_max_iff.mpr (Or.inr hT₁pos)
  · intro z hz hx
    have hTpos : 0 < max (max (8 * Rde) (8 * T₀)) T₁ := lt_max_iff.mpr (Or.inr hT₁pos)
    have himpos : 0 < |z.im| := lt_of_lt_of_le hTpos hz
    have himT1 : T₁ ≤ |z.im| := le_trans (le_max_right _ _) hz
    have him8Rde : 8 * Rde ≤ |z.im| :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hz
    have him8T0 : 8 * T₀ ≤ |z.im| :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hz
    have hzQ : z ∈ Qm ξ₁ α := hT₁ z himT1 hx
    have hRde' : Rde ≤ |z.im| / 8 := by linarith
    have hRpos : 0 < |z.im| / 8 := by linarith
    have hball : Metric.ball z (|z.im| / 8) ⊆ Qm ξ₁ α := by
      have h1 : Metric.closedBall z (|z.im| / 8) ⊆ Qm ξ₁ α :=
        hT₀ z (|z.im| / 2) (|z.im| / 8) (le_of_lt hRpos) hx (by linarith)
      exact fun w hw => h1 (Metric.ball_subset_closedBall hw)
    set v : ℂ → ℂ := fun w => F w - w with hv
    have hvdiff : DifferentiableOn ℂ v (Metric.ball z (|z.im| / 8)) := by
      have h1 : DifferentiableOn ℂ (fun w : ℂ => F w - w) (Metric.ball z (|z.im| / 8)) :=
        (hNT.1.1.mono hball).sub differentiableOn_id
      simpa [v] using h1
    have hvnear : ∀ w ∈ Metric.ball z (|z.im| / 8), ‖v w - 1‖ < 1 / 4 := by
      intro w hw
      have hwQ : w ∈ Qm ξ₁ α := hball hw
      have hbound : ‖v w - 1‖ ≤ 1 / 32 := by
        have heq : v w - 1 = F w - (w + 1) := by simp only [v]; ring
        rw [heq]; exact (hNT.1.2 w hwQ).1
      linarith
    have habel : ∀ w ∈ Metric.ball z (|z.im| / 8), w + v w ∈ Metric.ball z (|z.im| / 8) →
        Φ (w + v w) = Φ w + 1 := by
      intro w hw hwv
      have hwQ : w ∈ Qm ξ₁ α := hball hw
      have heq : w + v w = F w := by simp only [v]; ring
      have hFQ : F w ∈ Qm ξ₁ α := by rw [← heq]; exact hball hwv
      have h := hΦ.2.2 w hwQ hFQ
      rwa [heq]
    have hΦdiff : DifferentiableOn ℂ Φ (Metric.ball z (|z.im| / 8)) := hΦ.1.mono hball
    have hΦinj : Set.InjOn Φ (Metric.ball z (|z.im| / 8)) := hΦ.2.1.mono hball
    obtain ⟨_, hb2⟩ := hDE' Φ v z (|z.im| / 8) hRde' hΦdiff hΦinj hvdiff hvnear habel
    have hzball : z ∈ Metric.ball z (|z.im| / 8) := Metric.mem_ball_self hRpos
    have hΦz_diff : DifferentiableAt ℂ Φ z :=
      hΦdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hzball)
    have hderiv_eq : deriv (fun w => Φ w - w) z = deriv Φ z - 1 := by
      change deriv (Φ - id) z = deriv Φ z - 1
      rw [deriv_sub hΦz_diff differentiableAt_id, deriv_id]
    -- the inverse estimate `‖1/v z - 1‖ ≤ 1/31`
    have hvz : ‖v z - 1‖ ≤ 1 / 32 := by
      have heq : v z - 1 = F z - (z + 1) := by simp only [v]; ring
      rw [heq]; exact (hNT.1.2 z hzQ).1
    have hvinv : ‖1 / v z - 1‖ ≤ 1 / 31 := by
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
    have hC2R : C₂ / (|z.im| / 8) = 8 * C₂ / |z.im| := by
      rw [div_div_eq_mul_div]; ring
    rw [hC2R] at hb2
    rw [hderiv_eq]
    have htri : ‖deriv Φ z - 1‖ ≤ ‖deriv Φ z - 1 / v z‖ + ‖1 / v z - 1‖ := by
      have he : deriv Φ z - 1 = (deriv Φ z - 1 / v z) + (1 / v z - 1) := by ring
      rw [he]; exact norm_add_le _ _
    linarith [hb2, hvinv, htri]

end Work.Pert
