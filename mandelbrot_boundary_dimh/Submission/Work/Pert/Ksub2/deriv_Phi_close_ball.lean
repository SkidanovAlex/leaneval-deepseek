import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.image_cover_centered
import Submission.Work.Pert.Ksub2.deriv_diff_le
import Submission.Work.Interfaces.FatouNarrow

/-!
# `Work.Pert.Ksub2.deriv_Phi_close_ball`

`‖Φ' - 1‖ ≤ 1/2` on the gate, with the constants of Shishikura's derivative estimate
(`MandelDim.FatouDerivEstimate`, Lemma A.2.4(i)) made explicit.

The estimate is applied to the vertical displacement map `v := F - id` of the near-translation
`F`: since `z + v z = F z`, the Abel equation `Φ (z + v z) = Φ z + 1` is exactly the defining
property of the Fatou coordinate `Φ` on `Qm ξ₁ α`.  On `ball w R ⊆ Qm ξ₁ α` with `Rde ≤ R` we get

  `‖Φ' w - 1/v w‖ ≤ C₂ / R`   and   `‖v w - 1‖ ≤ 1/32`,

so `‖1/v w - 1‖ ≤ 1/31` and it remains to note `C₂ / R ≤ 1/64` because `64 C₂ ≤ R`:

  `‖Φ' w - 1‖ ≤ 1/64 + 1/31 < 1/2`. ∎

This is the input `(B)` of `NOTES_PERT_assembly.md` §I.1, in the form in which the perturbed
(constructed) coordinate `Φ` of `F = liftF u σ α` on the gate `Qm ξ₁ α` is used downstream.
-/

namespace Work.Pert.Ksub2

open MandelDim Complex Set Metric

theorem deriv_Phi_close_ball {F Φ : ℂ → ℂ} {α : ℂ} {ξ₁ Rde C₁ C₂ : ℝ}
    (hRdepos : 0 < Rde) (hC₁pos : 0 < C₁) (hC₂pos : 0 < C₂)
    (hDEest : ∀ (Φ v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z₀ R) → Set.InjOn Φ (Metric.ball z₀ R) →
      DifferentiableOn ℂ v (Metric.ball z₀ R) → (∀ z ∈ Metric.ball z₀ R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z₀ R, z + v z ∈ Metric.ball z₀ R → Φ (z + v z) = Φ z + 1) →
      ‖deriv Φ z₀ - 1 / v z₀‖ ≤ C₁ * (1 / R ^ 2 + ‖deriv v z₀‖) ∧
      ‖deriv Φ z₀ - 1 / v z₀‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm ξ₁ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm ξ₁ α)) :
    ∀ (w : ℂ) (R : ℝ), max Rde (64 * C₂) ≤ R → Metric.ball w R ⊆ Work.Pert.Qm ξ₁ α →
      ‖deriv Φ w - 1‖ ≤ 1 / 2 := by
  intro w R hR hball
  have hRQ : Rde ≤ R := le_trans (le_max_left _ _) hR
  have hRpos : 0 < R := lt_of_lt_of_le hRdepos hRQ
  have hwball : w ∈ Metric.ball w R := Metric.mem_ball_self hRpos
  have hwQ : w ∈ Work.Pert.Qm ξ₁ α := hball hwball
  -- the vertical displacement map `v = F - id`
  set v : ℂ → ℂ := fun u => F u - u with hv
  have hvdiff : DifferentiableOn ℂ v (Metric.ball w R) := by
    have h1 : DifferentiableOn ℂ (fun u : ℂ => F u - u) (Metric.ball w R) :=
      (hNT.1.1.mono hball).sub differentiableOn_id
    simpa [hv] using h1
  have hvnear : ∀ u ∈ Metric.ball w R, ‖v u - 1‖ < 1 / 4 := by
    intro u hu
    have huQ : u ∈ Work.Pert.Qm ξ₁ α := hball hu
    have hbound : ‖v u - 1‖ ≤ 1 / 32 := by
      have heq : v u - 1 = F u - (u + 1) := by simp only [hv]; ring
      rw [heq]; exact (hNT.1.2 u huQ).1
    linarith
  have habel : ∀ u ∈ Metric.ball w R, u + v u ∈ Metric.ball w R →
      Φ (u + v u) = Φ u + 1 := by
    intro u hu huv
    have huQ : u ∈ Work.Pert.Qm ξ₁ α := hball hu
    have heq : u + v u = F u := by simp only [hv]; ring
    have hFQ : F u ∈ Work.Pert.Qm ξ₁ α := by rw [← heq]; exact hball huv
    have h := hΦ.2.2 u huQ hFQ
    rwa [heq]
  have hΦdiff : DifferentiableOn ℂ Φ (Metric.ball w R) := hΦ.1.mono hball
  have hΦinj : Set.InjOn Φ (Metric.ball w R) := hΦ.2.1.mono hball
  obtain ⟨_, hb2⟩ := hDEest Φ v w R hRQ hΦdiff hΦinj hvdiff hvnear habel
  -- `C₂ / R ≤ 1/64`, since `64 C₂ ≤ R`
  have hC2R : C₂ / R ≤ 1 / 64 := by
    rw [div_le_iff₀ hRpos]
    nlinarith [le_trans (le_max_right (Rde : ℝ) (64 * C₂)) hR]
  -- `‖1/v w - 1‖ ≤ 1/31`, since `‖v w - 1‖ ≤ 1/32`
  have hvinv : ‖1 / v w - 1‖ ≤ 1 / 31 := by
    have hvw : ‖v w - 1‖ ≤ 1 / 32 := by
      have heq : v w - 1 = F w - (w + 1) := by simp only [hv]; ring
      rw [heq]; exact (hNT.1.2 w hwQ).1
    have h1a : ‖1 - v w‖ ≤ 1 / 32 := by
      rw [norm_sub_rev (1 : ℂ) (v w)]; exact hvw
    have hanorm : (31 : ℝ) / 32 ≤ ‖v w‖ := by
      have h1 : (1 : ℝ) ≤ ‖v w‖ + ‖1 - v w‖ := by
        have he : (1 : ℂ) = v w + (1 - v w) := by ring
        calc (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
          _ = ‖v w + (1 - v w)‖ := congrArg (fun x : ℂ => ‖x‖) he
          _ ≤ ‖v w‖ + ‖1 - v w‖ := norm_add_le _ _
      linarith
    have hne : v w ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hanorm
      norm_num at hanorm
    rw [div_sub_one hne, norm_div]
    calc ‖1 - v w‖ / ‖v w‖ ≤ (1 / 32) / (31 / 32) :=
          div_le_div₀ (by norm_num) h1a (by norm_num) hanorm
      _ = 1 / 31 := by norm_num
  have htri : ‖deriv Φ w - 1‖ ≤ ‖deriv Φ w - 1 / v w‖ + ‖1 / v w - 1‖ := by
    have he : deriv Φ w - 1 = (deriv Φ w - 1 / v w) + (1 / v w - 1) := by ring
    rw [he]; exact norm_add_le _ _
  linarith [hb2, hC2R, hvinv, htri]

end Work.Pert.Ksub2
