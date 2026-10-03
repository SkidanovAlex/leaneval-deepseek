import Mathlib
import Submission.Work.Repel.R3Level1.koebe_covering_open
import Submission.Work.Repel.invFunOn_differentiableOn

/-!
# Localising a point from a bound on its image

If `φ` is holomorphic and injective on the disc `ball c ρ`, if `‖deriv φ‖ ≥ g > 0` there, and if
`φ w` is not farther from the origin than `σ` while `φ c` is within `δ` of it, then `w` cannot be
far from `c`:

  `‖w - c‖ ≤ 8 * (σ + δ) / g`.

The proof is the classical Koebe/Schwarz argument.  By Koebe's one-quarter theorem in the open-disc
form `Work.Repel.R3Level1.koebe_covering_open`, the image of `ball c ρ` contains the disc of radius
`R = ρ * g / 4` around `φ c`; on that disc the inverse `ψ` of `φ` is holomorphic and maps into
`ball c ρ`.  Hence `h y = ψ y - c` is a holomorphic map of `ball (φ c) R` into the closed disc of
radius `ρ` with `h (φ c) = 0`, and the Schwarz lemma
(`Complex.dist_le_div_mul_dist_of_mapsTo_ball`) gives

  `‖w - c‖ = ‖h (φ w)‖ ≤ (ρ / R) * ‖φ w - φ c‖ = (4 / g) * ‖φ w - φ c‖`

as soon as `‖φ w - φ c‖ < R`; then `‖φ w - φ c‖ ≤ ‖φ w‖ + ‖φ c‖ ≤ σ + δ`.  If instead
`‖φ w - φ c‖ ≥ R` then `σ + δ ≥ ρ * g / 4`, so `ρ ≤ 4 (σ + δ) / g ≤ 8 (σ + δ) / g` while
`‖w - c‖ < ρ`.  In either case `‖w - c‖ ≤ 8 (σ + δ) / g`.
-/

namespace Work.Repel.R3Level1

open Metric Set Function

theorem koebe_localize {φ : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {ρ σ δ g : ℝ}
    (hρ : 0 < ρ) (hg : 0 < g) (hφ : DifferentiableOn ℂ φ U)
    (hsub : Metric.ball c ρ ⊆ U) (hinj : Set.InjOn φ (Metric.ball c ρ))
    (hlow : ∀ w ∈ Metric.ball c ρ, g ≤ ‖deriv φ w‖)
    (hc : ‖φ c‖ < δ) (hσ : 0 ≤ σ) :
    ∀ w ∈ Metric.ball c ρ, ‖φ w‖ ≤ σ → ‖w - c‖ ≤ 8 * (σ + δ) / g := by
  intro w hw hwσ
  have hφball : DifferentiableOn ℂ φ (Metric.ball c ρ) := hφ.mono hsub
  -- Koebe's one-quarter theorem: the image covers a disc of radius `ρ / 4 * ‖φ' c‖`
  have hcover := koebe_covering_open hρ hφball hinj
  have hlowc : g ≤ ‖deriv φ c‖ := hlow c (Metric.mem_ball_self hρ)
  set R : ℝ := ρ * g / 4 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hgR : R ≤ ρ / 4 * ‖deriv φ c‖ := by
    rw [hRdef]
    nlinarith [norm_nonneg (deriv φ c)]
  have hcoverR : Metric.ball (φ c) R ⊆ φ '' Metric.ball c ρ :=
    (Metric.ball_subset_ball hgR).trans hcover
  -- the inverse of `φ` on the disc, holomorphic on that covered disc
  let ψ : ℂ → ℂ := Function.invFunOn φ (Metric.ball c ρ)
  have hψdiff : DifferentiableOn ℂ ψ (Metric.ball (φ c) R) :=
    (Work.Repel.invFunOn_differentiableOn Metric.isOpen_ball hinj hφball).mono hcoverR
  have hψc : ψ (φ c) = c := hinj.leftInvOn_invFunOn (Metric.mem_ball_self hρ)
  have hδpos : 0 < δ := lt_of_le_of_lt (norm_nonneg _) hc
  have hσδ : 0 ≤ σ + δ := by linarith
  have hdb : ‖φ w - φ c‖ ≤ σ + δ := by
    have := norm_sub_le (φ w) (φ c)
    linarith
  -- the Schwarz lemma step
  have main : ‖w - c‖ ≤ 4 * (σ + δ) / g := by
    by_cases hcase : ‖φ w - φ c‖ < R
    · have hdiffmap : DifferentiableOn ℂ (fun y => ψ y - c) (Metric.ball (φ c) R) :=
        hψdiff.sub_const c
      have hcenter : (fun y => ψ y - c) (φ c) = 0 := by simp [hψc]
      have hmaps : MapsTo (fun y => ψ y - c) (Metric.ball (φ c) R)
          (Metric.closedBall ((fun y => ψ y - c) (φ c)) ρ) := by
        intro y hy
        show ψ y - c ∈ Metric.closedBall ((fun y => ψ y - c) (φ c)) ρ
        rw [hcenter, Metric.mem_closedBall, dist_eq_norm, sub_zero]
        have hymem : ψ y ∈ Metric.ball c ρ := Function.invFunOn_mem (hcoverR hy)
        rw [Metric.mem_ball, dist_eq_norm] at hymem
        exact le_of_lt hymem
      have hz : φ w ∈ Metric.ball (φ c) R := by
        rw [Metric.mem_ball, dist_eq_norm]; exact hcase
      have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiffmap hmaps hz
      have hψw : ψ (φ w) = w := hinj.leftInvOn_invFunOn hw
      have hleft : dist ((fun y => ψ y - c) (φ w)) ((fun y => ψ y - c) (φ c)) = ‖w - c‖ := by
        simp [hψw, hψc, dist_eq_norm]
      rw [hleft, dist_eq_norm] at hsch
      have hratio : ρ / R = 4 / g := by
        have hg0 : g ≠ 0 := ne_of_gt hg
        have hρ0 : ρ ≠ 0 := ne_of_gt hρ
        rw [hRdef]
        field_simp
      calc ‖w - c‖ ≤ ρ / R * ‖φ w - φ c‖ := hsch
        _ = 4 / g * ‖φ w - φ c‖ := by rw [hratio]
        _ ≤ 4 / g * (σ + δ) := mul_le_mul_of_nonneg_left hdb (by positivity)
        _ = 4 * (σ + δ) / g := by ring
    · -- `w` is already far out: then `σ + δ ≥ ρ g / 4` and the bound is trivial
      have hle : R ≤ ‖φ w - φ c‖ := not_lt.mp hcase
      have hwρ : ‖w - c‖ < ρ := by
        rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw
      have hρle : ρ ≤ 4 * (σ + δ) / g := by
        rw [le_div_iff₀ hg]
        rw [hRdef] at hle
        nlinarith
      linarith
  have h48 : 4 * (σ + δ) / g ≤ 8 * (σ + δ) / g := by
    rw [div_le_div_iff_of_pos_right hg]
    linarith
  linarith

end Work.Repel.R3Level1
