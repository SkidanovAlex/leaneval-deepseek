import Mathlib
import Submission.Work.FlowerGlue2.incr_defs
import Submission.Work.FlowerGlue2.h_c0_differentiableOn
import Submission.Work.FatouCoord.Exist.exists_eq_of_deriv_close
import Submission.Work.FlowerGlue2.exists_preimage_of_lipschitz

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Lavaurs

open Metric Set
open scoped Topology

noncomputable section

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- The parabolic normal-form germ `ζ ↦ ζ + ζ²·h_{c₀}(ζ)`. -/
def normalFormMap (P : Work.PARIMPL.ParNormal d) (ζ : ℂ) : ℂ := ζ + ζ ^ 2 * P.h c₀ ζ

/-- **Cauchy estimate for the germ `h_{c₀}`.**  On the quarter-ball `‖w‖ ≤ r/4` the derivative of
the germ is bounded by `4/r`: the sphere of radius `r/2` around `w` is contained in the chart ball
`‖z‖ < r`, on which `‖h‖ ≤ 2`. -/
theorem norm_deriv_h_le (P : Work.PARIMPL.ParNormal d) {w : ℂ} (hw : ‖w‖ ≤ P.r / 4) :
    ‖deriv (P.h c₀) w‖ ≤ 4 / P.r := by
  have hB := P.bounds c₀ (mem_ball_self P.hρ₀)
  have hR : 0 < P.r / 2 := by linarith [P.hr]
  have hcl : DiffContOnCl ℂ (P.h c₀) (Metric.ball w (P.r / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball w (ne_of_gt hR)]
    refine (Work.FlowerGlue2.h_c0_differentiableOn P).mono ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_zero_right]
    have : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
      calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
    linarith [P.hr]
  have hval := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := P.h c₀)
    (c := w) (R := P.r / 2) (C := 2) hR hcl ?_
  · have : (2 : ℝ) / (P.r / 2) = 4 / P.r := by ring_nf
    linarith
  · intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    refine hB.2.2.2.1 z ?_
    have : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
      calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
    linarith [P.hr]

/-- **Derivative of the normal-form germ.**  As `h_{c₀}` is holomorphic near `0`, the tangent-to-
the-identity germ `ζ ↦ ζ + ζ²·h_{c₀}(ζ)` has derivative `1 + 2ζ·h_{c₀}(ζ) + ζ²·h_{c₀}'(ζ)`. -/
theorem deriv_normalFormMap (P : Work.PARIMPL.ParNormal d) {w : ℂ} (hw : ‖w‖ < P.r) :
    deriv (normalFormMap P) w
      = 1 + (2 * w * P.h c₀ w + w ^ 2 * deriv (P.h c₀) w) := by
  have hwball : w ∈ Metric.ball (0 : ℂ) P.r := by simpa using hw
  have hdw : DifferentiableAt ℂ (P.h c₀) w :=
    (Work.FlowerGlue2.h_c0_differentiableOn P).differentiableAt (isOpen_ball.mem_nhds hwball)
  have hpow : HasDerivAt (fun ζ : ℂ => ζ ^ 2) (2 * w) w := by
    simpa using hasDerivAt_pow 2 w
  have hprod : HasDerivAt (fun ζ : ℂ => ζ ^ 2 * P.h c₀ ζ)
      ((2 * w) * P.h c₀ w + w ^ 2 * deriv (P.h c₀) w) w := hpow.mul hdw.hasDerivAt
  have hsum := (hasDerivAt_id w).add hprod
  exact hsum.deriv

/-- **Local surjectivity of the parabolic normal form at `c₀`.**

At the parabolic parameter `a c₀ = 0`, so in the chart `z = m c₀ + s c₀·ζ` the second return map
is `ζ ↦ ζ + ζ²·h_{c₀} ζ`.  The germ `φ ζ = ζ + ζ² * P.h c₀ ζ` is tangent to the identity at `0`
(the `ζ²` prefactor kills the `h c₀ 0` term), hence is locally a bijection there: every `ξ` with
`‖ξ‖ ≤ ε` has a preimage `ζ` inside the smallness ball `rsmall P` of
`Work.FlowerGlue2.incr_defs` (the ball on which the per-step estimates of the increment hold).
Note that no hypothesis on `h c₀ 0` is needed, and `ζ = 0` is allowed when `ξ = 0`.

*Suggested route*: `P.h c₀` is holomorphic on `ball 0 P.r`
(`Work.FlowerGlue2.h_c0_differentiableOn`).  Differentiate `φ` with `deriv_add`, `deriv_mul`,
`deriv_pow`; bound `‖h‖ ≤ 2` (`ParBounds`) and `‖deriv (P.h c₀) w‖ ≤ L` on a small ball (Cauchy
estimate `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`, whose sphere hypothesis is the bound
`‖h‖ ≤ 2`), so that `‖deriv φ w - 1‖ ≤ 1/2` on `closedBall ξ (2‖ξ‖)` when `‖ξ‖` is small.  Then
`Work.FatouCoord.Exist.exists_eq_of_deriv_close` (`ψ := φ`, `τ := ξ`, `ρ := 2‖ξ‖`, `q := 1/2`)
gives `ζ` with `φ ζ = ξ` and `‖ζ - ξ‖ ≤ 2‖ξ‖`, hence `‖ζ‖ ≤ 3‖ξ‖ ≤ rsmall P` for
`‖ξ‖ ≤ rsmall P / 3`.  (A Banach fixed point alternative: the Lipschitz bound on `h c₀` from the
same Cauchy estimate plus `Convex.norm_image_sub_le_of_norm_deriv_le` feeds
`Work.FlowerGlue2.exists_preimage_of_lipschitz`.) -/
theorem exists_normalForm_preimage {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ξ : ℂ, ‖ξ‖ ≤ ε →
      ∃ ζ : ℂ, ζ + ζ ^ 2 * P.h c₀ ζ = ξ ∧ ‖ζ‖ ≤ Work.FlowerGlue2.rsmall P := by
  have hB := P.bounds c₀ (mem_ball_self P.hρ₀)
  have hrm : 0 < Work.FlowerGlue2.rsmall P := Work.FlowerGlue2.rsmall_pos P
  refine ⟨min (Work.FlowerGlue2.rsmall P / 3) (min (P.r / 12) (1 / 30)), ?_, ?_⟩
  · exact lt_min (by linarith) (lt_min (by linarith [P.hr]) (by norm_num))
  · intro ξ hξ
    have hξ1 : ‖ξ‖ ≤ Work.FlowerGlue2.rsmall P / 3 := le_trans hξ (min_le_left _ _)
    have hξ2 : ‖ξ‖ ≤ P.r / 12 :=
      le_trans hξ (le_trans (min_le_right _ _) (min_le_left _ _))
    have hξ3 : ‖ξ‖ ≤ 1 / 30 :=
      le_trans hξ (le_trans (min_le_right _ _) (min_le_right _ _))
    by_cases h0 : ξ = 0
    · subst h0
      exact ⟨0, by simp, by simp only [norm_zero]; linarith⟩
    have hξpos : 0 < ‖ξ‖ := norm_pos_iff.mpr h0
    have hξr : ‖ξ‖ < P.r := by linarith [P.hr, hξ2]
    have hhξ : ‖P.h c₀ ξ‖ ≤ 2 := hB.2.2.2.1 ξ hξr
    -- the derivative of the germ is within `1/2` of `1` on the closed ball of radius `2‖ξ‖`
    have hbound : ∀ w : ℂ, dist w ξ ≤ 2 * ‖ξ‖ →
        ‖deriv (normalFormMap P) w - 1‖ ≤ 1 / 2 := by
      intro w hw
      have hw3 : ‖w‖ ≤ 3 * ‖ξ‖ := by
        rw [dist_eq_norm] at hw
        have hle : ‖w‖ ≤ ‖w - ξ‖ + ‖ξ‖ := by
          calc ‖w‖ = ‖(w - ξ) + ξ‖ := by ring_nf
            _ ≤ ‖w - ξ‖ + ‖ξ‖ := norm_add_le _ _
        linarith
      have hwr : ‖w‖ < P.r := by linarith [P.hr, hξ2]
      have hw4 : ‖w‖ ≤ P.r / 4 := by linarith [hξ2]
      have hhw : ‖P.h c₀ w‖ ≤ 2 := hB.2.2.2.1 w hwr
      have hdhd : ‖deriv (P.h c₀) w‖ ≤ 4 / P.r := norm_deriv_h_le P hw4
      rw [deriv_normalFormMap P hwr]
      have hsub : (1 + (2 * w * P.h c₀ w + w ^ 2 * deriv (P.h c₀) w)) - 1
          = 2 * w * P.h c₀ w + w ^ 2 * deriv (P.h c₀) w := by ring
      rw [hsub]
      have h1 : ‖2 * w * P.h c₀ w‖ ≤ 12 * ‖ξ‖ := by
        rw [norm_mul, norm_mul]
        simp only [Complex.norm_ofNat]
        nlinarith [hw3, hhw, norm_nonneg ξ, norm_nonneg w, norm_nonneg (P.h c₀ w)]
      have h2 : ‖w ^ 2 * deriv (P.h c₀) w‖ ≤ 36 * ‖ξ‖ ^ 2 / P.r := by
        rw [norm_mul, norm_pow]
        have hw2 : ‖w‖ ^ 2 ≤ 9 * ‖ξ‖ ^ 2 := by nlinarith [hw3, norm_nonneg w, norm_nonneg ξ]
        calc ‖w‖ ^ 2 * ‖deriv (P.h c₀) w‖
            ≤ (9 * ‖ξ‖ ^ 2) * (4 / P.r) :=
              mul_le_mul hw2 hdhd (norm_nonneg _) (by positivity)
          _ = 36 * ‖ξ‖ ^ 2 / P.r := by ring
      have h3 : 36 * ‖ξ‖ ^ 2 / P.r ≤ 3 * ‖ξ‖ := by
        rw [div_le_iff₀ P.hr]
        nlinarith [hξ2, P.hr, norm_nonneg ξ]
      calc ‖2 * w * P.h c₀ w + w ^ 2 * deriv (P.h c₀) w‖
          ≤ ‖2 * w * P.h c₀ w‖ + ‖w ^ 2 * deriv (P.h c₀) w‖ := norm_add_le _ _
        _ ≤ 12 * ‖ξ‖ + 36 * ‖ξ‖ ^ 2 / P.r := add_le_add h1 h2
        _ ≤ 12 * ‖ξ‖ + 3 * ‖ξ‖ := by linarith
        _ ≤ 1 / 2 := by linarith
    have hdiff : ∀ w : ℂ, dist w ξ ≤ 2 * ‖ξ‖ →
        DifferentiableAt ℂ (normalFormMap P) w := by
      intro w hw
      have hw3 : ‖w‖ ≤ 3 * ‖ξ‖ := by
        rw [dist_eq_norm] at hw
        have hle : ‖w‖ ≤ ‖w - ξ‖ + ‖ξ‖ := by
          calc ‖w‖ = ‖(w - ξ) + ξ‖ := by ring_nf
            _ ≤ ‖w - ξ‖ + ‖ξ‖ := norm_add_le _ _
        linarith
      have hwr : ‖w‖ < P.r := by linarith [P.hr, hξ2]
      have hwball : w ∈ Metric.ball (0 : ℂ) P.r := by simpa using hwr
      have hdw : DifferentiableAt ℂ (P.h c₀) w :=
        (Work.FlowerGlue2.h_c0_differentiableOn P).differentiableAt
          (isOpen_ball.mem_nhds hwball)
      have hpow : DifferentiableAt ℂ (fun ζ : ℂ => ζ ^ 2) w :=
        (hasDerivAt_pow 2 w).differentiableAt
      show DifferentiableAt ℂ (fun ζ : ℂ => ζ + ζ ^ 2 * P.h c₀ ζ) w
      exact differentiableAt_id.add (hpow.mul hdw)
    have hclose : dist (normalFormMap P ξ) ξ ≤ (1 - 1 / 2) * (2 * ‖ξ‖) := by
      have hval : normalFormMap P ξ - ξ = ξ ^ 2 * P.h c₀ ξ := by
        simp only [normalFormMap]; ring
      rw [dist_eq_norm, hval, norm_mul, norm_pow]
      have h1 : (1 - 1 / 2) * (2 * ‖ξ‖) = ‖ξ‖ := by ring
      rw [h1]
      nlinarith [hξ3, hhξ, norm_nonneg ξ]
    obtain ⟨ζ, hζdist, hζeq⟩ := Work.FatouCoord.Exist.exists_eq_of_deriv_close
      (ψ := normalFormMap P) (τ := ξ) (ρ := 2 * ‖ξ‖) (q := 1 / 2)
      (by linarith) (by norm_num) (by norm_num) hdiff hbound hclose
    refine ⟨ζ, hζeq, ?_⟩
    rw [dist_eq_norm] at hζdist
    have hle : ‖ζ‖ ≤ ‖ζ - ξ‖ + ‖ξ‖ := by
      calc ‖ζ‖ = ‖(ζ - ξ) + ξ‖ := by ring_nf
        _ ≤ ‖ζ - ξ‖ + ‖ξ‖ := norm_add_le _ _
    linarith [hξ1]

end

end Work.PARIMPL2.Lavaurs
