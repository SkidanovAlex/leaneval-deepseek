import Mathlib
import Submission.Work.FQC.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar)

/-- The mandelbar iterator of `ChallengeDeps`, in terms of `star`: `z ↦ (star z)^2 + c`. -/
theorem Tantibar_eq_star (c z : ℂ) : Tantibar c z = star z ^ 2 + c := by
  simp [LeanEval.ComplexAnalysis.Tantibar]

/-- The complex conjugate of the mandelbar iterator: `star (Tantibar c z) = z^2 + star c`.
This is the (anti-)conjugation identity behind the `w ↦ w^2` asymptotics of the conjugate of
`Tantibar c` by a quasiconformal map. -/
theorem star_Tantibar_eq (c z : ℂ) : star (Tantibar c z) = z ^ 2 + star c := by
  rw [Tantibar_eq_star]
  simp

/-- `Tantibar c` is continuous. -/
theorem continuous_Tantibar (c : ℂ) : Continuous (Tantibar c) := by
  rw [show Tantibar c = fun z : ℂ => star z ^ 2 + c from funext (Tantibar_eq_star c)]
  fun_prop

/-- **Boundedness of the conjugate of `Tantibar c` by the principal solution.**

For an admissible Beltrami coefficient `μ`, the homeomorphism `φ = principal μ` conjugates the
antiholomorphic quadratic map `Tantibar c` into (the conjugate of) a map which differs from
`w ↦ w^2` by a bounded amount.  This is the elementary consequence of the normalisation
`φ z = z + O(1/‖z‖)` which is what makes the transported map a "Böttcher-type" map with
asymptotics `w²` at infinity.

The proof is the standard one: write `z = φ.symm w`.  For large `‖w‖` the point `z` is large,
so `w = φ z = z + O(1/‖z‖)`, whence `Tantibar c z = (star z)^2 + c` has large modulus and
`φ (Tantibar c z) = Tantibar c z + O(1/‖Tantibar c z‖)`.  Conjugating the identity
`star (Tantibar c z) = z^2 + star c` and using `z - w = O(1/‖w‖)` gives
`star (φ (Tantibar c (φ.symm w))) = w^2 + O(1)`.  Boundedness on the remaining compact set is
continuity. -/
theorem principal_conj_Tantibar_bounded (c : ℂ) {μ : ℂ → ℂ} (hμ : Work.MRMT.Found.Admissible μ) : ∃ M : ℝ, ∀ w : ℂ, ‖star (Work.MRMT.Found.principal μ (LeanEval.ComplexAnalysis.Tantibar c ((Work.MRMT.Found.principal μ).symm w))) - w ^ 2‖ ≤ M := by
  classical
  set φ : ℂ ≃ₜ ℂ := Work.MRMT.Found.principal μ with hφ
  have key : ∃ M : ℝ, ∀ w : ℂ, ‖star (φ (Tantibar c (φ.symm w))) - w ^ 2‖ ≤ M := by
    obtain ⟨C, R, hdec⟩ := Work.MRMT.Found.principal_decay hμ
    rw [← hφ] at hdec
    -- normalise the decay constants
    obtain ⟨C', hC'0, hdec'⟩ : ∃ C' : ℝ, 0 ≤ C' ∧
        ∀ z : ℂ, R ≤ ‖z‖ → ‖φ z - z‖ ≤ C' / ‖z‖ :=
      ⟨max C 0, le_max_right C 0, fun z hz =>
        le_trans (hdec z hz) (div_le_div_of_nonneg_right (le_max_left C 0) (norm_nonneg z))⟩
    -- the radius `ρ` at which the dynamics has expanded, and the decay applies
    set ρ : ℝ := max (max R 1) (max (‖c‖ + 2) 2) with hρdef
    have hρR : R ≤ ρ := le_trans (le_max_left R 1) (le_max_left _ _)
    have hρ1 : 1 ≤ ρ := le_trans (le_max_right R 1) (le_max_left _ _)
    have hρ2 : 2 ≤ ρ := le_trans (le_max_right (‖c‖ + 2) 2) (le_max_right _ _)
    have hρc : ‖c‖ + 2 ≤ ρ := le_trans (le_max_left (‖c‖ + 2) 2) (le_max_right _ _)
    have hρpos : 0 < ρ := lt_of_lt_of_le one_pos hρ1
    have hρ2le : ρ ≤ ρ ^ 2 - ‖c‖ := by nlinarith [hρ2, hρc, norm_nonneg c]
    -- `φ` is bounded on the disc of radius `ρ`
    obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn
      φ.continuous.continuousOn
    have hD' : ∀ z : ℂ, ‖z‖ ≤ ρ → ‖φ z‖ ≤ D := fun z hz =>
      hD z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
    set ρ₁ : ℝ := max D 0 with hρ₁def
    have hρ₁ : ∀ z : ℂ, ‖z‖ ≤ ρ → ‖φ z‖ ≤ ρ₁ :=
      fun z hz => le_trans (hD' z hz) (le_max_left D 0)
    -- continuity of the map whose boundedness we are proving
    have hcont : Continuous fun w : ℂ => star (φ (Tantibar c (φ.symm w))) - w ^ 2 :=
      (continuous_star.comp (φ.continuous.comp ((continuous_Tantibar c).comp
        φ.continuous_symm))).sub (continuous_pow 2)
    -- bounded on the compact disc
    have hsmall : ∃ K : ℝ, ∀ w : ℂ, ‖w‖ ≤ ρ₁ + 1 →
        ‖star (φ (Tantibar c (φ.symm w))) - w ^ 2‖ ≤ K := by
      obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (ρ₁ + 1)).exists_bound_of_continuousOn
        hcont.continuousOn
      exact ⟨max K 0, fun w hw =>
        le_trans (hK w (by simpa [Metric.mem_closedBall, dist_eq_norm] using hw)) (le_max_left K 0)⟩
    -- the explicit bound outside that disc
    have hlarge : ∀ w : ℂ, ρ₁ + 1 ≤ ‖w‖ →
        ‖star (φ (Tantibar c (φ.symm w))) - w ^ 2‖ ≤ C' * (C' + 2) + ‖c‖ + C' := by
      intro w hw
      set z : ℂ := φ.symm w with hz
      have hzφ : φ z = w := φ.apply_symm_apply w
      -- `z` is large
      have hzbig : ρ < ‖z‖ := by
        by_contra hcon
        simp only [not_lt] at hcon
        have h1 : ‖w‖ ≤ ρ₁ := by
          have h2 := hρ₁ z hcon
          rwa [hzφ] at h2
        linarith
      have hzR : R ≤ ‖z‖ := le_trans hρR hzbig.le
      have hz1 : 1 ≤ ‖z‖ := le_trans hρ1 hzbig.le
      have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
      -- `w` is within `O(1/‖z‖)` of `z`
      have hzw : ‖z - w‖ ≤ C' / ‖z‖ := by
        have h : z - w = -(φ z - z) := by rw [hzφ]; ring
        rw [h, norm_neg]
        exact hdec' z hzR
      have hwnorm : ‖w‖ ≤ ‖z‖ + C' := by
        have h1 : ‖w‖ - ‖z‖ ≤ C' / ‖z‖ := by
          refine le_trans (norm_sub_norm_le w z) ?_
          rwa [norm_sub_rev]
        have h2 : C' / ‖z‖ ≤ C' := by
          rw [div_le_iff₀ hzpos]
          nlinarith [hC'0, hz1]
        linarith
      -- the quadratic term
      have hz2w2 : ‖z ^ 2 - w ^ 2‖ ≤ C' * (C' + 2) := by
        have hfac : z ^ 2 - w ^ 2 = (z - w) * (z + w) := by ring
        rw [hfac, norm_mul]
        have h1 : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le _ _
        have h3 : ‖z‖ + ‖w‖ ≤ (C' + 2) * ‖z‖ := by nlinarith [hwnorm, hz1, hC'0]
        have h4 : C' / ‖z‖ * (‖z‖ + ‖w‖) ≤ C' / ‖z‖ * ((C' + 2) * ‖z‖) :=
          mul_le_mul_of_nonneg_left h3 (div_nonneg hC'0 (norm_nonneg z))
        have h5 : C' / ‖z‖ * ((C' + 2) * ‖z‖) = C' * (C' + 2) := by
          rw [← mul_assoc, div_mul_eq_mul_div C' ‖z‖ (C' + 2),
            div_mul_cancel₀ _ (ne_of_gt hzpos)]
        calc ‖z - w‖ * ‖z + w‖ ≤ C' / ‖z‖ * (‖z‖ + ‖w‖) :=
              mul_le_mul hzw h1 (norm_nonneg _) (div_nonneg hC'0 (norm_nonneg z))
          _ ≤ C' / ‖z‖ * ((C' + 2) * ‖z‖) := h4
          _ = C' * (C' + 2) := h5
      -- the argument of the second `φ` is large, so the decay applies there too
      have hTnorm : ρ ≤ ‖Tantibar c z‖ := by
        rw [Tantibar_eq_star]
        have h4 := norm_sub_le (star z ^ 2 + c) c
        have h5 : star z ^ 2 + c - c = star z ^ 2 := by ring
        rw [h5, norm_pow, norm_star] at h4
        have h6 : ρ ≤ ‖z‖ ^ 2 - ‖c‖ := by
          have h7 : ρ ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [hρpos.le, hzbig.le]
          linarith [hρ2le]
        linarith
      have hTdec : ‖φ (Tantibar c z) - Tantibar c z‖ ≤ C' / ρ := by
        calc ‖φ (Tantibar c z) - Tantibar c z‖ ≤ C' / ‖Tantibar c z‖ :=
              hdec' _ (le_trans hρR hTnorm)
          _ ≤ C' / ρ := div_le_div_of_nonneg_left hC'0 hρpos hTnorm
      have hstar : ‖star (φ (Tantibar c z) - Tantibar c z)‖ ≤ C' := by
        rw [norm_star]
        exact le_trans hTdec (div_le_self hC'0 hρ1)
      -- the exact identity
      have hmain : star (φ (Tantibar c z)) - w ^ 2
          = (z ^ 2 - w ^ 2) + star c + star (φ (Tantibar c z) - Tantibar c z) := by
        have hsplit : star (φ (Tantibar c z))
            = star (Tantibar c z) + star (φ (Tantibar c z) - Tantibar c z) := by
          rw [star_sub]; ring
        rw [hsplit, star_Tantibar_eq c z]; ring
      have hbound : ‖star (φ (Tantibar c z)) - w ^ 2‖ ≤ C' * (C' + 2) + ‖c‖ + C' := by
        rw [hmain]
        calc ‖(z ^ 2 - w ^ 2) + star c + star (φ (Tantibar c z) - Tantibar c z)‖
            ≤ ‖(z ^ 2 - w ^ 2) + star c‖ + ‖star (φ (Tantibar c z) - Tantibar c z)‖ :=
              norm_add_le _ _
          _ ≤ (‖z ^ 2 - w ^ 2‖ + ‖star c‖) + ‖star (φ (Tantibar c z) - Tantibar c z)‖ := by
              have hle := norm_add_le (z ^ 2 - w ^ 2) (star c)
              linarith
          _ ≤ (C' * (C' + 2) + ‖c‖) + C' := by
              rw [norm_star c]
              linarith [hz2w2, hstar]
      simpa [hz] using hbound
    obtain ⟨K, hK⟩ := hsmall
    refine ⟨max K (C' * (C' + 2) + ‖c‖ + C'), fun w => ?_⟩
    rcases lt_or_ge ‖w‖ (ρ₁ + 1) with hlt | hge
    · exact le_trans (hK w hlt.le) (le_max_left _ _)
    · exact le_trans (hlarge w hge) (le_max_right _ _)
  rw [hφ] at key
  exact key

end Work.FQC
