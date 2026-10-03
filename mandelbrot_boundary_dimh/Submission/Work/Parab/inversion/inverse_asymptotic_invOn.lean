import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.inversion.inverse_asymptotic

namespace Work.Parab.inversion

open Complex Set Metric Filter Classical
open scoped Topology

noncomputable section

/-- `Work.Parab.inversion.inverse_asymptotic` with the existential `τ` replaced by the *explicit*
choice function `invOn Φ L`: the same hypotheses yield the three conclusions for `invOn Φ L`
itself.  (The proof of `inverse_asymptotic` already establishes exactly this — it is
`refine ⟨invOn Φ L, ...⟩` — but the existential statement cannot be used where the *value* of the
inverse matters, e.g. to identify `Φ`-preimages by injectivity.) -/
theorem inverse_asymptotic_invOn {Φ : ℂ → ℂ} {L : Set ℂ} {ξ : ℝ} {a b : ℂ}
    (hξ : 0 < ξ) (hL : IsOpen L)
    (hholo : DifferentiableOn ℂ Φ L) (hinj : Set.InjOn Φ L)
    (hasym : ∀ ε > 0, ∃ R : ℝ, ∀ ζ ∈ L, R < ‖ζ‖ →
        ‖Φ ζ - (ζ - a * Complex.log (-ζ) - b)‖ < ε)
    (hproper : ∀ R : ℝ, ∃ N : ℝ, ∀ ζ ∈ L, N < ‖Φ ζ‖ → R < ‖ζ‖)
    (himg : ∀ w : ℂ, ξ < ‖w‖ → w ∈ MandelDim.QLeft ξ → ∃ ζ ∈ L, Φ ζ = w) :
    (∀ w : ℂ, ξ < ‖w‖ → w ∈ MandelDim.QLeft ξ → Φ (invOn Φ L w) = w) ∧
      DifferentiableOn ℂ (invOn Φ L) {w : ℂ | w ∈ MandelDim.QLeft ξ ∧ ξ < ‖w‖} ∧
      (∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, w ∈ MandelDim.QLeft ξ → R < ‖w‖ →
        ‖invOn Φ L w - (w + a * Complex.log (-w) + b)‖ < ε) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hwξ hwQ
    exact invOn_apply (himg w hwξ hwQ)
  · refine (differentiableOn_invOn hL ?_ ?_ hinj).mono ?_
    · intro z hz
      exact ((hholo.analyticOnNhd hL) z hz).hasStrictDerivAt
    · exact deriv_ne_zero_of_injOn hL hholo hinj
    · rintro w ⟨hwQ, hwξ⟩
      obtain ⟨ζ, hζL, hζw⟩ := himg w hwξ hwQ
      exact ⟨ζ, hζL, hζw⟩
  · intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by linarith
    obtain ⟨R₁, hR₁⟩ := hasym (ε / 2) hε2
    obtain ⟨N₁, hN₁⟩ := hproper (max R₁ 1)
    obtain ⟨W₀, _hW₀le, hW₀⟩ :=
      exists_norm_sub_le_of_asymptotic (a := a) (b := b) (δ := ε / 2) hε2
    obtain ⟨R₂, _hR₂pos, hR₂⟩ :=
      exists_mul_log_lt (A := ‖a‖) (K := ‖a‖ * Real.pi + ‖b‖ + ε / 2) (norm_nonneg a)
        (by positivity) hε
    refine ⟨max ξ (max N₁ (max W₀ R₂)), ?_⟩
    intro w hwQ hwR
    have hRξ : ξ ≤ max ξ (max N₁ (max W₀ R₂)) := le_max_left _ _
    have hRN : N₁ ≤ max ξ (max N₁ (max W₀ R₂)) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hRW : W₀ ≤ max ξ (max N₁ (max W₀ R₂)) :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    have hR2 : R₂ ≤ max ξ (max N₁ (max W₀ R₂)) :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
    have hwξ : ξ < ‖w‖ := lt_of_le_of_lt hRξ hwR
    have hwpos : 0 < ‖w‖ := lt_trans hξ hwξ
    have hhex : ∃ ζ ∈ L, Φ ζ = w := himg w hwξ hwQ
    set ζ : ℂ := invOn Φ L w with hζdef
    have hζL : ζ ∈ L := invOn_mem hhex
    have hζw : Φ ζ = w := invOn_apply hhex
    have hζbig : max R₁ 1 < ‖ζ‖ := hN₁ ζ hζL (by rw [hζw]; exact lt_of_le_of_lt hRN hwR)
    have hζ1 : 1 ≤ ‖ζ‖ := le_of_lt (lt_of_le_of_lt (le_max_right R₁ 1) hζbig)
    have hdist : ‖ζ - w - a * Complex.log (-ζ) - b‖ < ε / 2 := by
      have h := hR₁ ζ hζL (lt_of_le_of_lt (le_max_left R₁ 1) hζbig)
      have heq : Φ ζ - (ζ - a * Complex.log (-ζ) - b)
          = -(ζ - w - a * Complex.log (-ζ) - b) := by
        rw [hζw]; ring
      rwa [heq, norm_neg] at h
    obtain ⟨_hζwd, hζw2⟩ := hW₀ w ζ hζ1 hdist (le_of_lt (lt_of_le_of_lt hRW hwR))
    -- the displacement bound `‖ζ - w‖ = O(log ‖w‖)`
    have hdisp : ‖ζ - w‖
        ≤ ‖a‖ * Real.log (2 * ‖w‖) + (‖a‖ * Real.pi + ‖b‖ + ε / 2) := by
      have h1 : ‖ζ - w‖ ≤ ‖a * Complex.log (-ζ) + b‖ + ε / 2 := by
        have h2 : ζ - w = (ζ - w - a * Complex.log (-ζ) - b) + (a * Complex.log (-ζ) + b) := by
          ring
        calc ‖ζ - w‖
            = ‖(ζ - w - a * Complex.log (-ζ) - b) + (a * Complex.log (-ζ) + b)‖ := by rw [← h2]
          _ ≤ ‖ζ - w - a * Complex.log (-ζ) - b‖ + ‖a * Complex.log (-ζ) + b‖ := norm_add_le _ _
          _ ≤ ε / 2 + ‖a * Complex.log (-ζ) + b‖ := by
                linarith [hdist, norm_nonneg (a * Complex.log (-ζ) + b)]
          _ = ‖a * Complex.log (-ζ) + b‖ + ε / 2 := by ring
      have h3 : ‖a * Complex.log (-ζ) + b‖ ≤ ‖a‖ * (Real.log ‖ζ‖ + Real.pi) + ‖b‖ := by
        have hl := norm_log_le (-ζ) (by simpa using hζ1)
        rw [norm_neg] at hl
        have hl' : ‖a‖ * ‖Complex.log (-ζ)‖ ≤ ‖a‖ * (Real.log ‖ζ‖ + Real.pi) :=
          mul_le_mul_of_nonneg_left hl (norm_nonneg a)
        have hab := norm_add_le (a * Complex.log (-ζ)) b
        rw [norm_mul] at hab
        linarith
      have h4 : Real.log ‖ζ‖ ≤ Real.log (2 * ‖w‖) :=
        Real.log_le_log (lt_of_lt_of_le zero_lt_one hζ1) hζw2
      have h5 : ‖a‖ * (Real.log ‖ζ‖ + Real.pi) ≤ ‖a‖ * (Real.log (2 * ‖w‖) + Real.pi) :=
        mul_le_mul_of_nonneg_left (by linarith [h4]) (norm_nonneg a)
      linarith
    obtain ⟨hfin1, hfin2⟩ := hR₂ ‖w‖ (le_of_lt (lt_of_le_of_lt hR2 hwR))
    have hstrict : ‖ζ - w‖ < ‖w‖ / 16 := lt_of_le_of_lt hdisp hfin2
    -- replacing `log (-ζ)` by `log (-w)`
    have hlog : ‖Complex.log (-ζ) - Complex.log (-w)‖ ≤ ‖ζ - w‖ / (‖w‖ / 2) := by
      refine norm_log_neg_sub_log_neg_le (w := w) (ρ := ‖w‖ / 16) (c := ‖w‖ / 2)
        (by positivity) (by positivity) ?_ ?_ ζ ?_ w ?_
      · intro x hx
        have hx' : ‖x - w‖ ≤ ‖w‖ / 8 := by
          have := mem_ball.mp hx
          rw [dist_eq_norm] at this
          linarith [this, norm_nonneg w]
        exact neg_mem_slitPlane_of_mem_QLeft hξ hwQ hwξ hx'
      · intro x hx
        have hxd := mem_ball.mp hx
        rw [dist_eq_norm] at hxd
        have h1 : ‖w‖ - ‖x‖ ≤ ‖x - w‖ := by
          have := norm_sub_norm_le w x
          rwa [norm_sub_rev] at this
        linarith [h1, hxd, norm_nonneg w]
      · rw [mem_ball, dist_eq_norm]; exact hstrict
      · rw [mem_ball, dist_self]; positivity
    -- final estimate
    have h4 : ‖a‖ * (‖ζ - w‖ / (‖w‖ / 2)) < ε / 2 := by
      have h5 : ‖a‖ * (‖ζ - w‖ / (‖w‖ / 2))
          ≤ ‖a‖ * ((‖a‖ * Real.log (2 * ‖w‖) + (‖a‖ * Real.pi + ‖b‖ + ε / 2))
              / (‖w‖ / 2)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hdisp (by positivity))
          (norm_nonneg a)
      refine lt_of_le_of_lt h5 ?_
      have heq : ‖a‖ * ((‖a‖ * Real.log (2 * ‖w‖) + (‖a‖ * Real.pi + ‖b‖ + ε / 2))
              / (‖w‖ / 2))
          = 2 * ‖a‖ * (‖a‖ * Real.log (2 * ‖w‖) + (‖a‖ * Real.pi + ‖b‖ + ε / 2)) / ‖w‖ := by
        field_simp
      rw [heq, div_lt_iff₀ hwpos]
      linarith [hfin1]
    have hsplit : ζ - (w + a * Complex.log (-w) + b)
        = (ζ - w - a * Complex.log (-ζ) - b)
          + a * (Complex.log (-ζ) - Complex.log (-w)) := by
      ring
    rw [hsplit]
    calc ‖(ζ - w - a * Complex.log (-ζ) - b) + a * (Complex.log (-ζ) - Complex.log (-w))‖
        ≤ ‖ζ - w - a * Complex.log (-ζ) - b‖
          + ‖a * (Complex.log (-ζ) - Complex.log (-w))‖ := norm_add_le _ _
      _ = ‖ζ - w - a * Complex.log (-ζ) - b‖
          + ‖a‖ * ‖Complex.log (-ζ) - Complex.log (-w)‖ := by rw [norm_mul]
      _ ≤ ‖ζ - w - a * Complex.log (-ζ) - b‖ + ‖a‖ * (‖ζ - w‖ / (‖w‖ / 2)) := by
            linarith [mul_le_mul_of_nonneg_left hlog (norm_nonneg a)]
      _ < ε := by linarith [hdist, h4]

end

end Work.Parab.inversion
