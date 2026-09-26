import Mathlib
import Submission.Work.Drive.chamferCrossingThin

/-!
# The chamfer–chord thin-crossing lemmas (the `OFat` lane)

The `OFat` lane consumes the chamfered sweep loop of a band arc whose *retained* arc is chord-free but
whose chords may carry *corner-local* middles (within `ρ` of an endpoint).  The injectivity of the
chamfered loop then rests on four separation statements; two of them (the tail/head chamfer meeting
the *chord*) are proved here, by the same first-order mechanism as
`Work.Drive.chamfer_crossing_thin_tilt`:

* if the tail chamfer point `(1 - c) • C + c • r (ta + lam*(tb-ta))` (`C = (1-lam) • r ta + lam • r tb`)
  lies on the chord *line* with `c > 0`, the identity

      c • (r (ta + lam*(tb-ta)) - r ta) = (ξ - (1 - c) * lam) • (r tb - r ta)

  shows that the displacement of the arc over the cut interval `[ta, ta + lam*(tb-ta)]` is parallel to
  the chord; pairing with the tilt `n = chordTilt (r ta) (r tb) (velocity r ta)` (which annihilates
  `r tb - r ta` and satisfies `⟪n, velocity r ta⟫ = ‖n‖ ^ 2`) forces `⟪n, r (ta + lam*(tb-ta)) - r ta⟫ = 0`,
  while the slack estimate `inner_knot_slack_mono` makes that quantity *positive* once the tilt exceeds
  `2 C * lam * (tb - ta)` (`C` a Lipschitz constant of the velocity).  Hence the tilt is at most
  `2 C * lam * (tb - ta)`.

The head case is the mirror, with `n = chordTilt (r ta) (r tb) (velocity r tb)` and the cut interval
`[tb - lam*(tb-ta), tb]`.

Consequently a *uniform* tilt margin `μ` on a window excludes both crossings for `lam` small — which
is exactly the non-tangency (`TCset`-avoidance) supplied by `Work.Drive.StripCrosscutAvoidingOFat`.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **A tail chamfer–chord crossing forces a nearly tangent chord at `ta`.** -/
theorem chamfer_chord_thin_tilt_tail {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ta tb lam c ξ : ℝ),
      0 < lam → 0 < tb - ta → tb - ta < period →
      0 < c → c ≤ 1 → ξ ∈ Set.Icc lam (1 - lam) →
      (1 - c) • ((1 - lam) • r ta + lam • r tb) + c • r (ta + lam * (tb - ta))
        = (1 - ξ) • r ta + ξ • r tb →
      ‖chordTilt (r ta) (r tb) (velocity r ta)‖ ≤ K * lam * (tb - ta) := by
  obtain ⟨m, M, C, hm, hM, hC, hspeed, hspeedM, hlip⟩ := exists_knot_c2_bounds hr
  refine ⟨2 * C, by positivity, ?_⟩
  intro ta tb lam c ξ hlam hw hwper hc0 hc1 hξ hcross
  have hAB : r ta ≠ r tb := knot_ne_of_sub_mem_Ioo hr hw hwper
  set n : Space := chordTilt (r ta) (r tb) (velocity r ta) with hn
  have hnn : inner ℝ n (velocity r ta) = ‖n‖ ^ 2 := by
    rw [hn]; exact inner_chordTilt_self hAB (velocity r ta)
  have hVn : inner ℝ n (r tb - r ta) = 0 := by
    have hsmul : r tb - r ta = ‖r tb - r ta‖ • chordDir (r ta) (r tb) :=
      (chordDir_smul (r ta) (r tb) hAB).symm
    rw [hsmul, inner_smul_right, hn, inner_chordTilt_chordDir hAB]
    ring
  set et : ℝ := lam * (tb - ta) with het
  have het_pos : 0 < et := mul_pos hlam hw
  -- the scalar form of the crossing
  have hscal : c * inner ℝ n (r (ta + et) - r ta) = 0 := by
    have h2 : (1 - c) • (lam • (r tb - r ta)) + c • (r (ta + et) - r ta)
        = ξ • (r tb - r ta) := by
      have h := congrArg (fun z : Space => z - r ta) hcross
      have h3 : ((1 - c) • ((1 - lam) • r ta + lam • r tb) + c • r (ta + et)) - r ta
          = (1 - c) • (lam • (r tb - r ta)) + c • (r (ta + et) - r ta) := by module
      have h4 : ((1 - ξ) • r ta + ξ • r tb) - r ta = ξ • (r tb - r ta) := by module
      rw [h3, h4] at h
      exact h
    rw [smul_smul] at h2
    have h6 : c • (r (ta + et) - r ta)
        = (ξ - (1 - c) * lam) • (r tb - r ta) := by
      rw [sub_smul]
      rw [eq_sub_iff_add_eq]
      rw [add_comm]
      exact h2
    have h7 : inner ℝ n (c • (r (ta + et) - r ta))
        = inner ℝ n ((ξ - (1 - c) * lam) • (r tb - r ta)) := by rw [h6]
    rw [inner_smul_right, inner_smul_right, hVn, mul_zero] at h7
    exact h7
  have hperp : inner ℝ n (r (ta + et) - r ta) = 0 := by
    rcases mul_eq_zero.mp hscal with h1 | h1
    · exact absurd h1 (ne_of_gt hc0)
    · exact h1
  -- the thick case is impossible
  by_contra hcon
  push Not at hcon
  have hthick : 2 * C * et < ‖n‖ := by
    rw [het]; nlinarith [hcon]
  have hnpos : 0 < ‖n‖ := lt_of_le_of_lt (mul_nonneg (by linarith [hC.le]) het_pos.le) hthick
  have harc : ∀ θ ∈ Set.Icc ta (ta + et), ‖n‖ ^ 2 / 2 ≤ inner ℝ n (velocity r θ) := by
    intro θ hθ
    have h1 : inner ℝ n (velocity r θ)
        = inner ℝ n (velocity r ta) + inner ℝ n (velocity r θ - velocity r ta) := by
      rw [inner_sub_right]; ring
    have h2 : ‖velocity r θ - velocity r ta‖ ≤ C * (θ - ta) := by
      have h := hlip θ ta
      have habs : |ta - θ| = θ - ta := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [hθ.1])]
      rwa [habs] at h
    have h3 : -(‖n‖ * (C * (θ - ta))) ≤ inner ℝ n (velocity r θ - velocity r ta) := by
      have h4 : |inner ℝ n (velocity r θ - velocity r ta)|
          ≤ ‖n‖ * ‖velocity r θ - velocity r ta‖ := abs_real_inner_le_norm n _
      have h5 : ‖n‖ * ‖velocity r θ - velocity r ta‖ ≤ ‖n‖ * (C * (θ - ta)) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg n)
      linarith [neg_abs_le (inner ℝ n (velocity r θ - velocity r ta))]
    have h4 : C * (θ - ta) ≤ C * et := by
      nlinarith [hC, hθ.2]
    have h5 : ‖n‖ * (C * (θ - ta)) ≤ ‖n‖ ^ 2 / 2 := by
      nlinarith [hnpos, hC, het_pos, h4, hthick]
    linarith [h1, hnn, h3, h5]
  have hslack := inner_knot_slack_mono hr (n := n) (ν := ‖n‖ ^ 2 / 2)
    (a := ta) (b := ta + et) harc
  have h := hslack ta ⟨le_rfl, by linarith [het_pos]⟩ (ta + et) ⟨by linarith, le_rfl⟩
    (by linarith)
  have h1 : 0 < (‖n‖ ^ 2 / 2) * et := mul_pos (by positivity) het_pos
  rw [add_sub_cancel_left] at h
  linarith [h, h1, hperp]

/-- **A head chamfer–chord crossing forces a nearly tangent chord at `tb`.** -/
theorem chamfer_chord_thin_tilt_head {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ta tb lam c ξ : ℝ),
      0 < lam → 0 < tb - ta → tb - ta < period →
      0 < c → c < 1 → ξ ∈ Set.Icc lam (1 - lam) →
      (1 - c) • r (tb - lam * (tb - ta)) + c • (lam • r ta + (1 - lam) • r tb)
        = (1 - ξ) • r ta + ξ • r tb →
      ‖chordTilt (r ta) (r tb) (velocity r tb)‖ ≤ K * lam * (tb - ta) := by
  obtain ⟨m, M, C, hm, hM, hC, hspeed, hspeedM, hlip⟩ := exists_knot_c2_bounds hr
  refine ⟨2 * C, by positivity, ?_⟩
  intro ta tb lam c ξ hlam hw hwper hc0 hc1 hξ hcross
  have hAB : r ta ≠ r tb := knot_ne_of_sub_mem_Ioo hr hw hwper
  set n : Space := chordTilt (r ta) (r tb) (velocity r tb) with hn
  have hnn : inner ℝ n (velocity r tb) = ‖n‖ ^ 2 := by
    rw [hn]; exact inner_chordTilt_self hAB (velocity r tb)
  have hVn : inner ℝ n (r ta - r tb) = 0 := by
    have hsmul : r tb - r ta = ‖r tb - r ta‖ • chordDir (r ta) (r tb) :=
      (chordDir_smul (r ta) (r tb) hAB).symm
    have h2 : r ta - r tb = -(‖r tb - r ta‖ • chordDir (r ta) (r tb)) := by
      rw [← hsmul]; abel
    rw [h2, inner_neg_right, inner_smul_right, hn, inner_chordTilt_chordDir hAB]
    ring
  set et : ℝ := lam * (tb - ta) with het
  have het_pos : 0 < et := mul_pos hlam hw
  -- the scalar form of the crossing
  have hscal : (1 - c) * inner ℝ n (r (tb - et) - r tb) = 0 := by
    have h2 : (1 - c) • (r (tb - et) - r tb) + c • (lam • (r ta - r tb))
        = (1 - ξ) • (r ta - r tb) := by
      have h := congrArg (fun z : Space => z - r tb) hcross
      have h3 : (1 - c) • r (tb - lam * (tb - ta)) + c • (lam • r ta + (1 - lam) • r tb) - r tb
          = (1 - c) • (r (tb - et) - r tb) + c • (lam • (r ta - r tb)) := by module
      have h4 : (1 - ξ) • r ta + ξ • r tb - r tb = (1 - ξ) • (r ta - r tb) := by module
      rw [h3, h4] at h
      exact h
    rw [smul_smul] at h2
    have h6 : (1 - c) • (r (tb - et) - r tb)
        = ((1 - ξ) - c * lam) • (r ta - r tb) := by
      conv_rhs => rw [sub_smul]
      rw [eq_sub_iff_add_eq]
      exact h2
    have h7 : inner ℝ n ((1 - c) • (r (tb - et) - r tb))
        = inner ℝ n (((1 - ξ) - c * lam) • (r ta - r tb)) := by rw [h6]
    rw [inner_smul_right, inner_smul_right, hVn, mul_zero] at h7
    exact h7
  have hperp : inner ℝ n (r (tb - et) - r tb) = 0 := by
    rcases mul_eq_zero.mp hscal with h1 | h1
    · exact absurd h1 (by linarith)
    · exact h1
  by_contra hcon
  push Not at hcon
  have hthick : 2 * C * et < ‖n‖ := by
    rw [het]; nlinarith [hcon]
  have hnpos : 0 < ‖n‖ := lt_of_le_of_lt (mul_nonneg (by linarith [hC.le]) het_pos.le) hthick
  have harc : ∀ θ ∈ Set.Icc (tb - et) tb, ‖n‖ ^ 2 / 2 ≤ inner ℝ n (velocity r θ) := by
    intro θ hθ
    have h1 : inner ℝ n (velocity r θ)
        = inner ℝ n (velocity r tb) + inner ℝ n (velocity r θ - velocity r tb) := by
      rw [inner_sub_right]; ring
    have h2 : ‖velocity r θ - velocity r tb‖ ≤ C * (tb - θ) := by
      have h := hlip θ tb
      rw [abs_of_nonneg (by linarith [hθ.2])] at h
      exact h
    have h3 : -(‖n‖ * (C * (tb - θ))) ≤ inner ℝ n (velocity r θ - velocity r tb) := by
      have h4 : |inner ℝ n (velocity r θ - velocity r tb)|
          ≤ ‖n‖ * ‖velocity r θ - velocity r tb‖ := abs_real_inner_le_norm n _
      have h5 : ‖n‖ * ‖velocity r θ - velocity r tb‖ ≤ ‖n‖ * (C * (tb - θ)) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg n)
      linarith [neg_abs_le (inner ℝ n (velocity r θ - velocity r tb))]
    have h4 : C * (tb - θ) ≤ C * et := by
      nlinarith [hC, hθ.1]
    have h5 : ‖n‖ * (C * (tb - θ)) ≤ ‖n‖ ^ 2 / 2 := by
      nlinarith [hnpos, hC, het_pos, h4, hthick]
    linarith [h1, hnn, h3, h5]
  have hslack := inner_knot_slack_mono hr (n := n) (ν := ‖n‖ ^ 2 / 2)
    (a := tb - et) (b := tb) harc
  have h := hslack (tb - et) ⟨by linarith, by linarith [het_pos]⟩ tb ⟨by linarith [het_pos], le_rfl⟩
    (by linarith)
  have h1 : 0 < (‖n‖ ^ 2 / 2) * et := mul_pos (by positivity) het_pos
  have h2 : tb - (tb - et) = et := by ring
  rw [h2] at h
  -- h : (‖n‖^2/2) * et ≤ ⟪n, r tb - r (tb-et)⟫ ; and hperp : ⟪n, r (tb-et) - r tb⟫ = 0
  have h3 : inner ℝ n (r tb - r (tb - et)) = -inner ℝ n (r (tb - et) - r tb) := by
    rw [← inner_neg_right]
    congr 1
    abel
  rw [h3, hperp, neg_zero] at h
  linarith [h, h1]

/-! ## The no-crossing corollaries (a uniform tilt margin excludes both crossings) -/

/-- **A uniform tilt margin at `ta` excludes the tail chamfer–chord crossing.** -/
theorem no_chamfer_chord_crossing_tail {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ K : ℝ, 0 < K ∧ ∀ (μ C₀ : ℝ), 0 < μ → 0 < C₀ →
      ∀ (ta tb lam c ξ : ℝ),
        0 < lam → lam * (K * C₀) < μ →
        0 < tb - ta → tb - ta < period → tb - ta ≤ C₀ →
        μ ≤ ‖chordTilt (r ta) (r tb) (velocity r ta)‖ →
        0 < c → c ≤ 1 → ξ ∈ Set.Icc lam (1 - lam) →
        (1 - c) • ((1 - lam) • r ta + lam • r tb) + c • r (ta + lam * (tb - ta))
          = (1 - ξ) • r ta + ξ • r tb → False := by
  obtain ⟨K, hK, hmain⟩ := chamfer_chord_thin_tilt_tail hr
  refine ⟨K, hK, ?_⟩
  intro μ C₀ hμ hC₀ ta tb lam c ξ hlam hlamμ hw hwper hwC₀ hμtilt hc0 hc1 hξ hcross
  have hthin := hmain ta tb lam c ξ hlam hw hwper hc0 hc1 hξ hcross
  have h1 : lam * (K * C₀) = K * lam * C₀ := by ring
  rw [h1] at hlamμ
  nlinarith [hthin, hμtilt, hμ, hC₀, hlam, hK, hlamμ, hw, hwC₀, hwper]

/-- **A uniform tilt margin at `tb` excludes the head chamfer–chord crossing.** -/
theorem no_chamfer_chord_crossing_head {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ K : ℝ, 0 < K ∧ ∀ (μ C₀ : ℝ), 0 < μ → 0 < C₀ →
      ∀ (ta tb lam c ξ : ℝ),
        0 < lam → lam * (K * C₀) < μ →
        0 < tb - ta → tb - ta < period → tb - ta ≤ C₀ →
        μ ≤ ‖chordTilt (r ta) (r tb) (velocity r tb)‖ →
        0 < c → c < 1 → ξ ∈ Set.Icc lam (1 - lam) →
        (1 - c) • r (tb - lam * (tb - ta)) + c • (lam • r ta + (1 - lam) • r tb)
          = (1 - ξ) • r ta + ξ • r tb → False := by
  obtain ⟨K, hK, hmain⟩ := chamfer_chord_thin_tilt_head hr
  refine ⟨K, hK, ?_⟩
  intro μ C₀ hμ hC₀ ta tb lam c ξ hlam hlamμ hw hwper hwC₀ hμtilt hc0 hc1 hξ hcross
  have hthin := hmain ta tb lam c ξ hlam hw hwper hc0 hc1 hξ hcross
  have h1 : lam * (K * C₀) = K * lam * C₀ := by ring
  rw [h1] at hlamμ
  nlinarith [hthin, hμtilt, hμ, hC₀, hlam, hK, hlamμ, hw, hwC₀, hwper]

end Work.Drive
