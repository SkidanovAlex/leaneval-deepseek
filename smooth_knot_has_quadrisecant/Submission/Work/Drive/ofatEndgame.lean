import Mathlib
import Submission.Work.Drive.oFatDefs
import Submission.Work.Drive.crosscut_or_spreadQuad
import Submission.Work.Drive.crosscut_of_close
import Submission.Work.Drive.spreadBookkeepingK_spreadCrux
import Submission.Work.Drive.isUnknotted_of_close

/-!
# The endgame contract of the lead's `OFat` design, and the crux from `E3` + the endgame

The lead's `NOTES_LEAD_OFat.md` splits the crux `Work.Drive.SpreadCrux` into

* `E3` (`Work.Drive.crosscut_or_spreadQuad_of_close`, this lane): every general-position approximant
  either has a uniform `δ`-spread quadrisecant, or carries a bottom–top crosscut of the strip
  avoiding `OFatObstruction r' ρ`; and
* the **endgame** `E1`/`E2`/`E4` (H105/H481): such a crosscut, for a small enough fatness threshold
  `ρ`, forces `r'` to be unknotted (the sweep with the perpendicular chamfer of depth `≥ ρ` removes the
  corner-local middles, its slices stay embedded, and the resulting family of knots joins `r'` to a
  round circle).

This module *names* the endgame (`Work.Drive.OFatCrosscutEndgame`), proves that it is exactly what is
missing (`Work.Drive.spreadCrux_of_endgame`: `E3` + the endgame give the crux), and leaves the
endgame itself as the single pin of the lane.  The clue for the constants is that the endgame needs
`C²`-closeness of the approximant to the reference knot (uniform curvature bound + uniform curvature
lower bound) and a bound `ρ ≤ ρ₀` on the fatness threshold, both *uniform over the ball*.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **A speed bound for a smooth knot.** -/
theorem exists_knot_velocity_bound {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ V : ℝ, 0 < V ∧ ∀ t : ℝ, ‖velocity r t‖ ≤ V := by
  have hcont : Continuous (velocity r) := hr.smooth.continuous_deriv le_top
  obtain ⟨x, -, hmax⟩ := (isCompact_Icc.image hcont).exists_isMaxOn
    (f := fun y : Space => ‖y‖)
    ⟨velocity r 0, 0, ⟨le_rfl, period_pos.le⟩, rfl⟩ continuous_norm.continuousOn
  refine ⟨‖x‖ + 1, by positivity, fun t => ?_⟩
  set k : ℤ := ⌊t / period⌋ with hk
  have hle : ((k : ℝ)) * period ≤ t := by
    have h := Int.floor_le (t / period)
    have h2 := mul_le_mul_of_nonneg_right h period_pos.le
    rw [div_mul_cancel₀ t (ne_of_gt period_pos)] at h2
    exact h2
  have hlt : t < (k : ℝ) * period + period := by
    have h := Int.lt_floor_add_one (t / period)
    have h2 := mul_lt_mul_of_pos_right h period_pos
    rw [div_mul_cancel₀ t (ne_of_gt period_pos), add_mul, one_mul] at h2
    linarith
  have hper : velocity r t = velocity r (t - (k : ℝ) * period) := by
    have hper' : Function.Periodic (velocity r) period := hr.velocity_periodic
    have h := hper'.zsmul k (t - (k : ℝ) * period)
    rw [zsmul_eq_mul] at h
    have h2 : t - (k : ℝ) * period + (k : ℝ) * period = t := by ring
    rw [h2] at h
    exact h
  rw [hper]
  have hmem : velocity r (t - (k : ℝ) * period) ∈ velocity r '' Set.Icc (0 : ℝ) period :=
    ⟨t - (k : ℝ) * period, ⟨by linarith, by linarith⟩, rfl⟩
  have hle' : ‖velocity r (t - (k : ℝ) * period)‖ ≤ ‖x‖ := hmax hmem
  linarith

/-- **The endgame contract of the `OFat` design.**  For a smooth knot `r` there are `ε₂ > 0` and
`ρ₀ > 0` such that every `r'` which is `C²`-`ε₂`-close to `r`, in tangent-chord general position and
inflection-free, and every fatness threshold `ρ ∈ (0, ρ₀]`, satisfies: a bottom–top crosscut of the
period strip avoiding `OFatObstruction r' ρ` forces `r'` to be unknotted. -/
def OFatCrosscutEndgame (r : ℝ → Space) : Prop :=
  IsSmoothKnot r → ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ r' : ℝ → Space, IsSmoothKnot r' → TangentChordGP r' →
      (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) →
      (∀ t : ℝ, ‖r' t - r t‖ < ε₂ ∧ ‖velocity r' t - velocity r t‖ < ε₂ ∧
        ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε₂) →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → StripCrosscutAvoidingOFat r' ρ → IsUnknotted r'

/-- **`E3` + the endgame give the crux.**  The two bodies of the lead's `OFat` design: `E3` produces,
for every approximant in the ball, either a *uniform* `δ`-spread quadrisecant or a crosscut; the
endgame rules the crosscut out (it would make `r'` unknotted, and `r'` is `C¹`-close to the
non-unknotted `r`). -/
theorem spreadCrux_of_endgame
    (hend : ∀ r : ℝ → Space, OFatCrosscutEndgame r) :
    ∀ r : ℝ → Space, SpreadCrux r := by
  intro r hr hnu
  obtain ⟨V, hVpos, hvel⟩ := exists_knot_velocity_bound hr
  obtain ⟨ε₁, hε₁pos, hε₁le, hE3⟩ := crosscut_or_spreadQuad_of_close hr hVpos hvel
  obtain ⟨εu, hεupos, hu⟩ := isUnknotted_of_close hr
  obtain ⟨ε₂, hε₂pos, ρ₀, hρ₀pos, hend'⟩ := hend r hr
  -- the fatness threshold handed to `E3` (small, for the endgame)
  set ρf : ℝ := min ρ₀ 1 with hρf
  have hρfpos : 0 < ρf := lt_min hρ₀pos one_pos
  have hρfρ₀ : ρf ≤ ρ₀ := min_le_left _ _
  -- the uniform spread of `E3` at that threshold
  obtain ⟨δ, hδpos, hE3δ⟩ := hE3 hρfpos
  -- the crux's ball
  set εc : ℝ := min ε₁ (min ε₂ εu) with hεc
  have hεcε₁ : εc ≤ ε₁ := min_le_left _ _
  have hεcε₂ : εc ≤ ε₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεcu : εc ≤ εu := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨δ, hδpos, εc, by positivity, ?_⟩
  intro r' hr' _hgp hinfl _hn5 htc _hfib _hqi hclose
  have hcl₁ : ∀ t : ℝ, ‖r' t - r t‖ < ε₁ ∧ ‖velocity r' t - velocity r t‖ < ε₁ :=
    fun t => ⟨lt_of_lt_of_le (hclose t).1 hεcε₁, lt_of_lt_of_le (hclose t).2.1 hεcε₁⟩
  have hcl₂ : ∀ t : ℝ, ‖r' t - r t‖ < ε₂ ∧ ‖velocity r' t - velocity r t‖ < ε₂ ∧
      ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε₂ :=
    fun t => ⟨lt_of_lt_of_le (hclose t).1 hεcε₂, lt_of_lt_of_le (hclose t).2.1 hεcε₂,
      lt_of_lt_of_le (hclose t).2.2 hεcε₂⟩
  have hcl_u : ∀ t : ℝ, ‖r' t - r t‖ < εu ∧ ‖velocity r' t - velocity r t‖ < εu :=
    fun t => ⟨lt_of_lt_of_le (hclose t).1 hεcu, lt_of_lt_of_le (hclose t).2.1 hεcu⟩
  rcases hE3δ r' hr' htc hinfl hcl₁ with hspread | hcc
  · exact hspread
  · exact absurd (hu r' hr' hcl_u (hend' r' hr' htc hinfl hcl₂ ρf hρfpos hρfρ₀ hcc)) hnu

end Work.Drive
