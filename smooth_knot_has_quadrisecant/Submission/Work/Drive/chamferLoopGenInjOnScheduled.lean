import Mathlib
import Submission.Work.Drive.chamferSchedule
import Submission.Work.Drive.chamferLoopGenInjOnBall
import Submission.Work.Drive.chamferLoopGenInjOnNt

namespace Work.Drive

set_option maxHeartbeats 1000000

open LeanEval.KnotTheory.Quadrisecant

/-! ## Helpers for the scheduled-slices bookkeeping (`NOTES_H47_thinE1_connectors.md` §12.2) -/

lemma circSep_comm' (x y : ℝ) : circSep x y = circSep y x := by
  simp [circSep, dist_comm]

/-- **The radial gap at the two cut points**, in the form in which the scheduled depth is consumed:
the window hypothesis is the *weaker* `b - a ≤ period - ρ₀` (rather than `period - 2ρ₀`), which is
what the schedule's depth satisfies in the wrap-around zone.  Copy of
`Work.Drive.radialGapOfTools` with that weakening. -/
lemma radialGapOfTools' {r : ℝ → Space} {ρ₀ δ : ℝ} (hρ : 0 < ρ₀) (h2δ : 2 * ρ₀ ≤ δ)
    (hmono : ∀ a s s' : ℝ, 0 ≤ s → s < s' → s' ≤ δ → ‖r (a + s) - r a‖ < ‖r (a + s') - r a‖)
    (hmonob : ∀ a s s' : ℝ, 0 ≤ s → s < s' → s' ≤ δ → ‖r (a - s) - r a‖ < ‖r (a - s') - r a‖)
    (hgap : ∀ x s : ℝ, 2 * ρ₀ ≤ circSep s x → ‖r (x + ρ₀) - r x‖ < ‖r s - r x‖)
    (hgapb : ∀ x s : ℝ, 2 * ρ₀ ≤ circSep s x → ‖r (x - ρ₀) - r x‖ < ‖r s - r x‖) :
    ∀ a b : ℝ, 0 < b - a → b - a ≤ period - ρ₀ →
      (∀ θ : ℝ, a + ρ₀ ≤ θ → θ ≤ b - ρ₀ → θ ≠ a + ρ₀ → ‖r (a + ρ₀) - r a‖ < ‖r θ - r a‖) ∧
      (∀ θ : ℝ, a + ρ₀ ≤ θ → θ ≤ b - ρ₀ → θ ≠ b - ρ₀ → ‖r (b - ρ₀) - r b‖ < ‖r θ - r b‖) := by
  intro a b hab hbL
  constructor
  · intro θ h1 h2 hne
    have hu_gt : ρ₀ < θ - a := by
      have hlt : a + ρ₀ < θ := lt_of_le_of_ne h1 (Ne.symm hne)
      linarith
    have hub : θ - a ≤ period - 2 * ρ₀ := by linarith
    rcases le_or_gt (θ - a) δ with hle | hgt
    · have hmon := hmono a ρ₀ (θ - a) hρ.le hu_gt hle
      have heq : a + (θ - a) = θ := by ring
      rwa [heq] at hmon
    · have h2ρ : 2 * ρ₀ < θ - a := lt_of_le_of_lt h2δ hgt
      have hsep : 2 * ρ₀ ≤ circSep θ a :=
        circSep_ge_of_sub_mem (x := a) (u := θ) (ρ := 2 * ρ₀) (by linarith) (by linarith) hub
      exact hgap a θ hsep
  · intro θ h1 h2 hne
    have hv_gt : ρ₀ < b - θ := by
      have hlt : θ < b - ρ₀ := lt_of_le_of_ne h2 hne
      linarith
    have hvb : b - θ ≤ period - 2 * ρ₀ := by linarith
    rcases le_or_gt (b - θ) δ with hle | hgt
    · have hmon := hmonob b ρ₀ (b - θ) hρ.le hv_gt hle
      have heq : b - (b - θ) = θ := by ring
      rwa [heq] at hmon
    · have h2ρ : 2 * ρ₀ < b - θ := lt_of_le_of_lt h2δ hgt
      have hsep : 2 * ρ₀ ≤ circSep b θ :=
        circSep_ge_of_sub_mem (x := θ) (u := b) (ρ := 2 * ρ₀) (by linarith) (by linarith) hvb
      exact hgapb b θ (by rw [circSep_comm' θ b]; exact hsep)

/-- `schedPhi x = 2x - 1` on `[1/2, 1]`. -/
lemma schedPhi_eq_two_mul_sub_one {x : ℝ} (h1 : 1 / 2 < x) (h2 : x ≤ 1) :
    schedPhi x = 2 * x - 1 := by
  have h3 : 0 ≤ 2 * x - 1 := by linarith
  have h4 : 2 * x - 1 ≤ 1 := by linarith
  rw [schedPhi, max_eq_right h3, min_eq_right h4]

/-- The width plus half the circular chord length is at most a period. -/
lemma sweepW_add_half_schedC_le {d : BandArcData} (D : SweepData d) {σ : ℝ}
    (hW : sweepW' D σ ≤ period) :
    sweepW' D σ + schedC D σ / 2 ≤ period := by
  rcases le_total (sweepW' D σ) (period - sweepW' D σ) with h | h
  · have hc : schedC D σ = sweepW' D σ := min_eq_left h
    rw [hc]
    linarith [period_pos]
  · have hc : schedC D σ = period - sweepW' D σ := min_eq_right h
    rw [hc]
    linarith

/-- **The cut depth of the schedule is less than half the circular chord length**, in the zone
where the ramp is active.  This is the quantitative heart of the `α < 1/2` clause of Lemma A
(`2ρ < δs` and `c ≤ δs` are what make it work; no relation between `ρ` and `δs/4` is needed). -/
lemma two_mul_schedDep_lt_schedC {d : BandArcData} (D : SweepData d) {lay ρ δs : ℝ}
    (hρ : 0 < ρ) (hδs : 0 < δs) (hρδs : 2 * ρ < δs) {σ : ℝ}
    (hcpos : 0 < schedC D σ)
    (hphi : 0 < schedPhi (schedC D σ / δs))
    (hdep : schedDep lay ρ δs D σ = ρ * schedPhi (schedC D σ / δs)) :
    2 * schedDep lay ρ δs D σ < schedC D σ := by
  have hcgt : δs / 2 < schedC D σ := by
    by_contra hc
    rw [not_lt] at hc
    have h0 : schedPhi (schedC D σ / δs) = 0 := by
      rw [schedPhi_eq_zero_iff, div_le_iff₀ hδs]; linarith
    rw [h0] at hphi; exact lt_irrefl 0 hphi
  rcases lt_or_ge (schedC D σ) δs with hcδ | hcδ
  · have hφeq : schedPhi (schedC D σ / δs) = 2 * (schedC D σ / δs) - 1 :=
      schedPhi_eq_two_mul_sub_one (by rw [lt_div_iff₀ hδs]; linarith)
        (by rw [div_le_one hδs]; exact hcδ.le)
    rw [hdep, hφeq]
    have hident : 2 * (ρ * (2 * (schedC D σ / δs) - 1))
        = (4 * ρ * schedC D σ - 2 * ρ * δs) / δs := by
      field_simp
      ring
    rw [hident, div_lt_iff₀ hδs]
    rcases lt_or_ge (4 * ρ) δs with h4 | h4
    · nlinarith [hcδ.le, hcpos, hρ, hδs]
    · nlinarith [hcδ.le, hρδs, hδs, hρ, h4]
  · have hφ1 : schedPhi (schedC D σ / δs) = 1 := by
      rw [schedPhi_eq_one_iff, le_div_iff₀ hδs]; linarith
    rw [hdep, hφ1, mul_one]
    linarith

/-- **The chord from `x` to `x + dep` is at least `cQ * dep` long**, for the depth schedule's
`dep ≤ ρ`: either the depth is inside the local window (where the speed floor `m` applies) or the
radial monotonicity pushes the distance up by the local scale. -/
lemma cQ_mul_le_norm_add {r : ℝ → Space} {cQ m δloc ρ μ dep : ℝ} (hm : 0 < m)
    (hδloc : 0 < δloc) (hρ : 0 < ρ) (hdep0 : 0 < dep) (hdepρ : dep ≤ ρ) (hdepμ : dep ≤ μ)
    (hcQm : cQ ≤ m / 2) (hcQmd : cQ ≤ m * δloc / (2 * ρ))
    (hnear : ∀ s t' : ℝ, |s - t'| ≤ δloc → (m / 2) * |s - t'| ≤ ‖r s - r t'‖)
    (hmono : ∀ a x y : ℝ, 0 ≤ x → x < y → y ≤ μ → ‖r (a + x) - r a‖ < ‖r (a + y) - r a‖)
    (x : ℝ) : cQ * dep ≤ ‖r (x + dep) - r x‖ := by
  have h4 : cQ * dep ≤ m * δloc / 2 := by
    have h5 : cQ * dep ≤ (m * δloc / (2 * ρ)) * dep := mul_le_mul_of_nonneg_right hcQmd hdep0.le
    have h6 : (m * δloc / (2 * ρ)) * dep ≤ m * δloc / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have h7 : (0 : ℝ) ≤ m * δloc * 2 := by positivity
      have h8 := mul_le_mul_of_nonneg_left hdepρ h7
      linarith [h8]
    linarith
  rcases lt_or_ge dep δloc with h | h
  · have h1 := hnear (x + dep) x
      (by rw [show x + dep - x = dep by ring, abs_of_pos hdep0]; exact le_of_lt h)
    rw [show x + dep - x = dep by ring, abs_of_pos hdep0] at h1
    nlinarith [h1, hcQm, hdep0.le]
  · have h2 := hnear (x + δloc) x
      (by rw [show x + δloc - x = δloc by ring, abs_of_pos hδloc])
    rw [show x + δloc - x = δloc by ring, abs_of_pos hδloc] at h2
    rcases eq_or_lt_of_le h with heq | hlt
    · rw [heq] at h2 h4
      linarith
    · have h3 := hmono x δloc dep hδloc.le hlt hdepμ
      linarith

/-- **The chord from `x - dep` to `x` is at least `cQ * dep` long** (the mirror of
`cQ_mul_le_norm_add`). -/
lemma cQ_mul_le_norm_sub {r : ℝ → Space} {cQ m δloc ρ μ dep : ℝ} (hm : 0 < m)
    (hδloc : 0 < δloc) (hρ : 0 < ρ) (hdep0 : 0 < dep) (hdepρ : dep ≤ ρ) (hdepμ : dep ≤ μ)
    (hcQm : cQ ≤ m / 2) (hcQmd : cQ ≤ m * δloc / (2 * ρ))
    (hnear : ∀ s t' : ℝ, |s - t'| ≤ δloc → (m / 2) * |s - t'| ≤ ‖r s - r t'‖)
    (hmonob : ∀ a x y : ℝ, 0 ≤ x → x < y → y ≤ μ → ‖r (a - x) - r a‖ < ‖r (a - y) - r a‖)
    (x : ℝ) : cQ * dep ≤ ‖r (x - dep) - r x‖ := by
  have h4 : cQ * dep ≤ m * δloc / 2 := by
    have h5 : cQ * dep ≤ (m * δloc / (2 * ρ)) * dep := mul_le_mul_of_nonneg_right hcQmd hdep0.le
    have h6 : (m * δloc / (2 * ρ)) * dep ≤ m * δloc / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have h7 : (0 : ℝ) ≤ m * δloc * 2 := by positivity
      have h8 := mul_le_mul_of_nonneg_left hdepρ h7
      linarith [h8]
    linarith
  rcases lt_or_ge dep δloc with h | h
  · have h1 := hnear (x - dep) x
      (by rw [show x - dep - x = -dep by ring, abs_neg, abs_of_pos hdep0]; exact le_of_lt h)
    rw [show x - dep - x = -dep by ring, abs_neg, abs_of_pos hdep0] at h1
    nlinarith [h1, hcQm, hdep0.le]
  · have h2 := hnear (x - δloc) x
      (by rw [show x - δloc - x = -δloc by ring, abs_neg, abs_of_pos hδloc])
    rw [show x - δloc - x = -δloc by ring, abs_neg, abs_of_pos hδloc] at h2
    rcases eq_or_lt_of_le h with heq | hlt
    · rw [heq] at h2 h4
      linarith
    · have h3 := hmonob x δloc dep hδloc.le hlt hdepμ
      linarith

theorem chamferLoopGenInjOnScheduled {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {ρ μ s δs M : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (hρμ : 2 * ρ ≤ μ) (hs : 0 < s) (hM : 0 < M)
    (hMv : ∀ t : ℝ, ‖LeanEval.KnotTheory.Quadrisecant.velocity r t‖ ≤ M)
    (hρs : 2 * M * ρ < s) (hδs : 0 < δs) (hρδs : 2 * ρ < δs)
    (hmono : ∀ a x y : ℝ, 0 ≤ x → x < y → y ≤ μ → ‖r (a + x) - r a‖ < ‖r (a + y) - r a‖)
    (hmonob : ∀ a x y : ℝ, 0 ≤ x → x < y → y ≤ μ → ‖r (a - x) - r a‖ < ‖r (a - y) - r a‖)
    (hgap : ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ μ → ∀ x y : ℝ, 2 * ρ' ≤ Work.Drive.circSep y x →
      ‖r (x + ρ') - r x‖ < ‖r y - r x‖)
    (hgapb : ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ μ → ∀ x y : ℝ, 2 * ρ' ≤ Work.Drive.circSep y x →
      ‖r (x - ρ') - r x‖ < ‖r y - r x‖)
    (hsep : ∀ a b : LeanEval.KnotTheory.Quadrisecant.KnotParam, ρ ≤ dist a b →
      s ≤ ‖LeanEval.KnotTheory.Quadrisecant.knotMap r a -
        LeanEval.KnotTheory.Quadrisecant.knotMap r b‖)
    (hfatmid : ∀ σ : ℝ, σ ∈ Set.Ioo (0 : ℝ) 1 → ∀ u : ℝ,
      Work.Drive.taR D σ + ρ ≤ u → u ≤ Work.Drive.tbR D σ - ρ →
        r u ∉ openSegment ℝ (r (Work.Drive.taR D σ)) (r (Work.Drive.tbR D σ)))
    (hshortmid : ∀ σ : ℝ, σ ∈ Set.Ioo (0 : ℝ) 1 → Work.Drive.schedC D σ ≤ δs → ∀ u : ℝ,
      Work.Drive.taR D σ ≤ u → u ≤ Work.Drive.tbR D σ →
        r u ∉ openSegment ℝ (r (Work.Drive.taR D σ)) (r (Work.Drive.tbR D σ)))
    (hV : ∀ σ : ℝ, σ ∈ Set.Ioo (0 : ℝ) 1 →
      r (Work.Drive.taR D σ) ≠ r (Work.Drive.tbR D σ))
    (hntA : ∀ σ : ℝ, σ ∈ Set.Ioo (0 : ℝ) 1 → ∀ m : ℝ,
      r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ) ≠
        m • LeanEval.KnotTheory.Quadrisecant.velocity r (Work.Drive.taR D σ))
    (hntB : ∀ σ : ℝ, σ ∈ Set.Ioo (0 : ℝ) 1 → ∀ m : ℝ,
      r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ) ≠
        m • LeanEval.KnotTheory.Quadrisecant.velocity r (Work.Drive.tbR D σ))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ lay ρ₀ cQ : ℝ, 0 < lay ∧ lay ≤ 1 / 4 ∧ 0 < ρ₀ ∧ 0 < cQ ∧ cQ ≤ 1 ∧
      ∀ σ ∈ Set.Icc a b,
        Set.InjOn (Work.Drive.chamferLoopGen r D lay
          (Work.Drive.schedAlpha lay ρ₀ δs D) (Work.Drive.schedBeta r lay ρ₀ δs cQ D) σ)
          (Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period) := by
  classical
  have hper : 0 < period := period_pos
  have hσIoo : ∀ σ ∈ Set.Icc a b, σ ∈ Set.Ioo (0 : ℝ) 1 := fun σ hσ =>
    ⟨lt_of_lt_of_le ha hσ.1, lt_of_le_of_lt hσ.2 hb⟩
  -- ## 1. uniform geometric bounds for `r`
  obtain ⟨m, δloc, σsep, hm, hδloc, hδlochalf, hσseppos, hbounds⟩ :=
    uniformBoundsC1 (F := fun t (_s : ℝ) => r t)
      ((hr.smooth.comp contDiff_fst).of_le le_top)
      (fun s _ => isCInfKnot_of_isSmoothKnot hr)
  have hb0 := hbounds 0 ⟨le_rfl, zero_le_one⟩
  have hvel : ∀ t : ℝ, m ≤ ‖velocity r t‖ := fun t => hb0.1 t
  have hnear : ∀ s t' : ℝ, |s - t'| ≤ δloc → (m / 2) * |s - t'| ≤ ‖r s - r t'‖ := by
    intro s t' h
    have h1 := hb0.2.1 s t' (by rwa [abs_sub_comm])
    rwa [abs_sub_comm] at h1
  have hlip : ∀ s t' : ℝ, ‖r s - r t'‖ ≤ M * |s - t'| := by
    intro s t'
    have h := norm_sub_le_of_velocity_bound hr.smooth hMv s t'
    rwa [norm_sub_rev, abs_sub_comm] at h
  -- ## 2. the constants `cQ`, `κ₁`, `LB`, `lay`
  set cQ : ℝ := min (min 1 (m / 2)) (min (m * δloc / (2 * ρ)) (s / (2 * ρ))) with hcQdef
  have hcQ0 : 0 < cQ := by
    rw [hcQdef]
    exact lt_min (lt_min one_pos (by linarith)) (lt_min (by positivity) (by positivity))
  have hcQ1 : cQ ≤ 1 := by
    rw [hcQdef]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hcQm : cQ ≤ m / 2 := by
    rw [hcQdef]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hcQmd : cQ ≤ m * δloc / (2 * ρ) := by
    rw [hcQdef]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  set κ₁ : ℝ := min 1 (cQ / M) with hκ₁def
  have hκ₁0 : 0 < κ₁ := by
    rw [hκ₁def]
    exact lt_min one_pos (div_pos hcQ0 hM)
  have hκ₁1 : κ₁ ≤ 1 := by rw [hκ₁def]; exact min_le_left _ _
  obtain ⟨LB, hLB0, hLB4, hBLem⟩ := chamferLoopGenInjOnNt hr D ha hab hb
    (fun σ hσ => hV σ (hσIoo σ hσ))
    (fun σ hσ => hntA σ (hσIoo σ hσ))
    (fun σ hσ => hntB σ (hσIoo σ hσ))
    (κ₁ := κ₁) (κ₂ := 1) hκ₁0 hκ₁1
  set lay : ℝ := min LB (1 / 4) with hlaydef
  have hlay0 : 0 < lay := by rw [hlaydef]; exact lt_min hLB0 (by norm_num)
  have hlay4 : lay ≤ 1 / 4 := by rw [hlaydef]; exact min_le_right _ _
  have hlayLB : lay ≤ LB := by rw [hlaydef]; exact min_le_left _ _
  have hl2 : (1 : ℝ) * lay < 1 / 2 := by linarith
  refine ⟨lay, ρ, cQ, hlay0, hlay4, hρ, hcQ0, hcQ1, ?_⟩
  intro σ hσ
  have hσI := hσIoo σ hσ
  have hW := clg_sweepW_pos_lt D hσI
  have hWdef : sweepW' D σ = tbR D σ - taR D σ := rfl
  have hLpos : 0 < ‖r (tbR D σ) - r (taR D σ)‖ := by
    refine norm_pos_iff.mpr ?_
    intro h0
    exact hV σ hσI (sub_eq_zero.mp h0).symm
  have hψ0 : 0 ≤ schedPsi D δs σ := schedPhi_nonneg _
  have hψ1 : schedPsi D δs σ ≤ 1 := schedPhi_le_one _
  have hβle : schedBeta r lay ρ δs cQ D σ ≤ lay := by
    rw [schedBeta]
    have h1 : min lay (cQ * schedDep lay ρ δs D σ / ‖r (tbR D σ) - r (taR D σ)‖) ≤ lay :=
      min_le_left _ _
    nlinarith [hψ0, hψ1, h1]
  by_cases hcase : ρ * schedPhi (schedC D σ / δs) ≤ lay * sweepW' D σ
  · -- ======================= case B: the depth is `lay * W` =======================
    have hdep : schedDep lay ρ δs D σ = lay * sweepW' D σ := max_eq_left hcase
    have hαeq : schedAlpha lay ρ δs D σ = lay := by
      rw [schedAlpha, hdep, mul_div_cancel_right₀ lay (ne_of_gt hW.1)]
    have hβge : κ₁ * lay ≤ schedBeta r lay ρ δs cQ D σ := by
      rw [schedBeta, hdep]
      set ψ := schedPsi D δs σ with hψdef
      set X := cQ * (lay * sweepW' D σ) / ‖r (tbR D σ) - r (taR D σ)‖ with hXdef
      have hX : cQ / M * lay ≤ X := by
        have hLle : ‖r (tbR D σ) - r (taR D σ)‖ ≤ M * sweepW' D σ := by
          have h := hlip (tbR D σ) (taR D σ)
          rw [← hWdef, abs_of_pos hW.1] at h
          exact h
        rw [hXdef]
        rw [show cQ / M * lay = cQ * lay / M by ring,
          show cQ * (lay * sweepW' D σ) / ‖r (tbR D σ) - r (taR D σ)‖
            = cQ * lay * sweepW' D σ / ‖r (tbR D σ) - r (taR D σ)‖ by ring]
        rw [div_le_div_iff₀ hM hLpos]
        nlinarith [hLle, mul_nonneg hcQ0.le hlay0.le, hM.le, hW.1.le]
      have hmin : κ₁ * lay ≤ min lay X := by
        have h1 := min_le_min (le_refl lay) hX
        have h2 : min lay ((cQ / M) * lay) = κ₁ * lay := by
          rw [hκ₁def, min_mul_of_nonneg (1 : ℝ) (cQ / M) hlay0.le, one_mul]
        rw [← h2]
        exact h1
      have hstep1 : ψ * (κ₁ * lay) ≤ ψ * min lay X := mul_le_mul_of_nonneg_left hmin hψ0
      have hstep2 : κ₁ * lay ≤ (1 - ψ) * lay + ψ * (κ₁ * lay) := by
        have hA : 0 ≤ 1 - ψ := by linarith
        have hB : 0 ≤ 1 - κ₁ := by linarith
        have hC : 0 ≤ (1 - ψ) * (1 - κ₁) * lay := mul_nonneg (mul_nonneg hA hB) hlay0.le
        nlinarith [hC]
      linarith [hstep1, hstep2]
    have hmid : ∀ u : ℝ, taR D σ + lay * sweepW' D σ ≤ u →
        u ≤ tbR D σ - lay * sweepW' D σ →
          r u ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) := by
      intro u hu1 hu2
      by_cases hcδ : schedC D σ ≤ δs
      · exact hshortmid σ hσI hcδ u (by nlinarith [mul_pos hlay0 hW.1])
          (by nlinarith [mul_pos hlay0 hW.1])
      · have hφ1 : schedPhi (schedC D σ / δs) = 1 := by
          rw [schedPhi_eq_one_iff, le_div_iff₀ hδs]; linarith
        have hρle : ρ ≤ lay * sweepW' D σ := by
          have h := hcase
          rw [hφ1, mul_one] at h
          exact h
        exact hfatmid σ hσI u (by linarith) (by linarith)
    refine hBLem lay hlay0 hlayLB hl2 (schedAlpha lay ρ δs D) (schedBeta r lay ρ δs cQ D)
      σ hσ hαeq hβge (by linarith [hβle]) hmid
  · -- ======================= case A: the depth is `ρ * φ(c/δs)` =======================
    have hlt : lay * sweepW' D σ < ρ * schedPhi (schedC D σ / δs) := lt_of_not_ge hcase
    have hdep : schedDep lay ρ δs D σ = ρ * schedPhi (schedC D σ / δs) :=
      max_eq_right (le_of_lt hlt)
    have hφpos : 0 < schedPhi (schedC D σ / δs) := by
      by_contra h
      rw [not_lt] at h
      have h0 : schedPhi (schedC D σ / δs) = 0 := le_antisymm h (schedPhi_nonneg _)
      rw [h0, mul_zero] at hlt
      linarith [mul_pos hlay0 hW.1]
    have hdeppos : 0 < schedDep lay ρ δs D σ := by rw [hdep]; positivity
    have hdeple : schedDep lay ρ δs D σ ≤ ρ := by
      rw [hdep]
      exact mul_le_of_le_one_right hρ.le (schedPhi_le_one _)
    have hdepμ : schedDep lay ρ δs D σ ≤ μ := by linarith
    have hcgt : δs / 2 < schedC D σ := by
      by_contra hc
      rw [not_lt] at hc
      have h0 : schedPhi (schedC D σ / δs) = 0 := by
        rw [schedPhi_eq_zero_iff, div_le_iff₀ hδs]; linarith
      rw [h0] at hφpos; exact lt_irrefl 0 hφpos
    have hcpos : 0 < schedC D σ := lt_trans (by linarith : (0 : ℝ) < δs / 2) hcgt
    have h2depc : 2 * schedDep lay ρ δs D σ < schedC D σ :=
      two_mul_schedDep_lt_schedC D hρ hδs hρδs hcpos hφpos hdep
    have h2depW : 2 * schedDep lay ρ δs D σ < sweepW' D σ :=
      lt_of_lt_of_le h2depc (min_le_left _ _)
    have hαW : schedAlpha lay ρ δs D σ * sweepW' D σ = schedDep lay ρ δs D σ := by
      rw [schedAlpha, div_mul_cancel₀ _ (ne_of_gt hW.1)]
    have hcoef : (1 - schedAlpha lay ρ δs D σ) * sweepW' D σ
        = sweepW' D σ - schedDep lay ρ δs D σ := by
      have h4 : (1 - schedAlpha lay ρ δs D σ) * sweepW' D σ
          = sweepW' D σ - schedAlpha lay ρ δs D σ * sweepW' D σ := by ring
      rw [h4, hαW]
    have harcA : sweepArc' r D σ (schedAlpha lay ρ δs D σ)
        = r (taR D σ + schedDep lay ρ δs D σ) := by
      show r (taR D σ + schedAlpha lay ρ δs D σ * sweepW' D σ)
        = r (taR D σ + schedDep lay ρ δs D σ)
      rw [hαW]
    have harcB : sweepArc' r D σ (1 - schedAlpha lay ρ δs D σ)
        = r (tbR D σ - schedDep lay ρ δs D σ) := by
      show r (taR D σ + (1 - schedAlpha lay ρ δs D σ) * sweepW' D σ)
        = r (tbR D σ - schedDep lay ρ δs D σ)
      rw [hcoef]
      congr 1
      linarith [hWdef]
    have hW_le : sweepW' D σ ≤ period - schedDep lay ρ δs D σ := by
      have hhalf : sweepW' D σ + schedC D σ / 2 ≤ period :=
        sweepW_add_half_schedC_le D hW.2.le
      have h2 : schedDep lay ρ δs D σ < schedC D σ / 2 := by linarith
      linarith
    -- the radial gaps at the two cut points
    have hrg := radialGapOfTools' (r := r) hdeppos (by linarith : 2 * schedDep lay ρ δs D σ ≤ μ)
      hmono hmonob
      (fun x y hy => hgap (schedDep lay ρ δs D σ) hdeppos hdepμ x y hy)
      (fun x y hy => hgapb (schedDep lay ρ δs D σ) hdeppos hdepμ x y hy)
      (taR D σ) (tbR D σ) hW.1 hW_le
    have hgapA : ∀ θ : ℝ, taR D σ + schedAlpha lay ρ δs D σ * sweepW' D σ < θ →
        θ ≤ tbR D σ - schedAlpha lay ρ δs D σ * sweepW' D σ →
          ‖sweepArc' r D σ (schedAlpha lay ρ δs D σ) - r (taR D σ)‖
            < ‖r θ - r (taR D σ)‖ := by
      intro θ h1 h2
      rw [hαW] at h1 h2
      rw [harcA]
      exact hrg.1 θ (le_of_lt h1) h2 (ne_of_gt h1)
    have hgapB : ∀ θ : ℝ, taR D σ + schedAlpha lay ρ δs D σ * sweepW' D σ ≤ θ →
        θ < tbR D σ - schedAlpha lay ρ δs D σ * sweepW' D σ →
          ‖sweepArc' r D σ (1 - schedAlpha lay ρ δs D σ) - r (tbR D σ)‖
            < ‖r θ - r (tbR D σ)‖ := by
      intro θ h1 h2
      rw [hαW] at h1 h2
      rw [harcB]
      exact hrg.2 θ h1 (le_of_lt h2) (ne_of_lt h2)
    -- the two ball bounds
    have hψ1' : schedPsi D δs σ = 1 := by
      rw [schedPsi, schedPhi_eq_one_iff, le_div_iff₀ hδs]; linarith
    have hβcs : schedBeta r lay ρ δs cQ D σ
        ≤ cQ * schedDep lay ρ δs D σ / ‖r (tbR D σ) - r (taR D σ)‖ := by
      rw [schedBeta, hψ1']
      simp only [sub_self, zero_mul, zero_add, one_mul]
      exact min_le_right _ _
    have hβLcQ : schedBeta r lay ρ δs cQ D σ * ‖r (tbR D σ) - r (taR D σ)‖
        ≤ cQ * schedDep lay ρ δs D σ := by
      have h := mul_le_mul_of_nonneg_right hβcs hLpos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hLpos)] at h
    have hβ0 : 0 < schedBeta r lay ρ δs cQ D σ := by
      rw [schedBeta, hψ1']
      simp only [sub_self, zero_mul, zero_add, one_mul]
      exact lt_min hlay0 (div_pos (mul_pos hcQ0 hdeppos) hLpos)
    have harcA_bound : cQ * schedDep lay ρ δs D σ
        ≤ ‖r (taR D σ + schedDep lay ρ δs D σ) - r (taR D σ)‖ :=
      cQ_mul_le_norm_add (r := r) hm hδloc hρ hdeppos hdeple hdepμ hcQm hcQmd hnear hmono (taR D σ)
    have harcB_bound : cQ * schedDep lay ρ δs D σ
        ≤ ‖r (tbR D σ - schedDep lay ρ δs D σ) - r (tbR D σ)‖ :=
      cQ_mul_le_norm_sub (r := r) hm hδloc hρ hdeppos hdeple hdepμ hcQm hcQmd hnear hmonob (tbR D σ)
    have hballA : schedBeta r lay ρ δs cQ D σ * ‖r (tbR D σ) - r (taR D σ)‖
        ≤ ‖sweepArc' r D σ (schedAlpha lay ρ δs D σ) - r (taR D σ)‖ := by
      rw [harcA]
      exact le_trans hβLcQ harcA_bound
    have hballB : schedBeta r lay ρ δs cQ D σ * ‖r (tbR D σ) - r (taR D σ)‖
        ≤ ‖sweepArc' r D σ (1 - schedAlpha lay ρ δs D σ) - r (tbR D σ)‖ := by
      rw [harcB]
      exact le_trans hβLcQ harcB_bound
    have hsumL : s ≤ ‖r (tbR D σ) - r (taR D σ)‖ := by
      have hcρ : ρ < schedC D σ := lt_trans (by linarith) hcgt
      have h1 : ρ ≤ sweepW' D σ := le_trans hcρ.le (min_le_left _ _)
      have h2 : sweepW' D σ ≤ period - ρ := by
        have h3 : ρ ≤ period - sweepW' D σ := le_trans hcρ.le (min_le_right _ _)
        linarith
      have h4 : ρ ≤ circSep (tbR D σ) (taR D σ) :=
        circSep_ge_of_sub_mem hρ h1 h2
      exact chord_length_ge_of_sep hr hsep D (by rwa [circSep_comm'])
    have hsum : ‖sweepArc' r D σ (schedAlpha lay ρ δs D σ) - r (taR D σ)‖
        + ‖sweepArc' r D σ (1 - schedAlpha lay ρ δs D σ) - r (tbR D σ)‖
        < ‖r (tbR D σ) - r (taR D σ)‖ := by
      rw [harcA, harcB]
      have h1 : ‖r (taR D σ + schedDep lay ρ δs D σ) - r (taR D σ)‖
          ≤ M * schedDep lay ρ δs D σ := by
        have h := hlip (taR D σ + schedDep lay ρ δs D σ) (taR D σ)
        rw [show taR D σ + schedDep lay ρ δs D σ - taR D σ = schedDep lay ρ δs D σ by ring,
          abs_of_pos hdeppos] at h
        exact h
      have h2 : ‖r (tbR D σ - schedDep lay ρ δs D σ) - r (tbR D σ)‖
          ≤ M * schedDep lay ρ δs D σ := by
        have h := hlip (tbR D σ - schedDep lay ρ δs D σ) (tbR D σ)
        rw [show tbR D σ - schedDep lay ρ δs D σ - tbR D σ = -schedDep lay ρ δs D σ by ring,
          abs_neg, abs_of_pos hdeppos] at h
        exact h
      nlinarith [h1, h2, hsumL, hρs, hdeple, hM.le]
    have hmidA : ∀ u : ℝ, taR D σ + schedAlpha lay ρ δs D σ * sweepW' D σ ≤ u →
        u ≤ tbR D σ - schedAlpha lay ρ δs D σ * sweepW' D σ →
          r u ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) := by
      intro u hu1 hu2
      rw [hαW] at hu1 hu2
      by_cases hcδ : schedC D σ ≤ δs
      · exact hshortmid σ hσI hcδ u (by linarith [hdeppos.le]) (by linarith [hdeppos.le])
      · have hφ1 : schedPhi (schedC D σ / δs) = 1 := by
          rw [schedPhi_eq_one_iff, le_div_iff₀ hδs]; linarith
        have hdepρ : schedDep lay ρ δs D σ = ρ := by rw [hdep, hφ1, mul_one]
        rw [hdepρ] at hu1 hu2
        exact hfatmid σ hσI u hu1 hu2
    have hα0 : 0 < schedAlpha lay ρ δs D σ := by
      rw [schedAlpha]; exact div_pos hdeppos hW.1
    have hα2 : 2 * schedAlpha lay ρ δs D σ < 1 := by
      rw [schedAlpha, show 2 * (schedDep lay ρ δs D σ / sweepW' D σ)
          = 2 * schedDep lay ρ δs D σ / sweepW' D σ by ring, div_lt_one hW.1]
      linarith
    exact chamferLoopGenInjOnBall hr D hlay0 (by linarith) hσI hα0 hα2 hβ0
      hgapA hgapB hballA hballB hsum hmidA

end Work.Drive
