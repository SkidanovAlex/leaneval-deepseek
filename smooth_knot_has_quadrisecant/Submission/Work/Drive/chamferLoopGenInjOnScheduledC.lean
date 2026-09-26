import Mathlib
import Submission.Work.Drive.chamferLoopGenInjOnScheduled
import Submission.Work.Drive.chamferJunctionDefs
import Submission.Work.Drive.chamferJunctionOK_of_ball
import Submission.Work.Drive.chamferJunctionOK_of_tilt

namespace Work.Drive

set_option maxHeartbeats 1000000

open LeanEval.KnotTheory.Quadrisecant

/-!
# The scheduled slices, with the junction clause

`Work.Drive.chamferLoopGenInjOnScheduledC` is `Work.Drive.chamferLoopGenInjOnScheduledB` with the
second clause of the lead's design (`NOTES_LEAD_scheduledBlur.md` §1) added: for the *same*
schedules, not only is the loop injective on one period at every slice of the window, but its four
junctions are non-degenerate (`Work.Drive.ChamferJunctionOK`).  The pair is exactly the interface
consumed by `Work.Drive.chamferLoopGen_localCone`.

The proof is the proof of `ScheduledB` with three additions:

* the constant `cQ`/`κ₁` bookkeeping is run against a *smaller* cap
  `Lmax' = min Lmax (min ((min μa μb) / (4 C period)) (Lmin / (2 M period)))`, where `μa`, `μb` are
  the uniform tilt margins at the two endpoints of the chord (`exists_tilt_margin`,
  `cli_exists_tilt_margin_head`) and `Lmin` a uniform lower bound for the chord length
  (`cli_exists_chordLen_pos`);
* in the **deep zone** (`ρ φ ≤ lay W`, i.e. `α σ * W = ρ φ ≤ ρ`) the junction clause comes from
  `chamferJunctionOK_of_ball`, whose two extra hypotheses `hradA`/`hradB` are supplied by the radial
  monotonicity hypotheses `hmono`/`hmonob` of the statement — the radial distance is increasing, so
  its derivative `2 ⟪r (a ± x) - r a, r' (a ± x)⟫` is signed (`inner_radial_nonneg_of_mono`,
  `inner_radial_nonpos_of_monob` below);
* in the **short zone** (`α σ = lay`) the junction clause comes from `chamferJunctionOK_of_tilt`,
  whose depth conditions `2 C (lay W) < μa`, `2 C (lay W) < μb`, `M (lay W) < L` are exactly what
  the smaller cap `Lmax'` buys, using `W < period` and `Lmin ≤ L`.
-/

section RadialHelpers

/-- The forward radial distance squared, differentiated. -/
lemma hasDerivAt_radial_fwd {r : ℝ → Space} (hr : IsSmoothKnot r) (a x : ℝ) :
    HasDerivAt (fun s : ℝ => ‖r (a + s) - r a‖ ^ 2)
      (2 * inner ℝ (r (a + x) - r a) (velocity r (a + x))) x := by
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
  have hdiff : Differentiable ℝ r := hsm.differentiable (by simp)
  have h1 : HasDerivAt (fun s : ℝ => r (a + s) - r a) (velocity r (a + x)) x := by
    have h2 := ((hdiff (a + x)).hasDerivAt.comp_const_add a x).sub_const (r a)
    simpa only [velocity] using h2
  exact h1.norm_sq

/-- The backward radial distance squared, differentiated. -/
lemma hasDerivAt_radial_bwd {r : ℝ → Space} (hr : IsSmoothKnot r) (a x : ℝ) :
    HasDerivAt (fun s : ℝ => ‖r (a - s) - r a‖ ^ 2)
      (2 * inner ℝ (r (a - x) - r a) (-(velocity r (a - x)))) x := by
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
  have hdiff : Differentiable ℝ r := hsm.differentiable (by simp)
  have h1 : HasDerivAt (fun s : ℝ => r (a - s) - r a) (-(velocity r (a - x))) x := by
    have h2 := ((hdiff (a - x)).hasDerivAt.comp_const_sub a x).sub_const (r a)
    simpa only [velocity] using h2
  exact h1.norm_sq

/-- **The radial sign at a forward-increasing point.**  If the radial distance
`y ↦ ‖r (a + y) - r a‖` is strictly increasing on `[0, μ]`, then the radial inner product at an
interior point `x ∈ (0, μ)` is nonnegative. -/
lemma inner_radial_nonneg_of_mono {r : ℝ → Space} (hr : IsSmoothKnot r) {μ : ℝ}
    (hmono : ∀ a x y : ℝ, 0 ≤ x → x < y → y ≤ μ → ‖r (a + x) - r a‖ < ‖r (a + y) - r a‖)
    {a x : ℝ} (hx0 : 0 < x) (hxμ : x < μ) :
    0 ≤ inner ℝ (r (a + x) - r a) (velocity r (a + x)) := by
  have hmonoOn : MonotoneOn (fun y : ℝ => ‖r (a + y) - r a‖ ^ 2) (Set.Icc 0 μ) := by
    intro y₁ hy₁ y₂ hy₂ hy12
    rcases eq_or_lt_of_le hy12 with h | h
    · rw [h]
    · have h1 := hmono a y₁ y₂ hy₁.1 h hy₂.2
      have h2 : (0 : ℝ) ≤ ‖r (a + y₁) - r a‖ := norm_nonneg _
      have h3 : (0 : ℝ) ≤ ‖r (a + y₂) - r a‖ := norm_nonneg _
      nlinarith [h1, h2, h3]
  have hmem : Set.Icc (0 : ℝ) μ ∈ nhds x := Icc_mem_nhds hx0 hxμ
  have h1 : 0 ≤ derivWithin (fun y : ℝ => ‖r (a + y) - r a‖ ^ 2) (Set.Icc 0 μ) x :=
    hmonoOn.derivWithin_nonneg
  have h2 := derivWithin_of_mem_nhds
    (f := fun y : ℝ => ‖r (a + y) - r a‖ ^ 2) (s := Set.Icc (0 : ℝ) μ) (x := x) hmem
  rw [h2, (hasDerivAt_radial_fwd hr a x).deriv] at h1
  linarith

/-- **The radial sign at a backward-increasing point** (the mirror of
`inner_radial_nonneg_of_mono`). -/
lemma inner_radial_nonpos_of_monob {r : ℝ → Space} (hr : IsSmoothKnot r) {μ : ℝ}
    (hmonob : ∀ a x y : ℝ, 0 ≤ x → x < y → y ≤ μ → ‖r (a - x) - r a‖ < ‖r (a - y) - r a‖)
    {a x : ℝ} (hx0 : 0 < x) (hxμ : x < μ) :
    inner ℝ (r (a - x) - r a) (velocity r (a - x)) ≤ 0 := by
  have hmonoOn : MonotoneOn (fun y : ℝ => ‖r (a - y) - r a‖ ^ 2) (Set.Icc 0 μ) := by
    intro y₁ hy₁ y₂ hy₂ hy12
    rcases eq_or_lt_of_le hy12 with h | h
    · rw [h]
    · have h1 := hmonob a y₁ y₂ hy₁.1 h hy₂.2
      have h2 : (0 : ℝ) ≤ ‖r (a - y₁) - r a‖ := norm_nonneg _
      have h3 : (0 : ℝ) ≤ ‖r (a - y₂) - r a‖ := norm_nonneg _
      nlinarith [h1, h2, h3]
  have hmem : Set.Icc (0 : ℝ) μ ∈ nhds x := Icc_mem_nhds hx0 hxμ
  have h1 : 0 ≤ derivWithin (fun y : ℝ => ‖r (a - y) - r a‖ ^ 2) (Set.Icc 0 μ) x :=
    hmonoOn.derivWithin_nonneg
  have h2 := derivWithin_of_mem_nhds
    (f := fun y : ℝ => ‖r (a - y) - r a‖ ^ 2) (s := Set.Icc (0 : ℝ) μ) (x := x) hmem
  rw [h2, (hasDerivAt_radial_bwd hr a x).deriv, inner_neg_right] at h1
  linarith

end RadialHelpers

section Arithmetic

/-- The tilt-scale arithmetic: a cap below `A / (4 C P)` times a width below `P` keeps
`2 C (lay * width)` below `A / 2`. -/
private lemma tilt_cap_bound {C P A L lay W : ℝ} (hC : 0 < C) (hP : 0 < P)
    (hL : L ≤ A / (4 * C * P)) (hL0 : 0 ≤ L) (hlay : lay ≤ L) (hW0 : 0 ≤ W) (hWp : W ≤ P) :
    2 * C * (lay * W) ≤ A / 2 := by
  have hCP : (0 : ℝ) ≤ 4 * C * P := by positivity
  have hne : 4 * C * P ≠ 0 := ne_of_gt (by positivity)
  have h2 : L * (4 * C * P) ≤ A := by
    have h := mul_le_mul_of_nonneg_right hL hCP
    rwa [div_mul_cancel₀ _ hne] at h
  have h3 : L * W ≤ L * P := mul_le_mul_of_nonneg_left hWp hL0
  have h4 : lay * W ≤ L * P := le_trans (mul_le_mul_of_nonneg_right hlay hW0) h3
  have h5 : 4 * C * (lay * W) ≤ A := by
    have h7 : 4 * C * (lay * W) ≤ 4 * C * (L * P) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h8 : 4 * C * (L * P) = L * (4 * C * P) := by ring
    linarith [h7, h8.le, h8.ge, h2]
  linarith

/-- The chord-length arithmetic: a cap below `A / (2 M P)` times a width below `P` keeps
`M (lay * width)` below `A / 2`. -/
private lemma chord_cap_bound {M P A L lay W : ℝ} (hM : 0 < M) (hP : 0 < P)
    (hL : L ≤ A / (2 * M * P)) (hL0 : 0 ≤ L) (hlay : lay ≤ L) (hW0 : 0 ≤ W) (hWp : W ≤ P) :
    M * (lay * W) ≤ A / 2 := by
  have hMP : (0 : ℝ) ≤ 2 * M * P := by positivity
  have hne : 2 * M * P ≠ 0 := ne_of_gt (by positivity)
  have h2 : L * (2 * M * P) ≤ A := by
    have h := mul_le_mul_of_nonneg_right hL hMP
    rwa [div_mul_cancel₀ _ hne] at h
  have h3 : L * W ≤ L * P := mul_le_mul_of_nonneg_left hWp hL0
  have h4 : lay * W ≤ L * P := le_trans (mul_le_mul_of_nonneg_right hlay hW0) h3
  have h5 : 2 * M * (lay * W) ≤ A := by
    have h7 : 2 * M * (lay * W) ≤ 2 * M * (L * P) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h8 : 2 * M * (L * P) = L * (2 * M * P) := by ring
    linarith [h7, h8.le, h8.ge, h2]
  linarith

end Arithmetic

open LeanEval.KnotTheory.Quadrisecant Set in
theorem chamferLoopGenInjOnScheduledC {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {ρ μ s δs M Lmax : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (hρμ : 2 * ρ ≤ μ) (hs : 0 < s) (hM : 0 < M)
    (hMv : ∀ t : ℝ, ‖LeanEval.KnotTheory.Quadrisecant.velocity r t‖ ≤ M)
    (hρs : 2 * M * ρ < s) (hδs : 0 < δs) (hρδs : 2 * ρ < δs) (hLmax : 0 < Lmax)
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
    ∃ lay ρ₀ cQ : ℝ, 0 < lay ∧ lay ≤ Lmax ∧ lay ≤ 1 / 4 ∧ 0 < ρ₀ ∧ 0 < cQ ∧ cQ ≤ 1 ∧
      ∀ σ ∈ Set.Icc a b,
        Set.InjOn (Work.Drive.chamferLoopGen r D lay
          (Work.Drive.schedAlpha lay ρ₀ δs D) (Work.Drive.schedBeta r lay ρ₀ δs cQ D) σ)
          (Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period) ∧
        Work.Drive.ChamferJunctionOK r D (Work.Drive.schedAlpha lay ρ₀ δs D)
          (Work.Drive.schedBeta r lay ρ₀ δs cQ D) σ := by
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
  -- ## 1b. the extra uniform data used by the junction clause
  obtain ⟨m₂, M₂, Cc, hm₂, hM₂, hCc, hvelc, hvelC, hvlip⟩ := exists_knot_c2_bounds hr
  have hposab : ∀ σ ∈ Set.Icc a b, 0 < sweepW' D σ ∧ sweepW' D σ < period := fun σ hσ =>
    clg_sweepW_pos_lt D (hσIoo σ hσ)
  have hposab' : ∀ σ ∈ Set.Icc a b, 0 < tbR D σ - taR D σ ∧ tbR D σ - taR D σ < period := by
    intro σ hσ
    have h := hposab σ hσ
    rwa [cli_sweepW_eq_sub] at h
  obtain ⟨μa, hμa, hμa_le⟩ := exists_tilt_margin hr (taR D) (tbR D) (cli_continuous_taR D)
    (cli_continuous_tbR D) hab.le hposab' (fun s hs m => hntA s (hσIoo s hs) m)
  obtain ⟨μb, hμb, hμb_le⟩ := cli_exists_tilt_margin_head hr D hab.le hposab
    (fun s hs m => hntB s (hσIoo s hs) m)
  obtain ⟨Lmin, hLmin, hLmin_le⟩ := cli_exists_chordLen_pos hr D hab.le
    (fun s hs => hV s (hσIoo s hs))
  have hminab : 0 < min μa μb := lt_min hμa hμb
  -- the *smaller* cap which makes the junction clause available
  set Lmax' : ℝ := min Lmax (min ((min μa μb) / (4 * Cc * period)) (Lmin / (2 * M * period)))
    with hLmax'def
  have hLmax'0 : 0 < 4 * Cc * period := by positivity
  have hLmax'M : 0 < 2 * M * period := by positivity
  have hLmax'pos : 0 < Lmax' := by
    rw [hLmax'def]
    exact lt_min hLmax (lt_min (div_pos hminab hLmax'0) (div_pos hLmin hLmax'M))
  have hLmax'leMax : Lmax' ≤ Lmax := by rw [hLmax'def]; exact min_le_left _ _
  have hLmax'leA : Lmax' ≤ (min μa μb) / (4 * Cc * period) := by
    rw [hLmax'def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hLmax'leL : Lmax' ≤ Lmin / (2 * M * period) := by
    rw [hLmax'def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- ## 2. the constants `cQ`, `κ₁`, `lay`
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
  set lay : ℝ := min (min LB (1 / 4)) Lmax' with hlaydef
  have hlay0 : 0 < lay := by rw [hlaydef]; exact lt_min (lt_min hLB0 (by norm_num)) hLmax'pos
  have hlay4 : lay ≤ 1 / 4 := by
    rw [hlaydef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hlayLmax' : lay ≤ Lmax' := by rw [hlaydef]; exact min_le_right _ _
  have hlayLmax : lay ≤ Lmax := le_trans hlayLmax' hLmax'leMax
  have hlayLB : lay ≤ LB := by
    rw [hlaydef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hl2 : (1 : ℝ) * lay < 1 / 2 := by linarith
  refine ⟨lay, ρ, cQ, hlay0, hlayLmax, hlay4, hρ, hcQ0, hcQ1, ?_⟩
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
    refine ⟨hBLem lay hlay0 hlayLB hl2 (schedAlpha lay ρ δs D) (schedBeta r lay ρ δs cQ D)
      σ hσ hαeq hβge (by linarith [hβle]) hmid, ?_⟩
    -- the junction clause in the short zone
    have hWle : sweepW' D σ ≤ period := hW.2.le
    have htiltA : 2 * Cc * (schedAlpha lay ρ δs D σ * sweepW' D σ) < μa := by
      rw [hαeq]
      have h1 : 2 * Cc * (lay * sweepW' D σ) ≤ min μa μb / 2 :=
        tilt_cap_bound hCc hper hLmax'leA hLmax'pos.le hlayLmax' hW.1.le hWle
      have h2 : min μa μb / 2 < μa := by
        have h3 := min_le_left μa μb
        linarith [hμa]
      linarith
    have htiltB : 2 * Cc * (schedAlpha lay ρ δs D σ * sweepW' D σ) < μb := by
      rw [hαeq]
      have h1 : 2 * Cc * (lay * sweepW' D σ) ≤ min μa μb / 2 :=
        tilt_cap_bound hCc hper hLmax'leA hLmax'pos.le hlayLmax' hW.1.le hWle
      have h2 : min μa μb / 2 < μb := by
        have h3 := min_le_right μa μb
        linarith [hμb]
      linarith
    have hchord : M * (schedAlpha lay ρ δs D σ * sweepW' D σ) < ‖r (tbR D σ) - r (taR D σ)‖ := by
      rw [hαeq]
      have h1 : M * (lay * sweepW' D σ) ≤ Lmin / 2 :=
        chord_cap_bound hM hper hLmax'leL hLmax'pos.le hlayLmax' hW.1.le hWle
      have h2 : Lmin / 2 < ‖r (tbR D σ) - r (taR D σ)‖ := by
        have h3 := hLmin_le σ hσ
        linarith [hLmin]
      linarith
    have hmid' : ∀ u : ℝ, taR D σ + schedAlpha lay ρ δs D σ * sweepW' D σ ≤ u →
        u ≤ tbR D σ - schedAlpha lay ρ δs D σ * sweepW' D σ →
          r u ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) := by
      intro u hu1 hu2
      rw [hαeq] at hu1 hu2
      exact hmid u hu1 hu2
    exact chamferJunctionOK_of_tilt (r := r) (μa := μa) (μb := μb) (C := Cc) hr D hW.1
      (by rw [hαeq]; exact hlay0) (by rw [hαeq]; linarith)
      (lt_of_lt_of_le (mul_pos hκ₁0 hlay0) hβge)
      (by linarith [hβle, hlay4]) (hV σ hσI) hMv hCc.le hvlip (hμa_le σ hσ) (hμb_le σ hσ)
      htiltA htiltB hchord hmid'
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
    have hdepμ' : schedDep lay ρ δs D σ < μ := by linarith
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
    have hargB : taR D σ + (1 - schedAlpha lay ρ δs D σ) * sweepW' D σ
        = tbR D σ - schedDep lay ρ δs D σ := by
      rw [hcoef]; linarith [hWdef]
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
    refine ⟨chamferLoopGenInjOnBall hr D hlay0 (by linarith) hσI hα0 hα2 hβ0
      hgapA hgapB hballA hballB hsum hmidA, ?_⟩
    -- the junction clause in the deep zone
    have hβ2 : 2 * schedBeta r lay ρ δs cQ D σ < 1 :=
      clg_beta_lt_half D hβ0 hballA hballB hsum
    refine chamferJunctionOK_of_ball hr D hW.1 hα0 hα2 hβ0 hβ2 (hV σ hσI)
      hballA hballB hsum hmidA ?_ ?_
    · rw [harcA, hαW]
      exact inner_radial_nonneg_of_mono (μ := μ) hr hmono hdeppos hdepμ'
    · rw [harcB, hargB]
      exact inner_radial_nonpos_of_monob (μ := μ) hr hmonob hdeppos hdepμ'

end Work.Drive
