import Mathlib
import Submission.Work.Drive.chamferLoopGenInjOnScheduledC4
import Submission.Work.Drive.blurSlicesScheduledFull
import Submission.Work.Drive.thinLocalRadial
import Submission.Work.Drive.thinCornerDistanceIncreasingParamNoInfl
import Submission.Work.Drive.separation_of_far_parameters
import Submission.Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul

/-!
# The scheduling slot of the `OFat` endgame, from the crosscut data

`Work.Drive.SchedSlot r D δs Lmax a b` (`Drive/blurSlicesScheduledFull.lean`) is the geometric input
of the blurred-slices clause of the uniform-`ρ₀` design: the scheduling parameters `(lay, ρ₀, cQ)`
together with the injectivity of the *raw* scheduled loop and the junction non-degeneracy
`Work.Drive.ChamferJunctionOK` on the clamped window `[a/2, (1+b)/2]`.

This module **produces** that slot from

* the **crosscut data** of `Work.Drive.bandArcData_sweepData_of_stripCrosscutOFatS`: a `SweepData`
  `D` of the period strip whose chords carry no retained middle at scale `ρ`, carry *no* middle at all
  when the chord is short (`≤ δs` or `≥ period - δs`), and are non-tangent at both endpoints;
* the **ball-uniform tools** around a reference knot `r₀`:
  `Work.Drive.exists_local_radial_mono` (the radial monotonicity, at a scale `μ`),
  `Work.Drive.thinCornerDistanceIncreasingParamNoInfl` (the radial gap `‖r (x ± ρ) - r x‖ <
  ‖r s - r x‖`, at every `ρ ≤ μ`),
  `Work.Drive.separation_of_far_parameters` (far parameters are spatially far) and
  `Work.Drive.exists_knot_velocity_bound` (a speed bound `V`);
* the **repaired** injectivity lemma `Work.Drive.chamferLoopGenInjOnScheduledC4`, whose `hsep`
  hypothesis is at the short-chord scale `δs/4` (see `NOTES_OFat_hsep_scale_BUG_AND_REPAIR.md` for
  why the original scale `ρ` makes the lemma unsatisfiable) and whose `hρs` companion is
  `2 * V * ρ < s`.

No `havoid`, no trisecant analysis, no uniformity of the tilt margin.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant Set

/-- `cross3 v w ≠ 0` forbids `v = m • w` (`Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul`). -/
private lemma not_smul_of_cross3_ne' {v w : Space} (h : cross3 v w ≠ 0) (m : ℝ) : v ≠ m • w := by
  intro heq
  rcases eq_or_ne m 0 with hm | hm
  · subst hm
    rw [zero_smul] at heq
    exact h ((Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul v w).mpr (Or.inl heq))
  · refine h ((Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul v w).mpr (Or.inr ⟨m⁻¹, ?_⟩))
    rw [heq, smul_smul, inv_mul_cancel₀ hm, one_smul]

/-- `clampI` is the identity on `(0,1)`; the subtype form of the point. -/
private lemma clampI_of_mem_Ioo {σ : ℝ} (h : σ ∈ Set.Ioo (0 : ℝ) 1) :
    clampI σ = ⟨σ, le_of_lt h.1, le_of_lt h.2⟩ := by
  apply Subtype.ext
  simp only [clampI, Subtype.coe_mk]
  rw [max_eq_right (le_of_lt h.1), min_eq_right (le_of_lt h.2)]

private lemma taR_eq_clampI {d : BandArcData} (D : SweepData d) {σ : ℝ}
    (h : σ ∈ Set.Ioo (0 : ℝ) 1) :
    taR D σ = D.ta ⟨σ, le_of_lt h.1, le_of_lt h.2⟩ := by
  rw [taR, clampI_of_mem_Ioo h]

private lemma tbR_eq_clampI {d : BandArcData} (D : SweepData d) {σ : ℝ}
    (h : σ ∈ Set.Ioo (0 : ℝ) 1) :
    tbR D σ = D.tb ⟨σ, le_of_lt h.1, le_of_lt h.2⟩ := by
  rw [tbR, clampI_of_mem_Ioo h]

/-- **The ball-uniform data around a reference knot.**  The radial tools of the endgame, uniform
over the `C²`-ball of radius `ε` around `r₀`, with the radial scale `μ` and the speed bound `V`. -/
def BallData (r₀ : ℝ → Space) (ε μ V : ℝ) : Prop :=
  ∀ r' : ℝ → Space, IsSmoothKnot r' →
    (∀ t : ℝ, ‖r' t - r₀ t‖ < ε ∧ ‖velocity r' t - velocity r₀ t‖ < ε ∧
      ‖deriv (deriv r') t - deriv (deriv r₀) t‖ < ε) →
    (∀ t : ℝ, ‖velocity r' t‖ ≤ V) ∧
    (∀ a x y : ℝ, 0 ≤ x → x < y → y ≤ μ → ‖r' (a + x) - r' a‖ < ‖r' (a + y) - r' a‖) ∧
    (∀ a x y : ℝ, 0 ≤ x → x < y → y ≤ μ → ‖r' (a - x) - r' a‖ < ‖r' (a - y) - r' a‖) ∧
    (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ μ → ∀ x y : ℝ, 2 * ρ' ≤ circSep y x →
      ‖r' (x + ρ') - r' x‖ < ‖r' y - r' x‖) ∧
    (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ μ → ∀ x y : ℝ, 2 * ρ' ≤ circSep y x →
      ‖r' (x - ρ') - r' x‖ < ‖r' y - r' x‖)

/-- **The ball-uniform data around a smooth knot.**  From `Work.Drive.exists_local_radial_mono`,
`Work.Drive.thinCornerDistanceIncreasingParamNoInfl` and `Work.Drive.exists_knot_c2_bounds`. -/
theorem exists_ballData (r₀ : ℝ → Space) (hr₀ : IsSmoothKnot r₀) :
    ∃ ε μ V : ℝ, 0 < ε ∧ 0 < μ ∧ 0 < V ∧ BallData r₀ ε μ V := by
  obtain ⟨εr, μr, hεr, hμr, hrad⟩ := exists_local_radial_mono hr₀
  obtain ⟨εc, ρc, hεc, hρc, -, hgap0⟩ := thinCornerDistanceIncreasingParamNoInfl hr₀
  obtain ⟨m₀, M₀, C₀, hm₀, hM₀, hC₀, hspd₀, hspdM₀, hlip₀⟩ := exists_knot_c2_bounds hr₀
  have hVpos : 0 < M₀ + 1 := by linarith
  refine ⟨min (min εr εc) 1, min μr ρc, M₀ + 1, ?_, ?_, hVpos, ?_⟩
  · exact lt_min (lt_min hεr hεc) one_pos
  · exact lt_min hμr hρc
  · intro r' hr' hclose
    have hε1 : min (min εr εc) 1 ≤ 1 := le_trans (min_le_right _ _) le_rfl
    have hεr' : min (min εr εc) 1 ≤ εr := le_trans (min_le_left _ _) (min_le_left _ _)
    have hεc' : min (min εr εc) 1 ≤ εc := le_trans (min_le_left _ _) (min_le_right _ _)
    have hμm : min μr ρc ≤ μr := min_le_left _ _
    have hμc : min μr ρc ≤ ρc := min_le_right _ _
    have hclose_r : ∀ t : ℝ, ‖r' t - r₀ t‖ < εr ∧
        ‖velocity r' t - velocity r₀ t‖ < εr ∧
        ‖deriv (deriv r') t - deriv (deriv r₀) t‖ < εr :=
      fun t => ⟨lt_of_lt_of_le (hclose t).1 hεr', lt_of_lt_of_le (hclose t).2.1 hεr',
        lt_of_lt_of_le (hclose t).2.2 hεr'⟩
    have hclose_c : ∀ t : ℝ, ‖r' t - r₀ t‖ < εc ∧
        ‖velocity r' t - velocity r₀ t‖ < εc ∧
        ‖deriv (deriv r') t - deriv (deriv r₀) t‖ < εc :=
      fun t => ⟨lt_of_lt_of_le (hclose t).1 hεc', lt_of_lt_of_le (hclose t).2.1 hεc',
        lt_of_lt_of_le (hclose t).2.2 hεc'⟩
    obtain ⟨hmono', hmonob'⟩ := hrad r' hr' hclose_r
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro t
      have h1 : ‖velocity r' t‖ ≤ ‖velocity r₀ t‖ + ‖velocity r' t - velocity r₀ t‖ := by
        have h5 := norm_add_le (velocity r₀ t) (velocity r' t - velocity r₀ t)
        have h6 : velocity r₀ t + (velocity r' t - velocity r₀ t) = velocity r' t := by abel
        rw [h6] at h5
        exact h5
      have h2 : ‖velocity r' t - velocity r₀ t‖ < 1 := lt_of_lt_of_le (hclose t).2.1 hε1
      linarith [hspdM₀ t]
    · intro a x y hx hxy hy
      exact hmono' a x y hx hxy (le_trans hy hμm)
    · intro a x y hx hxy hy
      exact hmonob' a x y hx hxy (le_trans hy hμm)
    · intro ρ' hρ' hρ'μ x y hsep
      exact (hgap0 r' hr' hclose_c ρ' hρ' (le_trans hρ'μ hμc) x y hsep).1
    · intro ρ' hρ' hρ'μ x y hsep
      exact (hgap0 r' hr' hclose_c ρ' hρ' (le_trans hρ'μ hμc) x y hsep).2

/-- **The scheduling slot from the crosscut data.**  The numerical data are the ball-uniform
constants of `Work.Drive.exists_ballData`; the extra inputs are the far-parameter separation `s` at
the short-chord scale `δs/4` and the fatness scale `ρ` (with `2 V ρ < s`). -/
theorem schedSlot_of_ballData (r₀ : ℝ → Space) {ε μ V : ℝ} (hall : BallData r₀ ε μ V) :
    ∀ r' : ℝ → Space, IsSmoothKnot r' →
      (∀ t : ℝ, ‖r' t - r₀ t‖ < ε ∧ ‖velocity r' t - velocity r₀ t‖ < ε ∧
        ‖deriv (deriv r') t - deriv (deriv r₀) t‖ < ε) →
      ∀ {δs ρ Lmax a b s : ℝ} (hδs : 0 < δs) (hρ : 0 < ρ) (hρμ : 2 * ρ ≤ μ)
        (hρδs : 2 * ρ < δs) (hLmax : 0 < Lmax) (ha : 0 < a) (hab : a < b) (hb : b < 1)
        (hsep : ∀ p q : KnotParam, δs / 4 ≤ dist p q →
          s ≤ ‖knotMap r' p - knotMap r' q‖)
        (hs : 0 < s) (hρs : 2 * V * ρ < s)
        {d : BandArcData} (D : SweepData d)
        (hmid : ∀ (u : Set.Icc (0 : ℝ) 1), (u : ℝ) ≠ 0 → (u : ℝ) ≠ 1 → ∀ z : ℝ,
          D.ta u + ρ ≤ z → z ≤ D.tb u - ρ →
            r' z ∉ openSegment ℝ (r' (D.ta u)) (r' (D.tb u)))
        (hshort : ∀ (u : Set.Icc (0 : ℝ) 1), (u : ℝ) ≠ 0 → (u : ℝ) ≠ 1 →
          (D.tb u - D.ta u ≤ δs ∨ period - (D.tb u - D.ta u) ≤ δs) → ∀ z : ℝ,
          D.ta u ≤ z → z ≤ D.tb u →
            r' z ∉ openSegment ℝ (r' (D.ta u)) (r' (D.tb u)))
        (hnt : ∀ (u : Set.Icc (0 : ℝ) 1), (u : ℝ) ≠ 0 → (u : ℝ) ≠ 1 →
          cross3 (r' (D.tb u) - r' (D.ta u)) (velocity r' (D.ta u)) ≠ 0 ∧
          cross3 (r' (D.tb u) - r' (D.ta u)) (velocity r' (D.tb u)) ≠ 0) ,
      SchedSlot r' D δs Lmax a b := by
  intro r' hr' hclose δs ρ Lmax a b s hδs hρ hρμ hρδs hLmax ha hab hb hsep hs hρs d D
    hmid hshort hnt
  obtain ⟨hMv, hmono, hmonob, hgap, hgapb⟩ := hall r' hr' hclose
  have hVpos : 0 < V := lt_of_lt_of_le (norm_pos_iff.mpr (hr'.regular 0)) (hMv 0)
  have hμpos : 0 < μ := by linarith
  -- the clamped window
  have ha' : 0 < a / 2 := by linarith
  have hab' : a / 2 < (1 + b) / 2 := by linarith
  have hb' : (1 + b) / 2 < 1 := by linarith
  -- the conversions of the crosscut clauses to the `r`-parametrised form
  have hfatmid : ∀ σ : ℝ, σ ∈ Set.Ioo (0 : ℝ) 1 → ∀ z : ℝ,
      taR D σ + ρ ≤ z → z ≤ tbR D σ - ρ →
        r' z ∉ openSegment ℝ (r' (taR D σ)) (r' (tbR D σ)) := by
    intro σ hσ z hz1 hz2 hmem
    exact hmid ⟨σ, le_of_lt hσ.1, le_of_lt hσ.2⟩ (ne_of_gt hσ.1) (ne_of_lt hσ.2) z
      (by simpa only [taR_eq_clampI D hσ, tbR_eq_clampI D hσ] using hz1)
      (by simpa only [taR_eq_clampI D hσ, tbR_eq_clampI D hσ] using hz2)
      (by simpa only [taR_eq_clampI D hσ, tbR_eq_clampI D hσ] using hmem)
  have hshortmid : ∀ σ : ℝ, σ ∈ Set.Ioo (0 : ℝ) 1 → schedC D σ ≤ δs → ∀ z : ℝ,
      taR D σ ≤ z → z ≤ tbR D σ →
        r' z ∉ openSegment ℝ (r' (taR D σ)) (r' (tbR D σ)) := by
    intro σ hσ hc z hz1 hz2 hmem
    have hW : sweepW' D σ = D.tb ⟨σ, le_of_lt hσ.1, le_of_lt hσ.2⟩
        - D.ta ⟨σ, le_of_lt hσ.1, le_of_lt hσ.2⟩ := by
      rw [sweepW', taR_eq_clampI D hσ, tbR_eq_clampI D hσ]
    have hdisj : D.tb ⟨σ, le_of_lt hσ.1, le_of_lt hσ.2⟩
          - D.ta ⟨σ, le_of_lt hσ.1, le_of_lt hσ.2⟩ ≤ δs ∨
        period - (D.tb ⟨σ, le_of_lt hσ.1, le_of_lt hσ.2⟩
          - D.ta ⟨σ, le_of_lt hσ.1, le_of_lt hσ.2⟩) ≤ δs := by
      have h1 : min (sweepW' D σ) (period - sweepW' D σ) ≤ δs := hc
      rcases min_le_iff.mp h1 with h | h
      · exact Or.inl (by rw [← hW]; exact h)
      · exact Or.inr (by rw [← hW]; exact h)
    exact hshort ⟨σ, le_of_lt hσ.1, le_of_lt hσ.2⟩ (ne_of_gt hσ.1) (ne_of_lt hσ.2) hdisj z
      (by simpa only [taR_eq_clampI D hσ, tbR_eq_clampI D hσ] using hz1)
      (by simpa only [taR_eq_clampI D hσ, tbR_eq_clampI D hσ] using hz2)
      (by simpa only [taR_eq_clampI D hσ, tbR_eq_clampI D hσ] using hmem)
  have hntA0 : ∀ σ : ℝ, σ ∈ Set.Ioo (0 : ℝ) 1 → ∀ m : ℝ,
      r' (tbR D σ) - r' (taR D σ) ≠ m • velocity r' (taR D σ) := by
    intro σ hσ m
    have h := (hnt ⟨σ, le_of_lt hσ.1, le_of_lt hσ.2⟩ (ne_of_gt hσ.1) (ne_of_lt hσ.2)).1
    exact not_smul_of_cross3_ne'
      (by simpa only [taR_eq_clampI D hσ, tbR_eq_clampI D hσ] using h) m
  have hntB0 : ∀ σ : ℝ, σ ∈ Set.Ioo (0 : ℝ) 1 → ∀ m : ℝ,
      r' (tbR D σ) - r' (taR D σ) ≠ m • velocity r' (tbR D σ) := by
    intro σ hσ m
    have h := (hnt ⟨σ, le_of_lt hσ.1, le_of_lt hσ.2⟩ (ne_of_gt hσ.1) (ne_of_lt hσ.2)).2
    exact not_smul_of_cross3_ne'
      (by simpa only [taR_eq_clampI D hσ, tbR_eq_clampI D hσ] using h) m
  have hV' : ∀ σ : ℝ, σ ∈ Set.Ioo (0 : ℝ) 1 → r' (taR D σ) ≠ r' (tbR D σ) := by
    intro σ hσ hEq
    have h := hntA0 σ hσ 0
    rw [zero_smul] at h
    exact h (sub_eq_zero.mpr hEq.symm)
  obtain ⟨lay, ρf, cQ, h1, h2, h3, h4, h5, h6, hIJ⟩ :=
    chamferLoopGenInjOnScheduledC4 hr' D hρ hμpos hρμ hs hVpos hMv hρs hδs hρδs hLmax
      hmono hmonob hgap hgapb hsep hfatmid hshortmid hV' hntA0 hntB0 ha' hab' hb'
  exact ⟨lay, ρf, cQ, h1, h2, h3, h4, h5, h6, hIJ⟩

end Work.Drive
