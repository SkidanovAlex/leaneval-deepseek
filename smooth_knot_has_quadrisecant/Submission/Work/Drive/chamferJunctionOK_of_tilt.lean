import Mathlib
import Submission.Work.Drive.chamferJunctionDefs
import Submission.Work.Drive.thinCornerDistanceIncreasingParam
import Submission.Work.Drive.chamferCrossingThin

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

set_option linter.unusedVariables false

/-!
# The junction non-degeneracy from the tilt hypotheses

`Work.Drive.chamferJunctionOK_of_tilt` produces `Work.Drive.ChamferJunctionOK r D α β σ` from the
*tilt* data of the secant `r (taR D σ) → r (tbR D σ)`:

* `nA` (resp. `nB`) is the component of the velocity at `taR D σ` (resp. `tbR D σ`) orthogonal to
  the chord; the hypotheses `hμa`/`hμb` bound its length below by `μa`/`μb`, and `hdepA`/`hdepB`
  say that the *depth* `α σ * sweepW' D σ` of the chamfer is below the tilt scale divided by `2 C`
  (`C` a Lipschitz constant for the velocity).

Consequently, on a strip of arc of parameter length `α σ * sweepW' D σ` at *both* ends of the
retained arc, the pairing of `nA` (resp. `nB`) with the knot velocity is strictly positive (indeed
`≥ ‖nA‖ ^ 2 / 2`).  Hence:

* the two cut points `sweepArc' … α` and `sweepArc' … (1 - α)` are strictly on one side of the
  chord's line (`nA`-pairing positive at the low end, `nB`-pairing negative at the high end, since
  the arc is traversed towards `tb`), so they are *not* on the chord: clauses 7 and 8;
* the four reversal conditions (clauses 9–12) compare the pairing of the connector directions with
  `nA`/`nB`: the connector difference pairs *positively* with the tilt vector, while a reversal
  `∓ k • velocity` (resp. `k • (r tb - r ta)`) pairs strictly *negatively* (resp. vanishes).

The extra hypotheses `hMv`, `hdepL`, `hmid` of the statement are not needed for this half of the
junction condition (they belong to the injectivity/far-separation half); they are kept because the
statement is the interface consumed downstream.
-/

/-- **The tilt slack at the low end.**  If the tilt `n = chordTilt (r ta) (r tb) (velocity r ta)`
of the chord has length at least `μ` and `2 * C * d < μ`, then the pairing of the knot velocity with
`n` is bounded below by `‖n‖ ^ 2 / 2` on the parameter interval `[ta, ta + d]`. -/
lemma chordTilt_slack_left {r : ℝ → Space} (hr : IsSmoothKnot r) {ta tb C d μ : ℝ}
    (hC : 0 ≤ C) (hlip : ∀ t t' : ℝ, ‖velocity r t - velocity r t'‖ ≤ C * |t' - t|)
    (hd : 0 < d) (hne : r ta ≠ r tb)
    (hμ : μ ≤ ‖chordTilt (r ta) (r tb) (velocity r ta)‖) (hdep : 2 * C * d < μ) :
    ∀ x ∈ Set.Icc ta (ta + d),
      ‖chordTilt (r ta) (r tb) (velocity r ta)‖ ^ 2 / 2
        ≤ inner ℝ (chordTilt (r ta) (r tb) (velocity r ta)) (velocity r x) := by
  set n := chordTilt (r ta) (r tb) (velocity r ta) with hn
  have hself : inner ℝ n (velocity r ta) = ‖n‖ ^ 2 := by
    rw [hn]; exact inner_chordTilt_self hne (velocity r ta)
  have hnn : 0 ≤ 2 * C * d := by
    have := mul_nonneg hC hd.le
    linarith
  have hμpos : 0 < μ := lt_of_le_of_lt hnn hdep
  have hnpos : 0 < ‖n‖ := lt_of_lt_of_le hμpos hμ
  have hCd : C * d < ‖n‖ / 2 := by nlinarith [hdep, hμ]
  intro x hx
  have h1 : inner ℝ n (velocity r x)
      = inner ℝ n (velocity r ta) + inner ℝ n (velocity r x - velocity r ta) := by
    rw [inner_sub_right]; ring
  have h2 : ‖velocity r x - velocity r ta‖ ≤ C * (x - ta) := by
    have h := hlip x ta
    have habs : |ta - x| = x - ta := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.1])]
    rwa [habs] at h
  have h3 : -(‖n‖ * (C * (x - ta))) ≤ inner ℝ n (velocity r x - velocity r ta) := by
    have h4 := abs_real_inner_le_norm n (velocity r x - velocity r ta)
    have h5 : ‖n‖ * ‖velocity r x - velocity r ta‖ ≤ ‖n‖ * (C * (x - ta)) :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg n)
    linarith [neg_abs_le (inner ℝ n (velocity r x - velocity r ta))]
  have h6 : C * (x - ta) ≤ C * d := mul_le_mul_of_nonneg_left (by linarith [hx.2]) hC
  have h7 : ‖n‖ * (C * d) ≤ ‖n‖ ^ 2 / 2 := by
    calc ‖n‖ * (C * d) ≤ ‖n‖ * (‖n‖ / 2) := mul_le_mul_of_nonneg_left hCd.le (norm_nonneg n)
      _ = ‖n‖ ^ 2 / 2 := by ring
  have h8 : ‖n‖ * (C * (x - ta)) ≤ ‖n‖ * (C * d) :=
    mul_le_mul_of_nonneg_left h6 (norm_nonneg n)
  nlinarith [h1, hself, h3, h8, h7]

/-- **The tilt slack at the high end** (the mirror of `chordTilt_slack_left`). -/
lemma chordTilt_slack_right {r : ℝ → Space} (hr : IsSmoothKnot r) {ta tb C d μ : ℝ}
    (hC : 0 ≤ C) (hlip : ∀ t t' : ℝ, ‖velocity r t - velocity r t'‖ ≤ C * |t' - t|)
    (hd : 0 < d) (hne : r ta ≠ r tb)
    (hμ : μ ≤ ‖chordTilt (r ta) (r tb) (velocity r tb)‖) (hdep : 2 * C * d < μ) :
    ∀ x ∈ Set.Icc (tb - d) tb,
      ‖chordTilt (r ta) (r tb) (velocity r tb)‖ ^ 2 / 2
        ≤ inner ℝ (chordTilt (r ta) (r tb) (velocity r tb)) (velocity r x) := by
  set n := chordTilt (r ta) (r tb) (velocity r tb) with hn
  have hself : inner ℝ n (velocity r tb) = ‖n‖ ^ 2 := by
    rw [hn]; exact inner_chordTilt_self hne (velocity r tb)
  have hnn : 0 ≤ 2 * C * d := by
    have := mul_nonneg hC hd.le
    linarith
  have hμpos : 0 < μ := lt_of_le_of_lt hnn hdep
  have hnpos : 0 < ‖n‖ := lt_of_lt_of_le hμpos hμ
  have hCd : C * d < ‖n‖ / 2 := by nlinarith [hdep, hμ]
  intro x hx
  have h1 : inner ℝ n (velocity r x)
      = inner ℝ n (velocity r tb) + inner ℝ n (velocity r x - velocity r tb) := by
    rw [inner_sub_right]; ring
  have h2 : ‖velocity r x - velocity r tb‖ ≤ C * (tb - x) := by
    have h := hlip x tb
    have habs : |tb - x| = tb - x := abs_of_nonneg (by linarith [hx.2])
    rwa [habs] at h
  have h3 : -(‖n‖ * (C * (tb - x))) ≤ inner ℝ n (velocity r x - velocity r tb) := by
    have h4 := abs_real_inner_le_norm n (velocity r x - velocity r tb)
    have h5 : ‖n‖ * ‖velocity r x - velocity r tb‖ ≤ ‖n‖ * (C * (tb - x)) :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg n)
    linarith [neg_abs_le (inner ℝ n (velocity r x - velocity r tb))]
  have h6 : C * (tb - x) ≤ C * d := mul_le_mul_of_nonneg_left (by linarith [hx.1]) hC
  have h7 : ‖n‖ * (C * d) ≤ ‖n‖ ^ 2 / 2 := by
    calc ‖n‖ * (C * d) ≤ ‖n‖ * (‖n‖ / 2) := mul_le_mul_of_nonneg_left hCd.le (norm_nonneg n)
      _ = ‖n‖ ^ 2 / 2 := by ring
  have h8 : ‖n‖ * (C * (tb - x)) ≤ ‖n‖ * (C * d) :=
    mul_le_mul_of_nonneg_left h6 (norm_nonneg n)
  nlinarith [h1, hself, h3, h8, h7]

open LeanEval.KnotTheory.Quadrisecant Set in
theorem chamferJunctionOK_of_tilt {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d)
    {α β : ℝ → ℝ} {σ M C μa μb : ℝ} (hW : 0 < Work.Drive.sweepW' D σ) (hα : 0 < α σ)
    (hα2 : 2 * α σ < 1) (hβ : 0 < β σ) (hβ2 : 2 * β σ < 1)
    (hV : r (Work.Drive.taR D σ) ≠ r (Work.Drive.tbR D σ))
    (hMv : ∀ t : ℝ, ‖velocity r t‖ ≤ M) (hC : 0 ≤ C)
    (hlip : ∀ t t' : ℝ, ‖velocity r t - velocity r t'‖ ≤ C * |t' - t|)
    (hμa : μa ≤ ‖Work.Drive.chordTilt (r (Work.Drive.taR D σ)) (r (Work.Drive.tbR D σ))
      (velocity r (Work.Drive.taR D σ))‖)
    (hμb : μb ≤ ‖Work.Drive.chordTilt (r (Work.Drive.taR D σ)) (r (Work.Drive.tbR D σ))
      (velocity r (Work.Drive.tbR D σ))‖)
    (hdepA : 2 * C * (α σ * Work.Drive.sweepW' D σ) < μa)
    (hdepB : 2 * C * (α σ * Work.Drive.sweepW' D σ) < μb)
    (hdepL : M * (α σ * Work.Drive.sweepW' D σ) < ‖r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)‖)
    (hmid : ∀ u : ℝ, Work.Drive.taR D σ + α σ * Work.Drive.sweepW' D σ ≤ u →
      u ≤ Work.Drive.tbR D σ - α σ * Work.Drive.sweepW' D σ →
      r u ∉ openSegment ℝ (r (Work.Drive.taR D σ)) (r (Work.Drive.tbR D σ))) :
    Work.Drive.ChamferJunctionOK r D α β σ := by
  set nA : Space := Work.Drive.chordTilt (r (Work.Drive.taR D σ)) (r (Work.Drive.tbR D σ))
    (velocity r (Work.Drive.taR D σ)) with hnA
  set nB : Space := Work.Drive.chordTilt (r (Work.Drive.taR D σ)) (r (Work.Drive.tbR D σ))
    (velocity r (Work.Drive.tbR D σ)) with hnB
  have hdpos : 0 < α σ * Work.Drive.sweepW' D σ := mul_pos hα hW
  -- the two tilt vectors are orthogonal to the chord
  have hperpA : inner ℝ nA (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)) = 0 := by
    have hsmul : r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)
        = ‖r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)‖ •
            Work.Drive.chordDir (r (Work.Drive.taR D σ)) (r (Work.Drive.tbR D σ)) :=
      (Work.Drive.chordDir_smul _ _ hV).symm
    rw [hsmul, inner_smul_right, hnA,
      Work.Drive.inner_chordTilt_chordDir hV (velocity r (Work.Drive.taR D σ)), mul_zero]
  have hperpB : inner ℝ nB (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)) = 0 := by
    have hsmul : r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)
        = ‖r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)‖ •
            Work.Drive.chordDir (r (Work.Drive.taR D σ)) (r (Work.Drive.tbR D σ)) :=
      (Work.Drive.chordDir_smul _ _ hV).symm
    rw [hsmul, inner_smul_right, hnB,
      Work.Drive.inner_chordTilt_chordDir hV (velocity r (Work.Drive.tbR D σ)), mul_zero]
  -- the tilt slack on both ends of the retained arc
  have hkeyA : ∀ x ∈ Set.Icc (Work.Drive.taR D σ)
      (Work.Drive.taR D σ + α σ * Work.Drive.sweepW' D σ),
      ‖nA‖ ^ 2 / 2 ≤ inner ℝ nA (velocity r x) := by
    have h := chordTilt_slack_left (ta := Work.Drive.taR D σ) (tb := Work.Drive.tbR D σ)
      (C := C) (d := α σ * Work.Drive.sweepW' D σ) (μ := μa) hr hC hlip hdpos hV hμa hdepA
    rwa [← hnA] at h
  have hkeyB : ∀ x ∈ Set.Icc (Work.Drive.tbR D σ - α σ * Work.Drive.sweepW' D σ)
      (Work.Drive.tbR D σ),
      ‖nB‖ ^ 2 / 2 ≤ inner ℝ nB (velocity r x) := by
    have h := chordTilt_slack_right (ta := Work.Drive.taR D σ) (tb := Work.Drive.tbR D σ)
      (C := C) (d := α σ * Work.Drive.sweepW' D σ) (μ := μb) hr hC hlip hdpos hV hμb hdepB
    rwa [← hnB] at h
  have hnnA : 0 ≤ 2 * C * (α σ * Work.Drive.sweepW' D σ) := by
    have := mul_nonneg hC hdpos.le
    linarith
  have hnnB : 0 ≤ 2 * C * (α σ * Work.Drive.sweepW' D σ) := hnnA
  have hnApos : 0 < ‖nA‖ := by
    have h1 : μa ≤ ‖nA‖ := by rw [hnA]; exact hμa
    exact lt_of_lt_of_le (lt_of_le_of_lt hnnA hdepA) h1
  have hnBpos : 0 < ‖nB‖ := by
    have h1 : μb ≤ ‖nB‖ := by rw [hnB]; exact hμb
    exact lt_of_lt_of_le (lt_of_le_of_lt hnnB hdepB) h1
  have hνA : 0 < ‖nA‖ ^ 2 / 2 := div_pos (pow_pos hnApos 2) (by norm_num)
  have hνB : 0 < ‖nB‖ ^ 2 / 2 := div_pos (pow_pos hnBpos 2) (by norm_num)
  -- the arc points at the two ends sit strictly on the correct side of the chord
  have hparMid : Work.Drive.taR D σ + (1 - α σ) * Work.Drive.sweepW' D σ
      = Work.Drive.tbR D σ - α σ * Work.Drive.sweepW' D σ := by
    rw [Work.Drive.sweepW']; ring
  have hposA : 0 < inner ℝ nA
      (r (Work.Drive.taR D σ + α σ * Work.Drive.sweepW' D σ) - r (Work.Drive.taR D σ)) := by
    have hsl := inner_knot_slack_mono (n := nA) (ν := ‖nA‖ ^ 2 / 2)
      (a := Work.Drive.taR D σ) (b := Work.Drive.taR D σ + α σ * Work.Drive.sweepW' D σ)
      hr hkeyA
    have h0 : 0 < ‖nA‖ ^ 2 / 2 *
        ((Work.Drive.taR D σ + α σ * Work.Drive.sweepW' D σ) - Work.Drive.taR D σ) := by
      have he : (Work.Drive.taR D σ + α σ * Work.Drive.sweepW' D σ) - Work.Drive.taR D σ
          = α σ * Work.Drive.sweepW' D σ := by ring
      rw [he]; exact mul_pos hνA hdpos
    have hmem1 : Work.Drive.taR D σ ∈ Set.Icc (Work.Drive.taR D σ)
        (Work.Drive.taR D σ + α σ * Work.Drive.sweepW' D σ) :=
      ⟨le_rfl, by linarith [hdpos]⟩
    have hmem2 : Work.Drive.taR D σ + α σ * Work.Drive.sweepW' D σ ∈
        Set.Icc (Work.Drive.taR D σ) (Work.Drive.taR D σ + α σ * Work.Drive.sweepW' D σ) :=
      ⟨by linarith [hdpos], le_rfl⟩
    have := hsl _ hmem1 _ hmem2 (by linarith [hdpos])
    linarith
  have hposB : 0 < inner ℝ nB
      (r (Work.Drive.tbR D σ) - r (Work.Drive.tbR D σ - α σ * Work.Drive.sweepW' D σ)) := by
    have hsl := inner_knot_slack_mono (n := nB) (ν := ‖nB‖ ^ 2 / 2)
      (a := Work.Drive.tbR D σ - α σ * Work.Drive.sweepW' D σ) (b := Work.Drive.tbR D σ)
      hr hkeyB
    have h0 : 0 < ‖nB‖ ^ 2 / 2 *
        (Work.Drive.tbR D σ - (Work.Drive.tbR D σ - α σ * Work.Drive.sweepW' D σ)) := by
      have he : Work.Drive.tbR D σ - (Work.Drive.tbR D σ - α σ * Work.Drive.sweepW' D σ)
          = α σ * Work.Drive.sweepW' D σ := by ring
      rw [he]; exact mul_pos hνB hdpos
    have hmem1 : Work.Drive.tbR D σ - α σ * Work.Drive.sweepW' D σ ∈
        Set.Icc (Work.Drive.tbR D σ - α σ * Work.Drive.sweepW' D σ) (Work.Drive.tbR D σ) :=
      ⟨le_rfl, by linarith [hdpos]⟩
    have hmem2 : Work.Drive.tbR D σ ∈
        Set.Icc (Work.Drive.tbR D σ - α σ * Work.Drive.sweepW' D σ) (Work.Drive.tbR D σ) :=
      ⟨by linarith [hdpos], le_rfl⟩
    have := hsl _ hmem1 _ hmem2 (by linarith [hdpos])
    linarith
  -- the velocities at the two cut points
  have hvelA : 0 < inner ℝ nA (velocity r (Work.Drive.taR D σ + α σ * Work.Drive.sweepW' D σ)) :=
    lt_of_lt_of_le hνA (hkeyA _ ⟨by linarith [hdpos], le_rfl⟩)
  have hvelB : 0 < inner ℝ nB
      (velocity r (Work.Drive.taR D σ + (1 - α σ) * Work.Drive.sweepW' D σ)) := by
    rw [hparMid]
    exact lt_of_lt_of_le hνB (hkeyB _ ⟨le_rfl, by linarith [hdpos]⟩)
  -- the pairing of the two chord points with the tilt vectors
  have hchordA : ∀ c : ℝ,
      inner ℝ nA ((1 - c) • r (Work.Drive.taR D σ) + c • r (Work.Drive.tbR D σ)
        - r (Work.Drive.taR D σ)) = 0 := by
    intro c
    have h : (1 - c) • r (Work.Drive.taR D σ) + c • r (Work.Drive.tbR D σ)
        - r (Work.Drive.taR D σ) = c • (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)) := by
      module
    rw [h, inner_smul_right, hperpA, mul_zero]
  have hchordB : ∀ c : ℝ,
      inner ℝ nB ((1 - c) • r (Work.Drive.taR D σ) + c • r (Work.Drive.tbR D σ)
        - r (Work.Drive.tbR D σ)) = 0 := by
    intro c
    have h : (1 - c) • r (Work.Drive.taR D σ) + c • r (Work.Drive.tbR D σ)
        - r (Work.Drive.tbR D σ) = (c - 1) • (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)) := by
      module
    rw [h, inner_smul_right, hperpB, mul_zero]
  -- the low cut point of the arc is strictly on the `nA`-positive side
  have hArcLo : 0 < inner ℝ nA (sweepArc' r D σ (α σ) - r (Work.Drive.taR D σ)) := by
    simpa only [sweepArc'] using hposA
  have hChordLo : inner ℝ nA (sweepChord' r D σ (β σ)) = inner ℝ nA (r (Work.Drive.taR D σ)) := by
    have h1 := hchordA (β σ)
    simp only [sweepChord', inner_sub_right] at h1 ⊢
    linarith
  -- the high cut point of the arc is strictly on the `nB`-negative side
  have hArcHi : inner ℝ nB (sweepArc' r D σ (1 - α σ) - r (Work.Drive.tbR D σ)) < 0 := by
    simp only [sweepArc']
    rw [hparMid]
    have h := hposB
    simp only [inner_sub_right] at h ⊢
    linarith
  have hChordHi : inner ℝ nB (sweepChord' r D σ (1 - β σ)) = inner ℝ nB (r (Work.Drive.tbR D σ)) := by
    have h1 := hchordB (1 - β σ)
    simp only [sweepChord', inner_sub_right] at h1 ⊢
    linarith
  have hL : 0 < inner ℝ nB (sweepChord' r D σ (1 - β σ) - sweepArc' r D σ (1 - α σ)) := by
    have h1 : 0 < inner ℝ nB (r (Work.Drive.tbR D σ)) - inner ℝ nB (sweepArc' r D σ (1 - α σ)) := by
      have h := hArcHi
      simp only [inner_sub_right] at h
      linarith
    simp only [inner_sub_right]
    linarith
  refine ⟨hV, hW, hα, hα2, hβ, hβ2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    rw [heq] at hArcLo
    simp only [inner_sub_right] at hArcLo
    linarith [hArcLo, hChordLo]
  · intro heq
    rw [heq] at hArcHi
    simp only [inner_sub_right] at hArcHi
    linarith [hArcHi, hChordHi]
  · intro k hk heq
    have hR : inner ℝ nB ((-k) • velocity r
        (Work.Drive.taR D σ + (1 - α σ) * Work.Drive.sweepW' D σ)) < 0 := by
      rw [inner_smul_right]
      nlinarith [hk, hvelB]
    have := congrArg (fun z : Space => inner ℝ nB z) heq
    linarith [hL, hR, this]
  · intro k hk heq
    have hR : inner ℝ nB (k • (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ))) = 0 := by
      rw [inner_smul_right, hperpB, mul_zero]
    have := congrArg (fun z : Space => inner ℝ nB z) heq
    linarith [hL, hR, this]
  · intro k hk heq
    have h2 : inner ℝ nA (sweepArc' r D σ (α σ) - sweepChord' r D σ (β σ)) > 0 := by
      have h := hArcLo
      simp only [inner_sub_right] at h ⊢
      linarith [h, hChordLo]
    have hR : inner ℝ nA (k • (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ))) = 0 := by
      rw [inner_smul_right, hperpA, mul_zero]
    have := congrArg (fun z : Space => inner ℝ nA z) heq
    rw [this, hR] at h2
    linarith
  · intro k hk heq
    have h2 : inner ℝ nA (sweepArc' r D σ (α σ) - sweepChord' r D σ (β σ)) > 0 := by
      have h := hArcLo
      simp only [inner_sub_right] at h ⊢
      linarith [h, hChordLo]
    have hR : inner ℝ nA ((-k) • velocity r
        (Work.Drive.taR D σ + α σ * Work.Drive.sweepW' D σ)) < 0 := by
      rw [inner_smul_right]
      nlinarith [hk, hvelA]
    have := congrArg (fun z : Space => inner ℝ nA z) heq
    linarith [h2, hR, this]

end Work.Drive
