import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs

/-!
# The chamfer–chord corner of the sweep is never a `π`-corner

The *regularity* clause of the chord sweep (`Work.Drive.sweepFamVelNz`: every slice of the doubly
smoothed sweep has nonvanishing velocity) is, by the proved reduction
`Work.Drive.velNz_velocity_ne_zero_of_avg_chord`, a statement about the *averaged chords* of the raw
chamfered loop: the blurred velocity is a positive weighted average of the branch velocities of the
raw loop over a small box, so it can vanish only if the box's branch directions positively cancel.
At a corner of the chamfered loop only the two adjacent branches occur, and a positive combination
of two vectors vanishes exactly when the two vectors are *oppositely* proportional.  This file
proves that at the corner where the first chamfer meets the closing chord this never happens for
small `lam`.

Writing

* `lam := lam`, `W := sweepW' D σ`, `A := r (taR D σ)`, `B := r (tbR D σ)`, `d := B - A`,
* `P := r (tbR D σ - lam * W)` (the arc's last retained point) and
  `Q := B - lam • d` (the chord point at fraction `1 - lam`),

the loop traverses the chamfer with velocity proportional to `Q - P` and the chord with velocity
proportional to `-d`.  So the cancellation needs `Q - P` to be a *positive* multiple of `d`, i.e.

  `∃ c > 0,  Q - P = c lam d`,  equivalently  `r (tbR D σ - lam W) = B - (lam (1 + c)) • d`.

`Work.Drive.chamferChord_no_piCorner` shows that this is impossible as soon as
`lam * (M * Wmax) < δ`, where `M` is a Lipschitz constant for `r` and `δ` a lower bound for the
chord length `‖d‖` on the window:

* if `lam (1 + c) < 1` then `r (tbR D σ - lam W) = (1 - t) • A + t • B` with
  `t = 1 - lam (1 + c) ∈ (0,1)` is a knot point **strictly inside** the chord, which the
  `O`-avoidance hypothesis `havoid` forbids (`IsMiddleOnChord`);
* if `lam (1 + c) ≥ 1` then `(1 + c) ‖d‖ ≤ M W` (from the Lipschitz bound on the arc
  `[tbR - lam W, tbR]`, whose arclength is `lam W`), hence `δ ≤ ‖d‖ ≤ lam (M Wmax)` (dividing by
  `1 + c ≥ 1/lam`) — contradicting `lam (M Wmax) < δ`.

The second case is the "beyond `A`" case of the analysis in
`Submission/Work/Drive/NOTES_middleClean_route.md`; the first is the case killed by `havoid`.  The
mirror statement at the other end of the retained arc (the second chamfer against the chord) is the
same with `tbR ↦ taR` and `1 - lam ↦ lam`.

`Work.Drive.sweepFamChord_lower_bound` supplies the lower bound `δ` (compactness of the window plus
injectivity of the knot), and `Work.Drive.chamferChord_no_piCorner_window` combines the two, with
the threshold `L` written explicitly in terms of `δ`, `M` and `period`.  Both are free of `sorry`,
`axiom` and `admit`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- `clampI` is continuous. -/
lemma continuous_clampI : Continuous clampI := by
  have h : clampI = fun x : ℝ =>
      (⟨min 1 (max 0 x), ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩⟩ :
        Set.Icc (0 : ℝ) 1) := rfl
  rw [h]
  exact Continuous.subtype_mk (continuous_const.min (continuous_const.max continuous_id)) _

/-- The retained width at an interior sweep parameter lies in `(0, period)`. -/
lemma sweepW'_pos_lt {d : BandArcData} (D : SweepData d) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) : 0 < sweepW' D σ ∧ sweepW' D σ < period := by
  have hclamp : clampI σ = (⟨σ, ⟨hσ0.le, hσ1.le⟩⟩ : Set.Icc (0 : ℝ) 1) := by
    refine Subtype.ext ?_
    simp only [clampI, min_eq_right hσ1.le, max_eq_right hσ0.le]
  have h : sweepW' D σ = sweepW D ⟨σ, ⟨hσ0.le, hσ1.le⟩⟩ := by
    simp only [sweepW', sweepW, tbR, taR, hclamp]
  rw [h]
  exact sweepW_pos_lt D ⟨σ, ⟨hσ0.le, hσ1.le⟩⟩ ⟨hσ0, hσ1⟩

/-- **The chord length is bounded below on a compact window.**  For a smooth knot `r` and a band
arc whose two branches are distinct at every interior parameter, the length of the chord
`r (tbR D σ) - r (taR D σ)` has a positive lower bound on `σ ∈ [a,b] ⊂ (0,1)`. -/
theorem sweepFamChord_lower_bound {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Set.Icc a b, δ ≤ ‖r (tbR D σ) - r (taR D σ)‖ := by
  have hcont : Continuous (fun σ : ℝ => ‖r (tbR D σ) - r (taR D σ)‖) := by
    refine Continuous.norm ((hr.smooth.continuous.comp ?_).sub (hr.smooth.continuous.comp ?_))
    · exact D.cont_tb.comp continuous_clampI
    · exact D.cont_ta.comp continuous_clampI
  have hne : (Set.Icc a b).Nonempty := ⟨a, le_rfl, hab.le⟩
  obtain ⟨σ₀, hσ₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont.continuousOn
  refine ⟨‖r (tbR D σ₀) - r (taR D σ₀)‖, ?_, fun σ hσ => hmin hσ⟩
  by_contra hzero
  push_neg at hzero
  have heq : r (tbR D σ₀) = r (taR D σ₀) :=
    sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))
  have hσ0 : 0 < σ₀ := lt_of_lt_of_le ha hσ₀.1
  have hσ1 : σ₀ < 1 := lt_of_le_of_lt hσ₀.2 hb
  set s : Set.Icc (0 : ℝ) 1 := ⟨σ₀, ⟨hσ0.le, hσ1.le⟩⟩ with hs
  have hclamp : clampI σ₀ = s := by
    refine Subtype.ext ?_
    simp only [clampI, hs, min_eq_right hσ1.le, max_eq_right hσ0.le]
  have hA : knotMap r (d.a s) = r (taR D σ₀) := by
    rw [← D.lift_a s, knotMap_coe' hr.periodic]
    congr 1
    exact congrArg (fun y : Set.Icc (0 : ℝ) 1 => ((D.ta y : ℝ))) hclamp.symm
  have hB : knotMap r (d.b s) = r (tbR D σ₀) := by
    rw [← D.lift_b s, knotMap_coe' hr.periodic]
    congr 1
    exact congrArg (fun y : Set.Icc (0 : ℝ) 1 => ((D.tb y : ℝ))) hclamp.symm
  refine d.offdiag s (ne_of_gt hσ0) (ne_of_lt hσ1) ?_
  apply knotMap_injective hr
  rw [hA, hB]
  exact heq.symm

/-- **The chamfer/chord corner is not a `π`-corner.**  Let `r` be a `period`-periodic curve which is
`M`-Lipschitz, `D` a sweep lift of a band arc whose chords avoid `O` at `σ`, `δ` a lower bound for
the chord length at `σ` and `Wmax` an upper bound for the retained width `sweepW' D σ`.  If
`0 < lam` with `lam * (M * Wmax) < δ`, then the chamfer's direction `Q - P` is not a positive
multiple of the chord's direction `d`: there is no `c > 0` with
`r (tbR D σ - lam * W) = r (tbR D σ) - (lam (1 + c)) • (r (tbR D σ) - r (taR D σ))`. -/
theorem chamferChord_no_piCorner {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (hper : Function.Periodic r period)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    {σ lam δ M Wmax : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hM0 : 0 ≤ M) (hM : ∀ x y : ℝ, ‖r x - r y‖ ≤ M * |x - y|)
    (hd : δ ≤ ‖r (tbR D σ) - r (taR D σ)‖)
    (hW : sweepW' D σ ≤ Wmax)
    (hlam0 : 0 < lam) (hlamδ : lam * (M * Wmax) < δ) :
    ¬ ∃ c : ℝ, 0 < c ∧ r (tbR D σ - lam * sweepW' D σ)
        = r (tbR D σ) - (lam * (1 + c)) • (r (tbR D σ) - r (taR D σ)) := by
  set s : Set.Icc (0 : ℝ) 1 := ⟨σ, ⟨hσ0.le, hσ1.le⟩⟩ with hs
  have hclamp : clampI σ = s := by
    refine Subtype.ext ?_
    simp only [clampI, hs, min_eq_right hσ1.le, max_eq_right hσ0.le]
  have hWpos : 0 < sweepW' D σ := (sweepW'_pos_lt D hσ0 hσ1).1
  have hmid : ¬ ∃ m : AddCircle period, IsMiddleOnChord r (d.a s) (d.b s) m := by
    intro ⟨m, hm⟩
    have h := havoid s (ne_of_gt hσ0) (ne_of_lt hσ1)
    simp only [trisecantSet, Set.mem_ofPred_eq, HasMiddleOnClass] at h
    exact h ⟨m, ⟨(d.a s, d.b s), d.offdiag s (ne_of_gt hσ0) (ne_of_lt hσ1)⟩, rfl, hm⟩
  rintro ⟨c, hc, hrel⟩
  have hc1 : 0 < 1 + c := by linarith
  have hlam1c : 0 < lam * (1 + c) := mul_pos hlam0 hc1
  have hrel' : r (tbR D σ) - r (tbR D σ - lam * sweepW' D σ)
      = (lam * (1 + c)) • (r (tbR D σ) - r (taR D σ)) := by
    rw [hrel]
    exact sub_sub_cancel _ _
  have hnorm : ‖r (tbR D σ) - r (tbR D σ - lam * sweepW' D σ)‖
      = (lam * (1 + c)) * ‖r (tbR D σ) - r (taR D σ)‖ := by
    rw [hrel', norm_smul, Real.norm_eq_abs, abs_of_pos hlam1c]
  have hlip : ‖r (tbR D σ) - r (tbR D σ - lam * sweepW' D σ)‖ ≤ M * (lam * sweepW' D σ) := by
    have h := hM (tbR D σ) (tbR D σ - lam * sweepW' D σ)
    have habs : |tbR D σ - (tbR D σ - lam * sweepW' D σ)| = lam * sweepW' D σ := by
      rw [sub_sub_cancel, abs_of_pos (mul_pos hlam0 hWpos)]
    rwa [habs] at h
  rcases lt_or_ge (lam * (1 + c)) 1 with hcase | hcase
  · -- the arc's last retained point lies strictly inside the chord: contradict `havoid`
    have hz : r (tbR D σ - lam * sweepW' D σ)
        ∈ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) := by
      rw [openSegment_eq_image]
      refine ⟨1 - lam * (1 + c), ⟨by linarith, by linarith⟩, ?_⟩
      change (1 - (1 - lam * (1 + c))) • r (taR D σ)
          + (1 - lam * (1 + c)) • r (tbR D σ) = r (tbR D σ - lam * sweepW' D σ)
      rw [hrel]
      have key : (1 - (1 - lam * (1 + c))) • r (taR D σ)
            + (1 - lam * (1 + c)) • r (tbR D σ)
          = r (tbR D σ) - (lam * (1 + c)) • (r (tbR D σ) - r (taR D σ)) := by
        rw [show (1 : ℝ) - (1 - lam * (1 + c)) = lam * (1 + c) by ring,
          show (1 - lam * (1 + c)) • r (tbR D σ)
              = r (tbR D σ) - (lam * (1 + c)) • r (tbR D σ) by rw [sub_smul, one_smul],
          smul_sub]
        abel
      exact key
    have hA : knotMap r (d.a s) = r (taR D σ) := by
      rw [← D.lift_a s, knotMap_coe' hper]
      congr 1
      exact congrArg (fun y : Set.Icc (0 : ℝ) 1 => ((D.ta y : ℝ))) hclamp.symm
    have hB : knotMap r (d.b s) = r (tbR D σ) := by
      rw [← D.lift_b s, knotMap_coe' hper]
      congr 1
      exact congrArg (fun y : Set.Icc (0 : ℝ) 1 => ((D.tb y : ℝ))) hclamp.symm
    refine hmid ⟨((tbR D σ - lam * sweepW' D σ : ℝ) : AddCircle period), ?_⟩
    simp only [IsMiddleOnChord]
    rw [knotMap_coe' hper, hA, hB]
    exact hz
  · -- otherwise the chord's far endpoint is too far away for the Lipschitz bound
    have h1 : (lam * (1 + c)) * ‖r (tbR D σ) - r (taR D σ)‖
        ≤ M * (lam * sweepW' D σ) := by
      rw [← hnorm]
      exact hlip
    have h2 : (1 + c) * ‖r (tbR D σ) - r (taR D σ)‖ ≤ M * sweepW' D σ := by
      have h3 : lam * ((1 + c) * ‖r (tbR D σ) - r (taR D σ)‖)
          ≤ lam * (M * sweepW' D σ) := by nlinarith [h1]
      exact (mul_le_mul_iff_right₀ hlam0).mp h3
    have h4 : 1 / (1 + c) ≤ lam := by
      rw [div_le_iff₀ hc1]; linarith
    have h5 : M * sweepW' D σ ≤ M * Wmax := mul_le_mul_of_nonneg_left hW hM0
    have h6 : ‖r (tbR D σ) - r (taR D σ)‖ ≤ lam * (M * Wmax) := by
      calc ‖r (tbR D σ) - r (taR D σ)‖
          = (1 / (1 + c)) * ((1 + c) * ‖r (tbR D σ) - r (taR D σ)‖) := by field_simp
        _ ≤ lam * (M * Wmax) := mul_le_mul h4 (h2.trans h5) (by positivity) hlam0.le
    linarith [hd, hlamδ, h6]

/-- **The chamfer/chord corner is never a `π`-corner, uniformly on a compact window.**  For a
smooth knot `r`, a band arc whose chords avoid `O` on the window `[a,b] ⊂ (0,1)`, and any Lipschitz
constant `M` of `r`, there is `L > 0` such that for every `σ ∈ [a,b]` and every `lam ∈ (0,L]` the
chamfer direction is not a positive multiple of the chord direction. -/
theorem chamferChord_no_piCorner_window {r : ℝ → Space} (hr : IsSmoothKnot r)
    {d : BandArcData} (D : SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    {a b M : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hM0 : 0 ≤ M) (hM : ∀ x y : ℝ, ‖r x - r y‖ ≤ M * |x - y|) :
    ∃ L : ℝ, 0 < L ∧ ∀ σ ∈ Set.Icc a b, ∀ lam : ℝ, 0 < lam → lam ≤ L →
      ¬ ∃ c : ℝ, 0 < c ∧ r (tbR D σ - lam * sweepW' D σ)
        = r (tbR D σ) - (lam * (1 + c)) • (r (tbR D σ) - r (taR D σ)) := by
  obtain ⟨δ, hδpos, hδ⟩ := sweepFamChord_lower_bound hr D ha hab hb
  set L : ℝ := δ / (M * period + 1) with hL
  have hden : 0 < M * period + 1 := by have := period_pos; nlinarith
  have hLpos : 0 < L := by rw [hL]; positivity
  refine ⟨L, hLpos, fun σ hσ lam hlam0 hlamL => ?_⟩
  have hσ0 : 0 < σ := lt_of_lt_of_le ha hσ.1
  have hσ1 : σ < 1 := lt_of_le_of_lt hσ.2 hb
  refine chamferChord_no_piCorner (Wmax := period) D hr.periodic havoid hσ0 hσ1 hM0 hM
    (hδ σ hσ) (sweepW'_pos_lt D hσ0 hσ1).2.le hlam0 ?_
  · have hbound : lam * (M * period) ≤ L * (M * period) :=
      mul_le_mul_of_nonneg_right hlamL (mul_nonneg hM0 period_pos.le)
    have h2 : L * (M * period) < δ := by
      have h1 : L * (M * period) = δ * (M * period) / (M * period + 1) := by
        rw [hL]; ring
      rw [h1, div_lt_iff₀ hden]
      nlinarith [hδpos]
    linarith

/-- **Positive combinations of two non-opposite vectors are bounded below, stably.**  If `a` and
`b` are not oppositely proportional (`t • a + (1 - t) • b ≠ 0` for `t ∈ [0,1]`), then there are
`c > 0` and a neighbourhood of the pair `(a,b)` in which every positive combination
`s • a' + t • b'` (`s, t ≥ 0`, `s + t = 1`) has norm at least `c`.

This is the abstract step that turns the *corner* statement `chamferChord_no_piCorner` (two branch
velocities are never oppositely proportional) into a positive lower bound for the blurred velocity,
which is a positive combination of the velocities of the two branches met by the window. -/
theorem posComb_bound_of_not_opposite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E} (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t • a + (1 - t) • b ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ a' b' : E, ‖a' - a‖ ≤ ε → ‖b' - b‖ ≤ ε →
      ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t = 1 → c ≤ ‖s • a' + t • b'‖ := by
  have hKc : IsCompact {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1} := by
    have himg : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1}
        = (fun s : ℝ => (s, 1 - s)) '' (Set.Icc 0 1) := by
      ext p; constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨p.1, ⟨h1, by linarith [h3, h2]⟩, Prod.ext rfl (by linarith [h3])⟩
      · rintro ⟨s, hs, hfl⟩
        rw [← hfl]
        exact ⟨hs.1, by linarith [hs.2], by ring⟩
    rw [himg]
    exact isCompact_Icc.image (by continuity)
  have hKne : ({p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1} : Set (ℝ × ℝ)).Nonempty :=
    ⟨(1, 0), by norm_num⟩
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ‖p.1 • a + p.2 • b‖)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1} :=
    ((continuous_fst.smul continuous_const).add
      (continuous_snd.smul continuous_const)).norm.continuousOn
  obtain ⟨p₀, hp₀, hmin⟩ := hKc.exists_isMinOn hKne hcont
  have hple : p₀.1 ≤ 1 := by linarith [hp₀.2.2, hp₀.2.1]
  have hpos : 0 < ‖p₀.1 • a + p₀.2 • b‖ := by
    rw [norm_pos_iff]
    intro hzero
    refine h p₀.1 hp₀.1 hple ?_
    have : p₀.2 = 1 - p₀.1 := by linarith [hp₀.2.2]
    rw [this] at hzero
    exact hzero
  set m : ℝ := ‖p₀.1 • a + p₀.2 • b‖ with hm
  have hmin' : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t = 1 → m ≤ ‖s • a + t • b‖ := by
    intro s t hs ht hst
    exact hmin (show (s, t) ∈ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1}
      from ⟨hs, ht, hst⟩)
  refine ⟨m / 2, by positivity, m / 2, by positivity, fun a' b' ha' hb' s t hs ht hst => ?_⟩
  have hdecomp : s • a' + t • b' = (s • a + t • b) + (s • (a' - a) + t • (b' - b)) := by module
  have h2 : ‖s • (a' - a) + t • (b' - b)‖ ≤ s * (m / 2) + t * (m / 2) := by
    calc ‖s • (a' - a) + t • (b' - b)‖ ≤ ‖s • (a' - a)‖ + ‖t • (b' - b)‖ := norm_add_le _ _
      _ = s * ‖a' - a‖ + t * ‖b' - b‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs,
            abs_of_nonneg ht]
      _ ≤ s * (m / 2) + t * (m / 2) :=
          add_le_add (mul_le_mul_of_nonneg_left ha' hs) (mul_le_mul_of_nonneg_left hb' ht)
  have h3 : s * (m / 2) + t * (m / 2) = m / 2 := by rw [← add_mul, hst, one_mul]
  have h5 : m ≤ ‖s • a + t • b‖ := hmin' s t hs ht hst
  have h8 := norm_sub_le ((s • a + t • b) + (s • (a' - a) + t • (b' - b)))
    (s • (a' - a) + t • (b' - b))
  rw [add_sub_cancel_right] at h8
  rw [hdecomp]
  linarith [h5, h2, h3, h8]

end Work.Drive
