import Mathlib
import Submission.Work.Drive.chamferJunctionDefs

/-!
# `ChamferJunctionOK` from the two ball bounds

(Implements §1 of `NOTES_LEAD_scheduledBlur.md`, the lemma `chamferJunctionOK_of_ball`.)

`Work.Drive.ChamferJunctionOK r D α β σ` says that the four junctions of the scheduled chamfer
loop at the slice `σ` are non-degenerate: the four junction points are pairwise distinct and at no
junction does the outgoing direction equal `-k` times the incoming one (`k > 0`).

The hypotheses of the present lemma are the *analytic* inputs of the lead's design:

* `hsum` and `hmid` (the two connectors are separated by the chord; the retained arc carries no
  middle of the chord) kill the two junctions **J2/J3** — the ones involving the chord direction
  `V = r (tbR) - r (taR)`: supposing, e.g., `sweepArc' (α σ) - sweepChord' (β σ) = k • V` puts the
  cut arc point on the *ray* `A + t V` with `0 < b + k < 1` (the strict inequality coming from
  `hsum`), hence strictly inside the open chord, contradicting `hmid`;
* `hballA`/`hballB` and the radial signs `hradA`/`hradB` kill the two junctions **J1/J4** — the ones
  involving the tangent: if, e.g., `sweepArc' (α σ) - sweepChord' (β σ) = -k • v` (`v` the velocity
  at the cut arc point) then `|chordPoint - A|² = |P - A|² + 2k ⟪P - A, v⟫ + k² |v|² > |P - A|²`,
  i.e. the chord point is *farther* from `A` than the arc point is, contradicting the ball bound.
  Note that the `k² |v|²` term supplies the strictness, so only the *weak* radial signs are needed.

The proof of the second group of junctions uses `velocity … ≠ 0`, which for a smooth knot is
`IsSmoothKnot.regular`.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant Set

/-! ## The abstract core of the two "ball" junctions -/

/-- **J4 core.**  If the chord point `C = A + b • (B - A)` lies on the *forward tangent ray* of the
arc at `P` (`C = P + k • v`), then `|C - A| > |P - A|`: the ball bound `b |B - A| ≤ |P - A|`
together with the radial sign `0 ≤ ⟪P - A, v⟫` is contradicted as soon as `v ≠ 0`. -/
private lemma cjb_tail_contra {A B P C v : Space} {b k : ℝ} (hb : 0 < b) (hk : 0 < k)
    (hv : v ≠ 0) (hC : C - A = b • (B - A))
    (hball : b * ‖B - A‖ ≤ ‖P - A‖) (hrad : 0 ≤ inner ℝ (P - A) v)
    (hP : P - C = (-k) • v) : False := by
  have hC' : C = P + k • v := by
    calc C = P - (P - C) := by abel
      _ = P - (-k) • v := by rw [hP]
      _ = P + k • v := by rw [neg_smul]; abel
  have h3 : (P - A) + k • v = b • (B - A) := by rw [← hC, hC']; abel
  have h4 : ‖(P - A) + k • v‖ ^ 2
      = ‖P - A‖ ^ 2 + 2 * k * inner ℝ (P - A) v + k ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    ring
  have h5 : ‖(P - A) + k • v‖ ^ 2 = (b * ‖B - A‖) ^ 2 := by
    rw [h3, norm_smul, Real.norm_eq_abs, abs_of_pos hb]
  have h6 : (b * ‖B - A‖) ^ 2 ≤ ‖P - A‖ ^ 2 := pow_le_pow_left₀ (by positivity) hball 2
  have h7 : ‖P - A‖ ^ 2 < ‖(P - A) + k • v‖ ^ 2 := by
    rw [h4]
    have h1 : 0 ≤ 2 * k * inner ℝ (P - A) v := by nlinarith [hrad, hk]
    have h2 : 0 < k ^ 2 * ‖v‖ ^ 2 := by
      have hv' : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) 2
      have hk' : 0 < k ^ 2 := pow_pos hk 2
      positivity
    linarith
  linarith [h5, h6, h7]

/-- **J1 core.**  If the chord point `C = B - b • (B - A)` lies on the *backward tangent ray* of
the arc at `Q` (`C = Q - k • v`), then `|C - B| > |Q - B|`, contradicting the ball bound
`b |B - A| ≤ |Q - B|` together with the radial sign `⟪Q - B, v⟫ ≤ 0`. -/
private lemma cjb_head_contra {A B Q C v : Space} {b k : ℝ} (hb : 0 < b) (hk : 0 < k)
    (hv : v ≠ 0) (hC : C - B = -(b • (B - A)))
    (hball : b * ‖B - A‖ ≤ ‖Q - B‖) (hrad : inner ℝ (Q - B) v ≤ 0)
    (hQ : C - Q = (-k) • v) : False := by
  have hC' : C = Q - k • v := by
    calc C = Q + (C - Q) := by abel
      _ = Q + (-k) • v := by rw [hQ]
      _ = Q - k • v := by rw [neg_smul]; abel
  have h3 : (Q - B) - k • v = -(b • (B - A)) := by rw [← hC, hC']; abel
  have h4 : ‖(Q - B) - k • v‖ ^ 2
      = ‖Q - B‖ ^ 2 - 2 * k * inner ℝ (Q - B) v + k ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    ring
  have h5 : ‖(Q - B) - k • v‖ ^ 2 = (b * ‖B - A‖) ^ 2 := by
    rw [h3, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hb]
  have h6 : (b * ‖B - A‖) ^ 2 ≤ ‖Q - B‖ ^ 2 := pow_le_pow_left₀ (by positivity) hball 2
  have h7 : ‖Q - B‖ ^ 2 < ‖(Q - B) - k • v‖ ^ 2 := by
    rw [h4]
    have h1 : 0 ≤ -2 * k * inner ℝ (Q - B) v := by nlinarith [hrad, hk]
    have h2 : 0 < k ^ 2 * ‖v‖ ^ 2 := by
      have hv' : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) 2
      have hk' : 0 < k ^ 2 := pow_pos hk 2
      positivity
    linarith
  linarith [h5, h6, h7]

/-! ## The four junctions in the language of the sweep -/

/-- **J4**: the tail connector does not point along the backward tangent at its arc endpoint. -/
private lemma cjb_tail_not_reverse {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {σ a b k : ℝ} {v : Space} (hb : 0 < b) (hk : 0 < k) (hv : v ≠ 0)
    (hballA : b * ‖r (tbR D σ) - r (taR D σ)‖ ≤ ‖sweepArc' r D σ a - r (taR D σ)‖)
    (hradA : 0 ≤ inner ℝ (sweepArc' r D σ a - r (taR D σ)) v) :
    sweepArc' r D σ a - sweepChord' r D σ b ≠ (-k) • v := by
  intro heq
  refine cjb_tail_contra (A := r (taR D σ)) (B := r (tbR D σ)) (P := sweepArc' r D σ a)
    (C := sweepChord' r D σ b) (v := v) hb hk hv ?_ hballA hradA heq
  rw [sweepChord']; module

/-- **J1**: the head connector does not point along the backward tangent at its arc endpoint. -/
private lemma cjb_head_not_reverse {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {σ a b k : ℝ} {v : Space} (hb : 0 < b) (hk : 0 < k) (hv : v ≠ 0)
    (hballB : b * ‖r (tbR D σ) - r (taR D σ)‖ ≤ ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖)
    (hradB : inner ℝ (sweepArc' r D σ (1 - a) - r (tbR D σ)) v ≤ 0) :
    sweepChord' r D σ (1 - b) - sweepArc' r D σ (1 - a) ≠ (-k) • v := by
  intro heq
  refine cjb_head_contra (A := r (taR D σ)) (B := r (tbR D σ)) (Q := sweepArc' r D σ (1 - a))
    (C := sweepChord' r D σ (1 - b)) (v := v) hb hk hv ?_ hballB hradB heq
  rw [sweepChord']; module

/-- **J3**: the tail connector does not point along the chord direction `V`; then the cut arc
point would lie strictly inside the open chord. -/
private lemma cjb_tail_not_V {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {σ a b k : ℝ} (hb : 0 < b) (hAne : r (taR D σ) ≠ r (tbR D σ))
    (hsum : ‖sweepArc' r D σ a - r (taR D σ)‖ + ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖
      < ‖r (tbR D σ) - r (taR D σ)‖)
    (hmid : ∀ u : ℝ, taR D σ + a * sweepW' D σ ≤ u → u ≤ tbR D σ - a * sweepW' D σ →
      r u ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ)))
    (hwin : taR D σ + a * sweepW' D σ ≤ tbR D σ - a * sweepW' D σ) (hk : 0 < k) :
    sweepArc' r D σ a - sweepChord' r D σ b ≠ k • (r (tbR D σ) - r (taR D σ)) := by
  intro heq
  have hVne : r (tbR D σ) - r (taR D σ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hAne)
  have hLpos : 0 < ‖r (tbR D σ) - r (taR D σ)‖ := norm_pos_iff.mpr hVne
  have hC : sweepChord' r D σ b - r (taR D σ) = b • (r (tbR D σ) - r (taR D σ)) := by
    rw [sweepChord']; module
  have hPA : sweepArc' r D σ a - r (taR D σ) = (k + b) • (r (tbR D σ) - r (taR D σ)) := by
    have h : sweepArc' r D σ a - r (taR D σ)
        = (sweepArc' r D σ a - sweepChord' r D σ b)
          + (sweepChord' r D σ b - r (taR D σ)) := by abel
    rw [h, heq, hC, ← add_smul]
  have hnorm : ‖sweepArc' r D σ a - r (taR D σ)‖
      = (k + b) * ‖r (tbR D σ) - r (taR D σ)‖ := by
    rw [hPA, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < k + b)]
  have hlt : (k + b) * ‖r (tbR D σ) - r (taR D σ)‖ < ‖r (tbR D σ) - r (taR D σ)‖ := by
    have h2 : (0:ℝ) ≤ ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖ := norm_nonneg _
    nlinarith [hsum, hnorm, h2]
  have hkb1 : k + b < 1 := by nlinarith [hlt, hLpos]
  have hPseg : sweepArc' r D σ a ∈ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) := by
    rw [openSegment_eq_image]
    refine ⟨k + b, ⟨by linarith, hkb1⟩, ?_⟩
    have h' : (1 - (k + b)) • r (taR D σ) + (k + b) • r (tbR D σ) = sweepArc' r D σ a := by
      rw [show (1 - (k + b)) • r (taR D σ) + (k + b) • r (tbR D σ)
          = r (taR D σ) + (k + b) • (r (tbR D σ) - r (taR D σ)) from by module, ← hPA]
      abel
    exact h'
  exact hmid (taR D σ + a * sweepW' D σ) le_rfl hwin (by simpa only [sweepArc'] using hPseg)

/-- **J2**: the head connector does not point along the chord direction `V`; then the cut arc
point would lie strictly inside the open chord. -/
private lemma cjb_head_not_V {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {σ a b k : ℝ} (hb : 0 < b) (hAne : r (taR D σ) ≠ r (tbR D σ))
    (hsum : ‖sweepArc' r D σ a - r (taR D σ)‖ + ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖
      < ‖r (tbR D σ) - r (taR D σ)‖)
    (hmid : ∀ u : ℝ, taR D σ + a * sweepW' D σ ≤ u → u ≤ tbR D σ - a * sweepW' D σ →
      r u ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ)))
    (hwin : taR D σ + a * sweepW' D σ ≤ tbR D σ - a * sweepW' D σ) (hk : 0 < k) :
    sweepChord' r D σ (1 - b) - sweepArc' r D σ (1 - a) ≠ k • (r (tbR D σ) - r (taR D σ)) := by
  intro heq
  have hVne : r (tbR D σ) - r (taR D σ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hAne)
  have hLpos : 0 < ‖r (tbR D σ) - r (taR D σ)‖ := norm_pos_iff.mpr hVne
  have hC2 : sweepChord' r D σ (1 - b) - r (taR D σ)
      = (1 - b) • (r (tbR D σ) - r (taR D σ)) := by
    rw [sweepChord']; module
  have hQA : sweepArc' r D σ (1 - a) - r (taR D σ)
      = (1 - b - k) • (r (tbR D σ) - r (taR D σ)) := by
    have h : sweepArc' r D σ (1 - a) - r (taR D σ)
        = (sweepChord' r D σ (1 - b) - r (taR D σ))
          - (sweepChord' r D σ (1 - b) - sweepArc' r D σ (1 - a)) := by abel
    rw [h, hC2, heq]
    module
  have hQB : sweepArc' r D σ (1 - a) - r (tbR D σ)
      = (-(b + k)) • (r (tbR D σ) - r (taR D σ)) := by
    have h : sweepArc' r D σ (1 - a) - r (tbR D σ)
        = (sweepArc' r D σ (1 - a) - r (taR D σ)) - (r (tbR D σ) - r (taR D σ)) := by abel
    rw [h, hQA]
    module
  have hnormQ : ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖
      = (b + k) * ‖r (tbR D σ) - r (taR D σ)‖ := by
    rw [hQB, norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith : -(b + k) < 0)]
    ring
  have hlt : (b + k) * ‖r (tbR D σ) - r (taR D σ)‖ < ‖r (tbR D σ) - r (taR D σ)‖ := by
    have h2 : (0:ℝ) ≤ ‖sweepArc' r D σ a - r (taR D σ)‖ := norm_nonneg _
    nlinarith [hsum, hnormQ, h2]
  have hkb1 : b + k < 1 := by nlinarith [hlt, hLpos]
  have hQseg : sweepArc' r D σ (1 - a) ∈ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) := by
    rw [openSegment_eq_image]
    refine ⟨1 - b - k, ⟨by linarith, by linarith⟩, ?_⟩
    have h' : (1 - (1 - b - k)) • r (taR D σ) + (1 - b - k) • r (tbR D σ)
        = sweepArc' r D σ (1 - a) := by
      rw [show (1 - (1 - b - k)) • r (taR D σ) + (1 - b - k) • r (tbR D σ)
          = r (taR D σ) + (1 - b - k) • (r (tbR D σ) - r (taR D σ)) from by module, ← hQA]
      abel
    exact h'
  have hQeq : sweepArc' r D σ (1 - a) = r (tbR D σ - a * sweepW' D σ) := by
    show r (taR D σ + (1 - a) * sweepW' D σ) = r (tbR D σ - a * sweepW' D σ)
    congr 1
    rw [show sweepW' D σ = tbR D σ - taR D σ from rfl]
    ring
  rw [hQeq] at hQseg
  exact hmid (tbR D σ - a * sweepW' D σ) hwin le_rfl hQseg

/-! ## The lemma -/

open LeanEval.KnotTheory.Quadrisecant Set in
theorem chamferJunctionOK_of_ball {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d)
    {α β : ℝ → ℝ} {σ : ℝ} (hW : 0 < Work.Drive.sweepW' D σ) (hα : 0 < α σ)
    (hα2 : 2 * α σ < 1) (hβ : 0 < β σ) (hβ2 : 2 * β σ < 1)
    (hV : r (Work.Drive.taR D σ) ≠ r (Work.Drive.tbR D σ))
    (hballA : β σ * ‖r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)‖ ≤
      ‖Work.Drive.sweepArc' r D σ (α σ) - r (Work.Drive.taR D σ)‖)
    (hballB : β σ * ‖r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)‖ ≤
      ‖Work.Drive.sweepArc' r D σ (1 - α σ) - r (Work.Drive.tbR D σ)‖)
    (hsum : ‖Work.Drive.sweepArc' r D σ (α σ) - r (Work.Drive.taR D σ)‖ +
      ‖Work.Drive.sweepArc' r D σ (1 - α σ) - r (Work.Drive.tbR D σ)‖ <
      ‖r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)‖)
    (hmid : ∀ u : ℝ, Work.Drive.taR D σ + α σ * Work.Drive.sweepW' D σ ≤ u →
      u ≤ Work.Drive.tbR D σ - α σ * Work.Drive.sweepW' D σ →
      r u ∉ openSegment ℝ (r (Work.Drive.taR D σ)) (r (Work.Drive.tbR D σ)))
    (hradA : 0 ≤ inner ℝ (Work.Drive.sweepArc' r D σ (α σ) - r (Work.Drive.taR D σ))
      (velocity r (Work.Drive.taR D σ + α σ * Work.Drive.sweepW' D σ)))
    (hradB : inner ℝ (Work.Drive.sweepArc' r D σ (1 - α σ) - r (Work.Drive.tbR D σ))
      (velocity r (Work.Drive.taR D σ + (1 - α σ) * Work.Drive.sweepW' D σ)) ≤ 0) :
    Work.Drive.ChamferJunctionOK r D α β σ := by
  have hb1 : β σ < 1 := by linarith
  -- the retained arc's parameter window is non-empty
  have hwin : taR D σ + α σ * sweepW' D σ ≤ tbR D σ - α σ * sweepW' D σ := by
    have h : (2 * α σ) * sweepW' D σ ≤ 1 * sweepW' D σ :=
      mul_le_mul_of_nonneg_right (le_of_lt hα2) (le_of_lt hW)
    have hwdef : sweepW' D σ = tbR D σ - taR D σ := rfl
    nlinarith [h, hwdef]
  refine ⟨hV, hW, hα, hα2, hβ, hβ2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the tail cut point is not the chord point at fraction `β σ`
    intro heq
    have hmem : sweepChord' r D σ (β σ) ∈ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) := by
      rw [openSegment_eq_image]
      exact ⟨β σ, ⟨hβ, hb1⟩, rfl⟩
    have hmem' : sweepArc' r D σ (α σ) ∈ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) := by
      rw [heq]; exact hmem
    exact hmid (taR D σ + α σ * sweepW' D σ) le_rfl hwin (by simpa only [sweepArc'] using hmem')
  · -- the head cut point is not the chord point at fraction `1 - β σ`
    intro heq
    have hmem : sweepChord' r D σ (1 - β σ) ∈ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) := by
      rw [openSegment_eq_image]
      exact ⟨1 - β σ, ⟨by linarith, by linarith⟩, rfl⟩
    have hmem' : sweepArc' r D σ (1 - α σ) ∈ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) := by
      rw [heq]; exact hmem
    have hQeq : sweepArc' r D σ (1 - α σ) = r (tbR D σ - α σ * sweepW' D σ) := by
      show r (taR D σ + (1 - α σ) * sweepW' D σ) = r (tbR D σ - α σ * sweepW' D σ)
      congr 1
      rw [show sweepW' D σ = tbR D σ - taR D σ from rfl]
      ring
    rw [hQeq] at hmem'
    exact hmid (tbR D σ - α σ * sweepW' D σ) hwin le_rfl hmem'
  · -- J1
    intro k hk
    exact cjb_head_not_reverse (D := D) (σ := σ) (a := α σ) (b := β σ) (k := k)
      (v := velocity r (taR D σ + (1 - α σ) * sweepW' D σ)) hβ hk (hr.regular _) hballB hradB
  · -- J2
    intro k hk
    exact cjb_head_not_V (D := D) (σ := σ) (a := α σ) (b := β σ) (k := k) hβ hV hsum hmid hwin hk
  · -- J3
    intro k hk
    exact cjb_tail_not_V (D := D) (σ := σ) (a := α σ) (b := β σ) (k := k) hβ hV hsum hmid hwin hk
  · -- J4
    intro k hk
    exact cjb_tail_not_reverse (D := D) (σ := σ) (a := α σ) (b := β σ) (k := k)
      (v := velocity r (taR D σ + α σ * sweepW' D σ)) hβ hk (hr.regular _) hballA hradA

end Work.Drive
