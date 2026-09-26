import Mathlib
import Submission.Work.Drive.chordFrame
import Submission.Work.Drive.chamferCrossingThin

/-!
# The perpendicular-chamfer ("thin") loop of the `OFat` sweep: geometry and separation

This module is the `E1` layer of the endgame of the project (the lead's `NOTES_LEAD_OFat.md`,
item `E1`): the sweep loop obtained from the retained arc by *cutting* it at an absolute parameter
depth `la` (resp. `lb`) from each end and joining the two cut points to the chord *perpendicularly*.

Nothing here is specific to the chord sweep of a band arc: the loop is built from two chord
endpoints `ta`, `tb` and two cut depths, so the statements apply verbatim to any family of chords.

The geometric point of the perpendicular chamfer is that every one of its points has the **same
chord coordinate** as its arc endpoint (`chordCoord` is constant on the connector, because the
connector is orthogonal to the chord direction).  Consequently

* the tail connector and the head connector have distinct chord coordinates, hence are disjoint;
* the chord part (the segment between the two feet) can only meet a connector at the shared foot;
* an arc point on a connector satisfies the *ball* bound `‖r ξ - A‖ ≤ ‖r (ta+la) - A‖`, which the
  far end of the arc cannot satisfy (`E2(iii)`, `Work.Drive.thinCorner_distance_increasing`), and
  the near end is handled by the chord-coordinate monotonicity on the *short* window
  `[ta, ta + 2 la]` (the lead's `G`, `Work.Drive.perpChamfer_disjoint`).

## Contents

* `Work.Drive.chordFoot` — the perpendicular foot of a point on the chord *line*;
* `Work.Drive.chordCoord_chordFoot`, `chordPerp_chordFoot` — the foot is on the line, at the same
  chord coordinate;
* `Work.Drive.chordCoord_thinCombo`, `chordPerp_thinCombo` — the points of the connector
  `[P, chordFoot A B P]` have chord coordinate `chordCoord A B P` and perpendicular part a multiple
  of that of `P`;
* `Work.Drive.norm_thinCombo_le` — the connector lies in the closed ball centred at `A` of radius
  `‖P - A‖`;
* `Work.Drive.thinFoot_segment_subset_segment` — the chord part of the loop lies in the open
  segment `(A, B)` as soon as the two feet are strictly inside;
* `Work.Drive.thinLoop` — the loop itself, and `Work.Drive.thinLoop_injOn` — its injectivity on one
  period from the separation hypotheses.
-/

set_option maxHeartbeats 4000000

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ## 1. The perpendicular foot and the connector -/

/-- **The perpendicular foot** of `P` on the chord *line* of `A B`. -/
def chordFoot (A B P : Space) : Space := A + chordCoord A B P • chordDir A B

lemma chordFoot_sub (A B P : Space) :
    chordFoot A B P - A = chordCoord A B P • chordDir A B := by
  rw [chordFoot]; abel

lemma chordCoord_chordFoot {A B P : Space} (hAB : A ≠ B) :
    chordCoord A B (chordFoot A B P) = chordCoord A B P := by
  rw [chordCoord, chordFoot_sub, inner_smul_left, real_inner_self_eq_norm_sq,
    chordDir_norm A B hAB, one_pow, RCLike.conj_to_real, mul_one]

lemma chordPerp_chordFoot {A B P : Space} (hAB : A ≠ B) :
    chordPerp A B (chordFoot A B P) = 0 := by
  rw [chordPerp, chordCoord_chordFoot hAB, chordFoot_sub, sub_self]

lemma chordPerp_inner_chordDir {A B P : Space} (hAB : A ≠ B) :
    inner ℝ (chordPerp A B P) (chordDir A B) = 0 := by
  rw [chordPerp, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq,
    chordDir_norm A B hAB, one_pow, mul_one, RCLike.conj_to_real]
  rw [show inner ℝ (P - A) (chordDir A B) = chordCoord A B P from rfl]
  ring

/-- The decomposition `P = A + chordCoord A B P • chordDir A B + chordPerp A B P`. -/
lemma sub_eq_smul_chordDir_add_chordPerp (A B P : Space) :
    P - A = chordCoord A B P • chordDir A B + chordPerp A B P := by
  rw [chordPerp]; abel

/-- Elementary inner-product fact: `⟪c • u, u⟫ = c` for a unit `u`. -/
lemma inner_smul_chordDir_self {A B P : Space} (hAB : A ≠ B) :
    inner ℝ (chordCoord A B P • chordDir A B) (chordDir A B) = chordCoord A B P := by
  rw [inner_smul_left, real_inner_self_eq_norm_sq, chordDir_norm A B hAB, one_pow,
    RCLike.conj_to_real, mul_one]

/-- **Chord coordinate along the connector.**  Every point of the segment from `P` to the
perpendicular foot `chordFoot A B P` has chord coordinate `chordCoord A B P`. -/
lemma chordCoord_thinCombo {A B P : Space} (hAB : A ≠ B) (μ : ℝ) :
    chordCoord A B ((1 - μ) • P + μ • chordFoot A B P) = chordCoord A B P := by
  have h1 : (1 - μ) • P + μ • chordFoot A B P - A
      = (1 - μ) • (P - A) + μ • (chordFoot A B P - A) := by module
  rw [chordCoord, h1, inner_add_left, inner_smul_left, inner_smul_left, chordFoot_sub,
    inner_smul_chordDir_self hAB, RCLike.conj_to_real, RCLike.conj_to_real]
  rw [show inner ℝ (P - A) (chordDir A B) = chordCoord A B P from rfl]
  ring

/-- **Perpendicular part along the connector**: it is the corresponding multiple of that of `P`. -/
lemma chordPerp_thinCombo {A B P : Space} (hAB : A ≠ B) (μ : ℝ) :
    chordPerp A B ((1 - μ) • P + μ • chordFoot A B P) = (1 - μ) • chordPerp A B P := by
  have h1 : (1 - μ) • P + μ • chordFoot A B P - A
      = (1 - μ) • (P - A) + μ • (chordFoot A B P - A) := by module
  have h2 : (1 - μ) • (P - A) + μ • (chordFoot A B P - A) - chordCoord A B P • chordDir A B
      = (1 - μ) • (P - A - chordCoord A B P • chordDir A B) := by
    rw [chordFoot_sub]; module
  show (1 - μ) • P + μ • chordFoot A B P - A
      - chordCoord A B ((1 - μ) • P + μ • chordFoot A B P) • chordDir A B
      = (1 - μ) • (P - A - chordCoord A B P • chordDir A B)
  rw [chordCoord_thinCombo hAB μ, h1, h2]

/-- **The connector lies in the ball.**  Every point of the segment from `P` to its perpendicular
foot is at distance at most `‖P - A‖` from `A`. -/
lemma norm_thinCombo_le {A B P : Space} (hAB : A ≠ B) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    ‖(1 - μ) • P + μ • chordFoot A B P - A‖ ≤ ‖P - A‖ := by
  have hunit : ‖chordDir A B‖ = 1 := chordDir_norm A B hAB
  have hdecomp : P - A = chordCoord A B P • chordDir A B + chordPerp A B P :=
    sub_eq_smul_chordDir_add_chordPerp A B P
  have horth : inner ℝ (chordDir A B) (chordPerp A B P) = 0 := by
    have h := chordPerp_inner_chordDir (A := A) (B := B) (P := P) hAB
    rw [real_inner_comm] at h
    exact h
  have hkey : (1 - μ) • P + μ • chordFoot A B P - A
      = chordCoord A B P • chordDir A B + (1 - μ) • chordPerp A B P := by
    have h1 : (1 - μ) • P + μ • chordFoot A B P - A
        = (1 - μ) • (P - A) + μ • (chordFoot A B P - A) := by
      module
    rw [h1, chordFoot_sub, hdecomp]
    module
  rw [hkey, hdecomp]
  have h2 : ‖chordCoord A B P • chordDir A B + (1 - μ) • chordPerp A B P‖ ^ 2
      = ‖chordCoord A B P • chordDir A B‖ ^ 2 + ‖(1 - μ) • chordPerp A B P‖ ^ 2 := by
    rw [sq, sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
    rw [inner_smul_left, inner_smul_right, horth, mul_zero, mul_zero]
  have h3 : ‖chordCoord A B P • chordDir A B + chordPerp A B P‖ ^ 2
      = ‖chordCoord A B P • chordDir A B‖ ^ 2 + ‖chordPerp A B P‖ ^ 2 := by
    rw [sq, sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
    rw [inner_smul_left, horth, mul_zero]
  have h4 : ‖(1 - μ) • chordPerp A B P‖ ≤ ‖chordPerp A B P‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - μ)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  have h5 : ‖chordCoord A B P • chordDir A B + (1 - μ) • chordPerp A B P‖ ^ 2
      ≤ ‖chordCoord A B P • chordDir A B + chordPerp A B P‖ ^ 2 := by
    rw [h2, h3]
    have h4' : ‖(1 - μ) • chordPerp A B P‖ ^ 2 ≤ ‖chordPerp A B P‖ ^ 2 := by
      rw [sq, sq]
      exact mul_self_le_mul_self (norm_nonneg _) h4
    linarith [h4']
  have h6 : (0:ℝ) ≤ ‖chordCoord A B P • chordDir A B + (1 - μ) • chordPerp A B P‖ := norm_nonneg _
  have h7 : (0:ℝ) ≤ ‖chordCoord A B P • chordDir A B + chordPerp A B P‖ := norm_nonneg _
  have h8 := Real.sqrt_le_sqrt h5
  rwa [Real.sqrt_sq h6, Real.sqrt_sq h7] at h8

lemma chordFoot_ne_iff {A B P : Space} (hAB : A ≠ B) :
    P ≠ chordFoot A B P ↔ chordPerp A B P ≠ 0 := by
  constructor
  · intro h hperp
    apply h
    have h1 : P - A = chordCoord A B P • chordDir A B := by
      rw [sub_eq_smul_chordDir_add_chordPerp, hperp, add_zero]
    rw [chordFoot, ← h1]
    abel
  · intro h hc
    apply h
    rw [hc, chordPerp_chordFoot hAB]

/-! ## 2. The thin loop -/

/-- The retained-arc parameter at profile fraction `u`: the affine map carrying `[0,1/4]` on the
retained arc `[a + la, b - lb]`. -/
def thinθ (a b la lb u : ℝ) : ℝ := a + la + 4 * u * ((b - lb) - (a + la))

lemma thinθ_zero (a b la lb : ℝ) : thinθ a b la lb 0 = a + la := by simp [thinθ]

lemma thinθ_quarter (a b la lb : ℝ) : thinθ a b la lb (1 / 4) = b - lb := by
  simp only [thinθ]; ring

lemma thinθ_strictMono {a b la lb : ℝ} (h : 0 < (b - lb) - (a + la)) :
    StrictMono (thinθ a b la lb) := by
  intro u v huv
  have h1 : thinθ a b la lb v - thinθ a b la lb u
      = 4 * (v - u) * ((b - lb) - (a + la)) := by
    simp only [thinθ]; ring
  nlinarith

lemma thinθ_inj {a b la lb : ℝ} (h : 0 < (b - lb) - (a + la)) {u v : ℝ} (heq : thinθ a b la lb u = thinθ a b la lb v) :
    u = v := (thinθ_strictMono h).injective heq

/-- **The profile of the thin (perpendicular-chamfered) loop** with chord endpoints
`A = r a`, `B = r b` and absolute cut depths `la`, `lb`: the retained arc from `a + la` to `b - lb`,
the perpendicular connector at the head, the chord part between the two feet, and the perpendicular
connector at the tail. -/
def thinProf (r : ℝ → Space) (a b la lb : ℝ) (u : ℝ) : Space :=
  if u ≤ 1 / 4 then r (thinθ a b la lb u)
  else if u ≤ 1 / 2 then
    (1 - (4 * u - 1)) • r (b - lb) + (4 * u - 1) • chordFoot (r a) (r b) (r (b - lb))
  else if u ≤ 3 / 4 then
    (1 - (4 * u - 2)) • chordFoot (r a) (r b) (r (b - lb))
      + (4 * u - 2) • chordFoot (r a) (r b) (r (a + la))
  else
    (1 - (4 * u - 3)) • chordFoot (r a) (r b) (r (a + la)) + (4 * u - 3) • r (a + la)

/-- **The thin loop**, `period`-periodic in the loop parameter `t`. -/
def thinLoop (r : ℝ → Space) (a b la lb : ℝ) (t : ℝ) : Space :=
  thinProf r a b la lb (sweepParam t)

lemma thinLoop_add_period (r : ℝ → Space) (a b la lb : ℝ) (t : ℝ) :
    thinLoop r a b la lb (t + period) = thinLoop r a b la lb t := by
  rw [thinLoop, thinLoop, sweepParam_add_period]

lemma thinLoop_periodic (r : ℝ → Space) (a b la lb : ℝ) :
    Function.Periodic (thinLoop r a b la lb) period :=
  thinLoop_add_period r a b la lb

/-! ### 2.1 The four branches of the profile -/

variable {r : ℝ → Space} {a b la lb : ℝ}

lemma thinProf_arc {u : ℝ} (h : u ≤ 1 / 4) :
    thinProf r a b la lb u = r (thinθ a b la lb u) := by
  rw [thinProf, if_pos h]

lemma thinProf_head {u : ℝ} (h1 : ¬ u ≤ 1 / 4) (h2 : u ≤ 1 / 2) :
    thinProf r a b la lb u
      = (1 - (4 * u - 1)) • r (b - lb) + (4 * u - 1) • chordFoot (r a) (r b) (r (b - lb)) := by
  rw [thinProf, if_neg h1, if_pos h2]

lemma thinProf_chord {u : ℝ} (h1 : ¬ u ≤ 1 / 4) (h2 : ¬ u ≤ 1 / 2) (h3 : u ≤ 3 / 4) :
    thinProf r a b la lb u
      = (1 - (4 * u - 2)) • chordFoot (r a) (r b) (r (b - lb))
        + (4 * u - 2) • chordFoot (r a) (r b) (r (a + la)) := by
  rw [thinProf, if_neg h1, if_neg h2, if_pos h3]

lemma thinProf_tail {u : ℝ} (h1 : ¬ u ≤ 1 / 4) (h2 : ¬ u ≤ 1 / 2) (h3 : ¬ u ≤ 3 / 4) :
    thinProf r a b la lb u
      = (1 - (4 * u - 3)) • chordFoot (r a) (r b) (r (a + la)) + (4 * u - 3) • r (a + la) := by
  rw [thinProf, if_neg h1, if_neg h2, if_neg h3]

/-! ### 2.1b The zone lemmas (valid on the *closed* zones) -/

lemma thinProf_seg_head {u : ℝ} (h1 : 1 / 4 ≤ u) (h2 : u ≤ 1 / 2) :
    thinProf r a b la lb u
      = (1 - (4 * u - 1)) • r (b - lb) + (4 * u - 1) • chordFoot (r a) (r b) (r (b - lb)) := by
  rcases lt_or_ge (1 / 4 : ℝ) u with h | h
  · exact thinProf_head (not_le.mpr h) h2
  · have hu : u = 1 / 4 := le_antisymm h h1
    rw [hu, thinProf_arc le_rfl, thinθ_quarter]
    norm_num

lemma thinProf_seg_chord {u : ℝ} (h1 : 1 / 2 ≤ u) (h2 : u ≤ 3 / 4) :
    thinProf r a b la lb u
      = (1 - (4 * u - 2)) • chordFoot (r a) (r b) (r (b - lb))
        + (4 * u - 2) • chordFoot (r a) (r b) (r (a + la)) := by
  rcases lt_or_ge (1 / 2 : ℝ) u with h | h
  · exact thinProf_chord (not_le.mpr (by linarith)) (not_le.mpr h) h2
  · have hu : u = 1 / 2 := le_antisymm h h1
    rw [hu, thinProf_seg_head (by norm_num : (1:ℝ) / 4 ≤ 1 / 2) (by norm_num : (1:ℝ) / 2 ≤ 1 / 2)]
    norm_num

lemma thinProf_seg_tail {u : ℝ} (h1 : 3 / 4 ≤ u) (h2 : u ≤ 1) :
    thinProf r a b la lb u
      = (1 - (4 * u - 3)) • chordFoot (r a) (r b) (r (a + la)) + (4 * u - 3) • r (a + la) := by
  rcases lt_or_ge (3 / 4 : ℝ) u with h | h
  · exact thinProf_tail (not_le.mpr (by linarith)) (not_le.mpr (by linarith)) (not_le.mpr h)
  · have hu : u = 3 / 4 := le_antisymm h h1
    rw [hu, thinProf_seg_chord (by norm_num : (1:ℝ) / 2 ≤ 3 / 4) (by norm_num : (3:ℝ) / 4 ≤ 3 / 4)]
    norm_num

/-! ### 2.2 Elementary convex-combination lemmas -/

/-- The chord coordinate of a convex combination is the convex combination of the chord
coordinates. -/
lemma chordCoord_convex_combo {A B X Y : Space} (μ : ℝ) :
    chordCoord A B ((1 - μ) • X + μ • Y)
      = (1 - μ) * chordCoord A B X + μ * chordCoord A B Y := by
  have h1 : (1 - μ) • X + μ • Y - A = (1 - μ) • (X - A) + μ • (Y - A) := by module
  rw [chordCoord, h1, inner_add_left, inner_smul_left, inner_smul_left, RCLike.conj_to_real,
    RCLike.conj_to_real, chordCoord, chordCoord]

/-- A convex combination is injective in its coefficient on a non-degenerate pair. -/
lemma convex_combo_inj {X Y : Space} (h : X ≠ Y) {s t : ℝ}
    (heq : (1 - s) • X + s • Y = (1 - t) • X + t • Y) : s = t := by
  have h1 : (s - t) • (Y - X) = 0 := by
    have h2 : (1 - s) • X + s • Y - ((1 - t) • X + t • Y) = (s - t) • (Y - X) := by module
    rw [← h2, sub_eq_zero.mpr heq]
  have hsub : Y - X ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hsub)

/-- A point of the chord line strictly inside the chord is a point of the open segment. -/
lemma mem_openSegment_of_chordPerp_eq_zero' {A B Q : Space} (hAB : A ≠ B)
    (h0 : 0 < chordCoord A B Q) (h1 : chordCoord A B Q < ‖B - A‖)
    (hperp : chordPerp A B Q = 0) : Q ∈ openSegment ℝ A B :=
  mem_openSegment_of_chordPerp_eq_zero hAB h0 h1 hperp


/-! ### 2.3 The perpendicular part of a convex combination, and the chord part of the loop -/

lemma chordPerp_convex_combo {A B X Y : Space} (μ : ℝ) :
    chordPerp A B ((1 - μ) • X + μ • Y)
      = (1 - μ) • chordPerp A B X + μ • chordPerp A B Y := by
  rw [chordPerp, chordPerp, chordPerp, chordCoord_convex_combo]
  have h1 : (1 - μ) • X + μ • Y - A = (1 - μ) • (X - A) + μ • (Y - A) := by module
  rw [h1]
  module

/-- **The chord part of the thin loop lies in the open segment.**  If the two feet
`X`, `Y` are on the chord line strictly inside the chord, then so is the whole segment between
them. -/
lemma segment_feet_subset_openSegment {A B X Y : Space} (hAB : A ≠ B)
    (hXperp : chordPerp A B X = 0) (hYperp : chordPerp A B Y = 0)
    (hX0 : 0 < chordCoord A B X) (hX1 : chordCoord A B X < ‖B - A‖)
    (hY0 : 0 < chordCoord A B Y) (hY1 : chordCoord A B Y < ‖B - A‖)
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    (1 - μ) • X + μ • Y ∈ openSegment ℝ A B := by
  have hperp : chordPerp A B ((1 - μ) • X + μ • Y) = 0 := by
    rw [chordPerp_convex_combo, hXperp, hYperp]
    module
  have hc := chordCoord_convex_combo (A := A) (B := B) (X := X) (Y := Y) μ
  refine mem_openSegment_of_chordPerp_eq_zero hAB ?_ ?_ hperp
  · have : 0 < (1 - μ) * chordCoord A B X + μ * chordCoord A B Y := by
      rcases lt_or_ge μ 1 with h | h
      · have h1 := mul_pos (sub_pos.mpr h) hX0
        have h2 := mul_nonneg hμ0 hY0.le
        linarith
      · have hμ1' : μ = 1 := le_antisymm hμ1 h
        rw [hμ1']
        simpa using hY0
    rw [hc]; exact this
  · have : (1 - μ) * chordCoord A B X + μ * chordCoord A B Y < ‖B - A‖ := by
      rcases lt_or_ge μ 1 with h | h
      · have h1 : (1 - μ) * chordCoord A B X < (1 - μ) * ‖B - A‖ :=
          mul_lt_mul_of_pos_left hX1 (sub_pos.mpr h)
        have h2 : μ * chordCoord A B Y ≤ μ * ‖B - A‖ :=
          mul_le_mul_of_nonneg_left hY1.le hμ0
        nlinarith [h1, h2]
      · have hμ1' : μ = 1 := le_antisymm hμ1 h
        rw [hμ1']
        simpa using hY1
    rw [hc]; exact this

/-! ## 3. Injectivity of the thin loop -/

/-- **Injectivity of the thin loop on one period**, from the geometric separation hypotheses:

* the retained arc `[a + la, b - lb]` misses the chord `(r a, r b)` (`hmid`);
* the perpendicular connector at `a + la` meets the retained arc only at its own arc endpoint
  (`hsep_a`) — the lead's `G`, `Work.Drive.perpChamfer_disjoint`;
* likewise at `b - lb` (`hsep_b`);
* both feet are strictly inside the chord and distinct (`hca`, `hca'`, `hcb`, `hcb'`, `hcne`).

The three separation hypotheses are exactly what the corner analysis (`E2` and `G`) supplies; the
rest of the proof is the chord-frame bookkeeping: the connectors have constant chord coordinate, so
they can only meet the chord part at the shared foot. -/
theorem thinLoop_injOn {r : ℝ → Space} (hr : IsSmoothKnot r)
    {a b la lb : ℝ} (hab : a < b) (hbw : b - a < period) (hla : 0 < la) (hlb : 0 < lb)
    (hlab : la + lb < b - a)
    (hca : 0 < chordCoord (r a) (r b) (r (a + la)))
    (hca' : chordCoord (r a) (r b) (r (a + la)) < ‖r b - r a‖)
    (hcb : 0 < chordCoord (r a) (r b) (r (b - lb)))
    (hcb' : chordCoord (r a) (r b) (r (b - lb)) < ‖r b - r a‖)
    (hcne : chordCoord (r a) (r b) (r (a + la))
              ≠ chordCoord (r a) (r b) (r (b - lb)))
    (hmid : ∀ θ : ℝ, a + la ≤ θ → θ ≤ b - lb → ∀ μ : ℝ, 0 < μ → μ < 1 →
        r θ ≠ (1 - μ) • r a + μ • r b)
    (hsep_a : ∀ θ μ : ℝ, a + la ≤ θ → θ ≤ b - lb → 0 ≤ μ → μ ≤ 1 →
        r θ = (1 - μ) • r (a + la) + μ • chordFoot (r a) (r b) (r (a + la)) → θ = a + la)
    (hsep_b : ∀ θ μ : ℝ, a + la ≤ θ → θ ≤ b - lb → 0 ≤ μ → μ ≤ 1 →
        r θ = (1 - μ) • r (b - lb) + μ • chordFoot (r a) (r b) (r (b - lb)) → θ = b - lb) :
    Set.InjOn (thinLoop r a b la lb) (Set.Ico 0 period) := by
  classical
  set A : Space := r a with hAdef
  set B : Space := r b with hBdef
  set P : Space := r (a + la) with hPdef
  set Q : Space := r (b - lb) with hQdef
  set Fa : Space := chordFoot A B P with hFadef
  set Fb : Space := chordFoot A B Q with hFbdef
  have hwpos : 0 < (b - lb) - (a + la) := by linarith
  have hAB : A ≠ B := by
    rw [hAdef, hBdef]
    exact knot_ne_of_sub_mem_Ioo hr (by linarith) hbw
  have hVpos : 0 < ‖B - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hAB))
  have hcP_lt : chordCoord A B P < ‖B - A‖ := hca'
  have hcQ_lt : chordCoord A B Q < ‖B - A‖ := hcb'
  have hperpa : chordPerp A B Fa = 0 := by rw [hFadef]; exact chordPerp_chordFoot hAB
  have hperpb : chordPerp A B Fb = 0 := by rw [hFbdef]; exact chordPerp_chordFoot hAB
  have hχFa : chordCoord A B Fa = chordCoord A B P := by
    rw [hFadef]; exact chordCoord_chordFoot hAB
  have hχFb : chordCoord A B Fb = chordCoord A B Q := by
    rw [hFbdef]; exact chordCoord_chordFoot hAB
  -- the free endpoints of the retained arc are not on the chord line
  have hPnotline : chordPerp A B P ≠ 0 := by
    intro h
    have hseg : P ∈ openSegment ℝ A B :=
      mem_openSegment_of_chordPerp_eq_zero hAB hca hcP_lt h
    rw [openSegment_eq_image] at hseg
    obtain ⟨t, ht, hteq⟩ := hseg
    exact hmid (a + la) le_rfl (by linarith) t ht.1 ht.2 hteq.symm
  have hQnotline : chordPerp A B Q ≠ 0 := by
    intro h
    have hseg : Q ∈ openSegment ℝ A B :=
      mem_openSegment_of_chordPerp_eq_zero hAB hcb hcQ_lt h
    rw [openSegment_eq_image] at hseg
    obtain ⟨t, ht, hteq⟩ := hseg
    exact hmid (b - lb) (by linarith) le_rfl t ht.1 ht.2 hteq.symm
  have hFaP : Fa ≠ P := fun h => hPnotline (by rw [← h]; exact hperpa)
  have hFbQ : Fb ≠ Q := fun h => hQnotline (by rw [← h]; exact hperpb)
  have hFaFb : Fa ≠ Fb := by
    intro h
    have h' : chordCoord A B Fa = chordCoord A B Fb := by rw [h]
    rw [hχFa, hχFb] at h'
    exact absurd h' hcne
  have hcQne : chordCoord A B Q ≠ chordCoord A B P := hcne.symm
  have hcPne : chordCoord A B P ≠ chordCoord A B Q := hcne
  have hθmono : StrictMono (thinθ a b la lb) := thinθ_strictMono hwpos
  have harc_bounds : ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 4 →
      a + la ≤ thinθ a b la lb u ∧ thinθ a b la lb u ≤ b - lb := by
    intro u hu0 hu1
    constructor
    · have h1 : thinθ a b la lb u - thinθ a b la lb 0 = 4 * u * ((b - lb) - (a + la)) := by
        simp only [thinθ]; ring
      rw [thinθ_zero] at h1
      nlinarith
    · have h1 : thinθ a b la lb u ≤ thinθ a b la lb (1 / 4) := hθmono.monotone hu1
      rwa [thinθ_quarter] at h1
  -- chord coordinates of the three zones
  have hχhead : ∀ u : ℝ, 1 / 4 ≤ u → u ≤ 1 / 2 →
      chordCoord A B (thinProf r a b la lb u) = chordCoord A B Q := by
    intro u h1 h2
    rw [thinProf_seg_head h1 h2, chordCoord_convex_combo, hχFb]
    ring
  have hχchord : ∀ u : ℝ, 1 / 2 ≤ u → u ≤ 3 / 4 →
      chordCoord A B (thinProf r a b la lb u)
        = (1 - (4 * u - 2)) * chordCoord A B Q + (4 * u - 2) * chordCoord A B P := by
    intro u h1 h2
    rw [thinProf_seg_chord h1 h2, chordCoord_convex_combo, hχFb, hχFa]
  have hχtail : ∀ u : ℝ, 3 / 4 ≤ u → u ≤ 1 →
      chordCoord A B (thinProf r a b la lb u) = chordCoord A B P := by
    intro u h1 h2
    rw [thinProf_seg_tail h1 h2, chordCoord_convex_combo, hχFa]
    ring
  -- injectivity on each zone
  have hArcInj : ∀ u₁ u₂ : ℝ, 0 ≤ u₁ → u₁ ≤ 1 / 4 → 0 ≤ u₂ → u₂ ≤ 1 / 4 →
      thinProf r a b la lb u₁ = thinProf r a b la lb u₂ → u₁ = u₂ := by
    intro u₁ u₂ hu₁0 hu₁1 hu₂0 hu₂1 heq
    rw [thinProf_arc hu₁1, thinProf_arc hu₂1] at heq
    have h1 := harc_bounds u₁ hu₁0 hu₁1
    have h2 := harc_bounds u₂ hu₂0 hu₂1
    have hθeq : thinθ a b la lb u₁ = thinθ a b la lb u₂ := by
      rcases lt_trichotomy (thinθ a b la lb u₁) (thinθ a b la lb u₂) with hlt | heq' | hgt
      · exact absurd heq (knot_ne_of_sub_mem_Ioo hr (by linarith) (by linarith))
      · exact heq'
      · exact absurd heq.symm (knot_ne_of_sub_mem_Ioo hr (by linarith) (by linarith))
    exact thinθ_inj hwpos hθeq
  have hSegHead : ∀ u₁ u₂ : ℝ, 1 / 4 ≤ u₁ → u₁ ≤ 1 / 2 → 1 / 4 ≤ u₂ → u₂ ≤ 1 / 2 →
      thinProf r a b la lb u₁ = thinProf r a b la lb u₂ → u₁ = u₂ := by
    intro u₁ u₂ hu₁0 hu₁1 hu₂0 hu₂1 heq
    rw [thinProf_seg_head hu₁0 hu₁1, thinProf_seg_head hu₂0 hu₂1] at heq
    have h := convex_combo_inj (X := Q) (Y := Fb) hFbQ.symm heq
    linarith
  have hSegChord : ∀ u₁ u₂ : ℝ, 1 / 2 ≤ u₁ → u₁ ≤ 3 / 4 → 1 / 2 ≤ u₂ → u₂ ≤ 3 / 4 →
      thinProf r a b la lb u₁ = thinProf r a b la lb u₂ → u₁ = u₂ := by
    intro u₁ u₂ hu₁0 hu₁1 hu₂0 hu₂1 heq
    rw [thinProf_seg_chord hu₁0 hu₁1, thinProf_seg_chord hu₂0 hu₂1] at heq
    have h := convex_combo_inj (X := Fb) (Y := Fa) hFaFb.symm heq
    linarith
  have hSegTail : ∀ u₁ u₂ : ℝ, 3 / 4 ≤ u₁ → u₁ ≤ 1 → 3 / 4 ≤ u₂ → u₂ ≤ 1 →
      thinProf r a b la lb u₁ = thinProf r a b la lb u₂ → u₁ = u₂ := by
    intro u₁ u₂ hu₁0 hu₁1 hu₂0 hu₂1 heq
    rw [thinProf_seg_tail hu₁0 hu₁1, thinProf_seg_tail hu₂0 hu₂1] at heq
    have h := convex_combo_inj (X := Fa) (Y := P) hFaP heq
    linarith
  -- the cross-zone facts
  have hI12 : ∀ u₁ u₂ : ℝ, 0 ≤ u₁ → u₁ ≤ 1 / 4 → 1 / 4 ≤ u₂ → u₂ ≤ 1 / 2 → u₁ < u₂ →
      thinProf r a b la lb u₁ = thinProf r a b la lb u₂ → False := by
    intro u₁ u₂ hu₁0 hu₁1 hu₂0 hu₂1 hlt heq
    have hseg : thinProf r a b la lb u₂
        = (1 - (4 * u₂ - 1)) • Q + (4 * u₂ - 1) • Fb := thinProf_seg_head hu₂0 hu₂1
    have heqarc : r (thinθ a b la lb u₁) = (1 - (4 * u₂ - 1)) • Q + (4 * u₂ - 1) • Fb := by
      rw [← thinProf_arc (r := r) (a := a) (b := b) (la := la) (lb := lb) hu₁1]
      exact heq.trans hseg
    have hb := harc_bounds u₁ hu₁0 hu₁1
    have hμ0 : 0 ≤ 4 * u₂ - 1 := by linarith
    have hμ1 : 4 * u₂ - 1 ≤ 1 := by linarith
    have hθ := hsep_b (thinθ a b la lb u₁) (4 * u₂ - 1) hb.1 hb.2 hμ0 hμ1 heqarc
    have hu₁ : u₁ = 1 / 4 := thinθ_inj hwpos (hθ.trans (thinθ_quarter a b la lb).symm)
    have h1 : thinProf r a b la lb u₁ = Q := by rw [thinProf_arc hu₁1, hθ]
    have h2 : thinProf r a b la lb u₂ = Q := by rw [← heq, h1]
    have h3 : (1 - (4 * u₂ - 1)) • Q + (4 * u₂ - 1) • Fb
        = ((1:ℝ) - 0) • Q + (0:ℝ) • Fb := by
      rw [← hseg, h2]; simp
    have h4 : 4 * u₂ - 1 = 0 := convex_combo_inj (X := Q) (Y := Fb) hFbQ.symm h3
    have hu₂ : u₂ = 1 / 4 := by linarith
    exact absurd (hu₁.trans hu₂.symm) (ne_of_lt hlt)
  have hI13 : ∀ u₁ u₂ : ℝ, 0 ≤ u₁ → u₁ ≤ 1 / 4 → 1 / 2 ≤ u₂ → u₂ ≤ 3 / 4 →
      thinProf r a b la lb u₁ = thinProf r a b la lb u₂ → False := by
    intro u₁ u₂ hu₁0 hu₁1 hu₂0 hu₂1 heq
    have hb := harc_bounds u₁ hu₁0 hu₁1
    have hμ0 : 0 ≤ 4 * u₂ - 2 := by linarith
    have hμ1 : 4 * u₂ - 2 ≤ 1 := by linarith
    have hmem : thinProf r a b la lb u₂ ∈ openSegment ℝ A B := by
      rw [thinProf_seg_chord hu₂0 hu₂1]
      exact segment_feet_subset_openSegment (X := Fb) (Y := Fa) hAB hperpb hperpa
        (by rw [hχFb]; exact hcb) (by rw [hχFb]; exact hcQ_lt)
        (by rw [hχFa]; exact hca) (by rw [hχFa]; exact hcP_lt) hμ0 hμ1
    have hmem' : thinProf r a b la lb u₁ ∈ openSegment ℝ A B := by rw [heq]; exact hmem
    rw [thinProf_arc hu₁1, openSegment_eq_image] at hmem'
    obtain ⟨t, ht, hteq⟩ := hmem'
    exact hmid (thinθ a b la lb u₁) hb.1 hb.2 t ht.1 ht.2 hteq.symm
  have hI14 : ∀ u₁ u₂ : ℝ, 0 ≤ u₁ → u₁ ≤ 1 / 4 → 3 / 4 ≤ u₂ → u₂ < 1 →
      thinProf r a b la lb u₁ = thinProf r a b la lb u₂ → False := by
    intro u₁ u₂ hu₁0 hu₁1 hu₂0 hu₂1 heq
    have hseg : thinProf r a b la lb u₂
        = (1 - (4 * u₂ - 3)) • Fa + (4 * u₂ - 3) • P := thinProf_seg_tail hu₂0 hu₂1.le
    have heqarc : r (thinθ a b la lb u₁) = (1 - (4 * u₂ - 3)) • Fa + (4 * u₂ - 3) • P := by
      rw [← thinProf_arc (r := r) (a := a) (b := b) (la := la) (lb := lb) hu₁1]
      exact heq.trans hseg
    have heq' : r (thinθ a b la lb u₁)
        = (1 - (1 - (4 * u₂ - 3))) • P + (1 - (4 * u₂ - 3)) • Fa := by
      rw [heqarc, show (1 - (1 - (4 * u₂ - 3))) = 4 * u₂ - 3 by ring, add_comm]
    have hb := harc_bounds u₁ hu₁0 hu₁1
    have hμ0 : 0 ≤ 1 - (4 * u₂ - 3) := by linarith
    have hμ1 : 1 - (4 * u₂ - 3) ≤ 1 := by linarith
    have hθ := hsep_a (thinθ a b la lb u₁) (1 - (4 * u₂ - 3)) hb.1 hb.2 hμ0 hμ1 heq'
    have hu₁ : u₁ = 0 := thinθ_inj hwpos (hθ.trans (thinθ_zero a b la lb).symm)
    have h1 : thinProf r a b la lb u₁ = P := by rw [thinProf_arc hu₁1, hθ]
    have h2 : thinProf r a b la lb u₂ = P := by rw [← heq, h1]
    have h3 : (1 - (4 * u₂ - 3)) • Fa + (4 * u₂ - 3) • P
        = ((1:ℝ) - 1) • Fa + (1:ℝ) • P := by
      rw [← hseg, h2]; simp
    have h4 : 4 * u₂ - 3 = 1 := convex_combo_inj (X := Fa) (Y := P) hFaP h3
    have hu₂ : u₂ = 1 := by linarith
    exact absurd hu₂ (ne_of_lt hu₂1)
  have hI23 : ∀ u₁ u₂ : ℝ, 1 / 4 ≤ u₁ → u₁ ≤ 1 / 2 → 1 / 2 < u₂ → u₂ ≤ 3 / 4 →
      thinProf r a b la lb u₁ = thinProf r a b la lb u₂ → False := by
    intro u₁ u₂ hu₁0 hu₁1 hu₂0 hu₂1 heq
    have h1 := hχhead u₁ hu₁0 hu₁1
    have h2 := hχchord u₂ hu₂0.le hu₂1
    have hχeq : chordCoord A B (thinProf r a b la lb u₁)
        = chordCoord A B (thinProf r a b la lb u₂) := by rw [heq]
    rw [h1, h2] at hχeq
    have h5 : (4 * u₂ - 2) * (chordCoord A B Q - chordCoord A B P) = 0 := by linarith
    rcases mul_eq_zero.mp h5 with h | h
    · linarith
    · exact absurd (sub_eq_zero.mp h) hcQne
  have hI24 : ∀ u₁ u₂ : ℝ, 1 / 4 ≤ u₁ → u₁ ≤ 1 / 2 → 3 / 4 ≤ u₂ → u₂ ≤ 1 →
      thinProf r a b la lb u₁ = thinProf r a b la lb u₂ → False := by
    intro u₁ u₂ hu₁0 hu₁1 hu₂0 hu₂1 heq
    have h1 := hχhead u₁ hu₁0 hu₁1
    have h2 := hχtail u₂ hu₂0 hu₂1
    have hχeq : chordCoord A B (thinProf r a b la lb u₁)
        = chordCoord A B (thinProf r a b la lb u₂) := by rw [heq]
    rw [h1, h2] at hχeq
    exact absurd hχeq hcQne
  have hI34 : ∀ u₁ u₂ : ℝ, 1 / 2 ≤ u₁ → u₁ ≤ 3 / 4 → 3 / 4 ≤ u₂ → u₂ ≤ 1 → u₁ < u₂ →
      thinProf r a b la lb u₁ = thinProf r a b la lb u₂ → False := by
    intro u₁ u₂ hu₁0 hu₁1 hu₂0 hu₂1 hlt heq
    have h1 := hχchord u₁ hu₁0 hu₁1
    have h2 := hχtail u₂ hu₂0 hu₂1
    have hχeq : chordCoord A B (thinProf r a b la lb u₁)
        = chordCoord A B (thinProf r a b la lb u₂) := by rw [heq]
    rw [h1, h2] at hχeq
    have h5 : (1 - (4 * u₁ - 2)) * (chordCoord A B Q - chordCoord A B P) = 0 := by linarith
    have ht1 : 4 * u₁ - 2 = 1 := by
      rcases mul_eq_zero.mp h5 with h | h
      · exact (sub_eq_zero.mp h).symm
      · exact absurd (sub_eq_zero.mp h) hcQne
    have hu₁ : u₁ = 3 / 4 := by linarith
    have h3 : thinProf r a b la lb u₁ = Fa := by
      rw [thinProf_seg_chord hu₁0 hu₁1, ht1, sub_self, zero_smul, one_smul, zero_add]
    have h4 : thinProf r a b la lb u₂ = Fa := by rw [← heq, h3]
    have h4' : (1 - (4 * u₂ - 3)) • Fa + (4 * u₂ - 3) • P = Fa := by
      rw [← thinProf_seg_tail hu₂0 hu₂1]; exact h4
    have h5' : (1 - (4 * u₂ - 3)) • Fa + (4 * u₂ - 3) • P
        = ((1:ℝ) - 0) • Fa + (0:ℝ) • P := by
      rw [h4']; simp
    have h6 : 4 * u₂ - 3 = 0 := convex_combo_inj (X := Fa) (Y := P) hFaP h5'
    have hu₂ : u₂ = 3 / 4 := by linarith
    exact absurd (hu₁.trans hu₂.symm) (ne_of_lt hlt)
  -- the main dichotomy
  have hcontr : ∀ u₁ u₂ : ℝ, 0 ≤ u₁ → u₁ < 1 → 0 ≤ u₂ → u₂ < 1 → u₁ < u₂ →
      thinProf r a b la lb u₁ = thinProf r a b la lb u₂ → False := by
    intro u₁ u₂ hu₁0 hu₁1 hu₂0 hu₂1 hlt heq
    by_cases h2a : u₂ ≤ 1 / 4
    · exact absurd (hArcInj u₁ u₂ hu₁0 (le_trans hlt.le h2a) hu₂0 h2a heq) (ne_of_lt hlt)
    · have h2b : 1 / 4 < u₂ := not_le.mp h2a
      by_cases h2c : u₂ ≤ 1 / 2
      · by_cases h1a : u₁ ≤ 1 / 4
        · exact hI12 u₁ u₂ hu₁0 h1a h2b.le h2c hlt heq
        · exact absurd (hSegHead u₁ u₂ (not_le.mp h1a).le (hlt.le.trans h2c) h2b.le h2c heq)
            (ne_of_lt hlt)
      · have h2d : 1 / 2 < u₂ := not_le.mp h2c
        by_cases h2e : u₂ ≤ 3 / 4
        · by_cases h1a : u₁ ≤ 1 / 4
          · exact hI13 u₁ u₂ hu₁0 h1a h2d.le h2e heq
          · by_cases h1b : u₁ ≤ 1 / 2
            · exact hI23 u₁ u₂ (not_le.mp h1a).le h1b h2d h2e heq
            · exact absurd (hSegChord u₁ u₂ (not_le.mp h1b).le (hlt.le.trans h2e) h2d.le h2e heq)
                (ne_of_lt hlt)
        · have h2f : 3 / 4 < u₂ := not_le.mp h2e
          by_cases h1a : u₁ ≤ 1 / 4
          · exact hI14 u₁ u₂ hu₁0 h1a h2f.le hu₂1 heq
          · by_cases h1b : u₁ ≤ 1 / 2
            · exact hI24 u₁ u₂ (not_le.mp h1a).le h1b h2f.le hu₂1.le heq
            · by_cases h1c : u₁ ≤ 3 / 4
              · exact hI34 u₁ u₂ (not_le.mp h1b).le h1c h2f.le hu₂1.le hlt heq
              · exact absurd (hSegTail u₁ u₂ (not_le.mp h1c).le hu₁1.le h2f.le hu₂1.le heq)
                  (ne_of_lt hlt)
  have hprof : ∀ u₁ u₂ : ℝ, 0 ≤ u₁ → u₁ < 1 → 0 ≤ u₂ → u₂ < 1 →
      thinProf r a b la lb u₁ = thinProf r a b la lb u₂ → u₁ = u₂ := by
    intro u₁ u₂ hu₁0 hu₁1 hu₂0 hu₂1 heq
    rcases lt_trichotomy u₁ u₂ with hlt | heq' | hgt
    · exact (hcontr u₁ u₂ hu₁0 hu₁1 hu₂0 hu₂1 hlt heq).elim
    · exact heq'
    · exact (hcontr u₂ u₁ hu₂0 hu₂1 hu₁0 hu₁1 hgt heq.symm).elim
  -- transfer to the loop
  intro t₁ ht₁ t₂ ht₂ heq
  have h1 := hprof (sweepParam t₁) (sweepParam t₂) (sweepParam_mem t₁).1 (sweepParam_mem t₁).2
    (sweepParam_mem t₂).1 (sweepParam_mem t₂).2 heq
  rw [sweepParam_eq_div ht₁, sweepParam_eq_div ht₂] at h1
  have h2 := congrArg (fun x : ℝ => x * period) h1
  rwa [div_mul_cancel₀ t₁ (ne_of_gt period_pos), div_mul_cancel₀ t₂ (ne_of_gt period_pos)] at h2


/-! ## 4. Corollaries: the profile form, and the endgame-shaped hypotheses -/

/-- On `[0,1)` the profile fraction is recovered from the loop parameter by `t = period * u`. -/
lemma sweepParam_mul_period' {u : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    sweepParam (period * u) = u := by
  rw [sweepParam, mul_div_cancel_left₀ u (ne_of_gt period_pos)]
  have hfl : ⌊u⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hu.1, hu.2⟩
  rw [hfl]
  simp

/-- **The profile form of the injectivity statement**: the same conclusion for the profile map
`thinProf` on `[0,1)`.  This is the form the parameter-blur (`sweepFam`-style) arguments consume. -/
theorem thinProf_injOn {r : ℝ → Space} (hr : IsSmoothKnot r)
    {a b la lb : ℝ} (hab : a < b) (hbw : b - a < period) (hla : 0 < la) (hlb : 0 < lb)
    (hlab : la + lb < b - a)
    (hca : 0 < chordCoord (r a) (r b) (r (a + la)))
    (hca' : chordCoord (r a) (r b) (r (a + la)) < ‖r b - r a‖)
    (hcb : 0 < chordCoord (r a) (r b) (r (b - lb)))
    (hcb' : chordCoord (r a) (r b) (r (b - lb)) < ‖r b - r a‖)
    (hcne : chordCoord (r a) (r b) (r (a + la))
              ≠ chordCoord (r a) (r b) (r (b - lb)))
    (hmid : ∀ θ : ℝ, a + la ≤ θ → θ ≤ b - lb → ∀ μ : ℝ, 0 < μ → μ < 1 →
        r θ ≠ (1 - μ) • r a + μ • r b)
    (hsep_a : ∀ θ μ : ℝ, a + la ≤ θ → θ ≤ b - lb → 0 ≤ μ → μ ≤ 1 →
        r θ = (1 - μ) • r (a + la) + μ • chordFoot (r a) (r b) (r (a + la)) → θ = a + la)
    (hsep_b : ∀ θ μ : ℝ, a + la ≤ θ → θ ≤ b - lb → 0 ≤ μ → μ ≤ 1 →
        r θ = (1 - μ) • r (b - lb) + μ • chordFoot (r a) (r b) (r (b - lb)) → θ = b - lb) :
    Set.InjOn (thinProf r a b la lb) (Set.Ico 0 1) := by
  intro u₁ h₁ u₂ h₂ heq
  have hm₁ : period * u₁ ∈ Set.Ico (0 : ℝ) period :=
    ⟨by nlinarith [period_pos, h₁.1], by nlinarith [period_pos, h₁.2]⟩
  have hm₂ : period * u₂ ∈ Set.Ico (0 : ℝ) period :=
    ⟨by nlinarith [period_pos, h₂.1], by nlinarith [period_pos, h₂.2]⟩
  have hsq : thinLoop r a b la lb (period * u₁) = thinLoop r a b la lb (period * u₂) := by
    show thinProf r a b la lb (sweepParam (period * u₁))
      = thinProf r a b la lb (sweepParam (period * u₂))
    rw [sweepParam_mul_period' h₁, sweepParam_mul_period' h₂]
    exact heq
  have h := thinLoop_injOn hr hab hbw hla hlb hlab hca hca' hcb hcb' hcne hmid hsep_a hsep_b
    hm₁ hm₂ hsq
  exact mul_left_cancel₀ (ne_of_gt period_pos) h

/-- **The endgame shape of the injectivity statement.**  If the retained arc `[a, b]` carries no
middle at parameter distance `≥ ρ` from both endpoints (`StripCrosscutAvoidingOFat` in the
vocabulary of the `OFat` lane) and the cut depths are at least `ρ`, then the separation hypotheses
of `thinLoop_injOn` reduce to the *single* no-fat-middle hypothesis. -/
theorem thinLoop_injOn_of_noFatMiddle {r : ℝ → Space} (hr : IsSmoothKnot r)
    {a b ρ la lb : ℝ} (hab : a < b) (hbw : b - a < period) (hρ : 0 < ρ)
    (hla : ρ ≤ la) (hlb : ρ ≤ lb) (hlab : la + lb < b - a)
    (hnoFat : ∀ u : ℝ, a + ρ ≤ u → u ≤ b - ρ → r u ∉ openSegment ℝ (r a) (r b))
    (hca : 0 < chordCoord (r a) (r b) (r (a + la)))
    (hca' : chordCoord (r a) (r b) (r (a + la)) < ‖r b - r a‖)
    (hcb : 0 < chordCoord (r a) (r b) (r (b - lb)))
    (hcb' : chordCoord (r a) (r b) (r (b - lb)) < ‖r b - r a‖)
    (hcne : chordCoord (r a) (r b) (r (a + la))
              ≠ chordCoord (r a) (r b) (r (b - lb)))
    (hsep_a : ∀ θ μ : ℝ, a + la ≤ θ → θ ≤ b - lb → 0 ≤ μ → μ ≤ 1 →
        r θ = (1 - μ) • r (a + la) + μ • chordFoot (r a) (r b) (r (a + la)) → θ = a + la)
    (hsep_b : ∀ θ μ : ℝ, a + la ≤ θ → θ ≤ b - lb → 0 ≤ μ → μ ≤ 1 →
        r θ = (1 - μ) • r (b - lb) + μ • chordFoot (r a) (r b) (r (b - lb)) → θ = b - lb) :
    Set.InjOn (thinLoop r a b la lb) (Set.Ico 0 period) := by
  refine thinLoop_injOn hr hab hbw (lt_of_lt_of_le hρ hla) (lt_of_lt_of_le hρ hlb) hlab
    hca hca' hcb hcb' hcne ?_ hsep_a hsep_b
  intro θ h1 h2 μ hμ0 hμ1 hmem
  refine hnoFat θ (by linarith) (by linarith) ?_
  rw [openSegment_eq_image]
  exact ⟨μ, ⟨hμ0, hμ1⟩, hmem.symm⟩


/-! ## 5. Continuity of the thin loop (needed by the parameter-blur layer) -/

lemma thinProf_one_eq_zero (r : ℝ → Space) (a b la lb : ℝ) :
    thinProf r a b la lb 1 = thinProf r a b la lb 0 := by
  rw [thinProf, if_neg (by norm_num : ¬ (1:ℝ) ≤ 1 / 4),
    if_neg (by norm_num : ¬ (1:ℝ) ≤ 1 / 2), if_neg (by norm_num : ¬ (1:ℝ) ≤ 3 / 4)]
  rw [thinProf, if_pos (by norm_num : (0:ℝ) ≤ 1 / 4)]
  show (1 - (4 * 1 - 3)) • chordFoot (r a) (r b) (r (a + la)) + (4 * 1 - 3) • r (a + la)
    = r (thinθ a b la lb 0)
  rw [thinθ_zero]
  norm_num

theorem thinProf_continuous {r : ℝ → Space} (hr : Continuous r) (a b la lb : ℝ) :
    Continuous (thinProf r a b la lb) := by
  have hA : Continuous (fun u : ℝ => r (thinθ a b la lb u)) :=
    hr.comp (by unfold thinθ; fun_prop)
  have hB : Continuous (fun u : ℝ =>
      (1 - (4 * u - 1)) • r (b - lb) + (4 * u - 1) • chordFoot (r a) (r b) (r (b - lb))) := by
    fun_prop
  have hC : Continuous (fun u : ℝ =>
      (1 - (4 * u - 2)) • chordFoot (r a) (r b) (r (b - lb))
        + (4 * u - 2) • chordFoot (r a) (r b) (r (a + la))) := by
    fun_prop
  have hD : Continuous (fun u : ℝ =>
      (1 - (4 * u - 3)) • chordFoot (r a) (r b) (r (a + la)) + (4 * u - 3) • r (a + la)) := by
    fun_prop
  have hCD : Continuous (fun u : ℝ =>
      if u ≤ 3 / 4 then
        (1 - (4 * u - 2)) • chordFoot (r a) (r b) (r (b - lb))
          + (4 * u - 2) • chordFoot (r a) (r b) (r (a + la))
      else
        (1 - (4 * u - 3)) • chordFoot (r a) (r b) (r (a + la)) + (4 * u - 3) • r (a + la)) := by
    refine Continuous.if_le (f := fun u : ℝ => u) (g := fun _ : ℝ => 3 / 4) hC hD
      continuous_id continuous_const ?_
    intro x hx
    rw [hx]
    norm_num
  have hBCD : Continuous (fun u : ℝ =>
      if u ≤ 1 / 2 then
        (1 - (4 * u - 1)) • r (b - lb) + (4 * u - 1) • chordFoot (r a) (r b) (r (b - lb))
      else
        if u ≤ 3 / 4 then
          (1 - (4 * u - 2)) • chordFoot (r a) (r b) (r (b - lb))
            + (4 * u - 2) • chordFoot (r a) (r b) (r (a + la))
        else
          (1 - (4 * u - 3)) • chordFoot (r a) (r b) (r (a + la)) + (4 * u - 3) • r (a + la)) := by
    refine Continuous.if_le (f := fun u : ℝ => u) (g := fun _ : ℝ => 1 / 2) hB hCD
      continuous_id continuous_const ?_
    intro x hx
    rw [hx]
    norm_num
  have hmain : Continuous (fun u : ℝ =>
      if u ≤ 1 / 4 then r (thinθ a b la lb u)
      else
        if u ≤ 1 / 2 then
          (1 - (4 * u - 1)) • r (b - lb) + (4 * u - 1) • chordFoot (r a) (r b) (r (b - lb))
        else
          if u ≤ 3 / 4 then
            (1 - (4 * u - 2)) • chordFoot (r a) (r b) (r (b - lb))
              + (4 * u - 2) • chordFoot (r a) (r b) (r (a + la))
          else
            (1 - (4 * u - 3)) • chordFoot (r a) (r b) (r (a + la)) + (4 * u - 3) • r (a + la)) := by
    refine Continuous.if_le (f := fun u : ℝ => u) (g := fun _ : ℝ => 1 / 4) hA hBCD
      continuous_id continuous_const ?_
    intro x hx
    rw [hx]
    have : thinθ a b la lb (1 / 4 : ℝ) = b - lb := thinθ_quarter a b la lb
    rw [this]
    norm_num
  exact hmain

/-- `sweepParam` is the fractional part of `t / period`. -/
lemma sweepParam_eq_fract (t : ℝ) : sweepParam t = Int.fract (t / period) := by
  rw [sweepParam, Int.fract]

theorem thinLoop_continuous {r : ℝ → Space} (hr : Continuous r) (a b la lb : ℝ) :
    Continuous (thinLoop r a b la lb) := by
  have hG : Continuous (thinProf r a b la lb) := thinProf_continuous hr a b la lb
  have hf : Continuous (fun u : ℝ => thinProf r a b la lb (Int.fract u)) :=
    ContinuousOn.comp_fract'' hG.continuousOn (thinProf_one_eq_zero r a b la lb).symm
  have heq : (fun t : ℝ => thinLoop r a b la lb t)
      = (fun u : ℝ => thinProf r a b la lb (Int.fract u)) ∘ (fun t : ℝ => t / period) := by
    funext t
    show thinProf r a b la lb (sweepParam t) = thinProf r a b la lb (Int.fract (t / period))
    rw [sweepParam_eq_fract]
  change Continuous (fun t : ℝ => thinLoop r a b la lb t)
  rw [heq]
  exact hf.comp (continuous_id.div_const period)


/-! ## 6. Joint continuity of the thin-loop family (data depending on the sweep parameter)

This is the input the compactness arguments of the blur/far-separation layer consume: for a band arc
with continuous lifts `ta`, `tb` and continuous cut depths, the family
`(σ, t) ↦ thinLoop r (ta σ) (tb σ) (la σ) (lb σ) t` is jointly continuous.

The only caveat is that `chordFoot` involves `‖r (tb σ) - r (ta σ)‖⁻¹`, which is *not* continuous at
the degenerate chords `r (tb σ) = r (ta σ)`; the statements below therefore carry a uniform positive
lower bound `δ` on the chord length.  (On a compact sweep window such a bound is available, and the
data can be clamped to make it global.) -/

/-- Continuity of the perpendicular foot, under a uniform bound on the chord length. -/
lemma continuous_chordFoot_of_bound {α : Type*} [TopologicalSpace α]
    {A B P : α → Space} {δ : ℝ} (hδ : 0 < δ)
    (hA : Continuous A) (hB : Continuous B) (hP : Continuous P)
    (hbd : ∀ x, δ ≤ ‖B x - A x‖) :
    Continuous (fun x => chordFoot (A x) (B x) (P x)) := by
  have hBA : Continuous (fun x => B x - A x) := hB.sub hA
  have hnorm : Continuous (fun x => ‖B x - A x‖) := hBA.norm
  have hpos : ∀ x, 0 < ‖B x - A x‖ := fun x => lt_of_lt_of_le hδ (hbd x)
  have hm : Continuous (fun x => (‖B x - A x‖)⁻¹) := hnorm.inv₀ (fun x => (hpos x).ne')
  have hu : Continuous (fun x => chordDir (A x) (B x)) := hm.smul hBA
  have hcc : Continuous (fun x => chordCoord (A x) (B x) (P x)) :=
    (hP.sub hA).inner hu
  exact hA.add (hcc.smul hu)

/-- The thin loop with the chord data depending on the sweep parameter. -/
def thinFam (r : ℝ → Space) (ta tb la lb : ℝ → ℝ) (s t : ℝ) : Space :=
  thinProf r (ta s) (tb s) (la s) (lb s) (sweepParam t)

lemma thinFam_eq (r : ℝ → Space) (ta tb la lb : ℝ → ℝ) (s t : ℝ) :
    thinFam r ta tb la lb s t = thinLoop r (ta s) (tb s) (la s) (lb s) t := rfl

/-- The *profile* of the thin family, as a function of `(σ, u)`. -/
def thinProfFam (r : ℝ → Space) (ta tb la lb : ℝ → ℝ) (p : ℝ × ℝ) : Space :=
  thinProf r (ta p.1) (tb p.1) (la p.1) (lb p.1) p.2

theorem thinProfFam_continuous_of_bound {r : ℝ → Space} (hr : Continuous r)
    {ta tb la lb : ℝ → ℝ} (hta : Continuous ta) (htb : Continuous tb)
    (hla : Continuous la) (hlb : Continuous lb)
    {δ : ℝ} (hδ : 0 < δ) (hbd : ∀ s : ℝ, δ ≤ ‖r (tb s) - r (ta s)‖) :
    Continuous (thinProfFam r ta tb la lb) := by
  have hA : Continuous (fun p : ℝ × ℝ => r (ta p.1)) := hr.comp (hta.comp continuous_fst)
  have hB : Continuous (fun p : ℝ × ℝ => r (tb p.1)) := hr.comp (htb.comp continuous_fst)
  have hP : Continuous (fun p : ℝ × ℝ => r (ta p.1 + la p.1)) :=
    hr.comp ((hta.comp continuous_fst).add (hla.comp continuous_fst))
  have hQ : Continuous (fun p : ℝ × ℝ => r (tb p.1 - lb p.1)) :=
    hr.comp ((htb.comp continuous_fst).sub (hlb.comp continuous_fst))
  have hFa : Continuous (fun p : ℝ × ℝ =>
      chordFoot (r (ta p.1)) (r (tb p.1)) (r (ta p.1 + la p.1))) :=
    continuous_chordFoot_of_bound hδ hA hB hP (fun p : ℝ × ℝ => hbd p.1)
  have hFb : Continuous (fun p : ℝ × ℝ =>
      chordFoot (r (ta p.1)) (r (tb p.1)) (r (tb p.1 - lb p.1))) :=
    continuous_chordFoot_of_bound hδ hA hB hQ (fun p : ℝ × ℝ => hbd p.1)
  have h1 : Continuous (fun p : ℝ × ℝ => 4 * p.2 - 1) := by fun_prop
  have h2 : Continuous (fun p : ℝ × ℝ => 4 * p.2 - 2) := by fun_prop
  have h3 : Continuous (fun p : ℝ × ℝ => 4 * p.2 - 3) := by fun_prop
  have harc : Continuous (fun p : ℝ × ℝ =>
      r (thinθ (ta p.1) (tb p.1) (la p.1) (lb p.1) p.2)) := by
    refine hr.comp ?_
    unfold thinθ
    fun_prop
  have hseg1 : Continuous (fun p : ℝ × ℝ =>
      (1 - (4 * p.2 - 1)) • r (tb p.1 - lb p.1) + (4 * p.2 - 1) • chordFoot (r (ta p.1)) (r (tb p.1)) (r (tb p.1 - lb p.1))) :=
    ((continuous_const.sub h1).smul hQ).add (h1.smul hFb)
  have hseg2 : Continuous (fun p : ℝ × ℝ =>
      (1 - (4 * p.2 - 2)) • chordFoot (r (ta p.1)) (r (tb p.1)) (r (tb p.1 - lb p.1))
        + (4 * p.2 - 2) • chordFoot (r (ta p.1)) (r (tb p.1)) (r (ta p.1 + la p.1))) :=
    ((continuous_const.sub h2).smul hFb).add (h2.smul hFa)
  have hseg3 : Continuous (fun p : ℝ × ℝ =>
      (1 - (4 * p.2 - 3)) • chordFoot (r (ta p.1)) (r (tb p.1)) (r (ta p.1 + la p.1))
        + (4 * p.2 - 3) • r (ta p.1 + la p.1)) :=
    ((continuous_const.sub h3).smul hFa).add (h3.smul hP)
  have hCD : Continuous (fun p : ℝ × ℝ =>
      if p.2 ≤ 3 / 4 then
        (1 - (4 * p.2 - 2)) • chordFoot (r (ta p.1)) (r (tb p.1)) (r (tb p.1 - lb p.1))
          + (4 * p.2 - 2) • chordFoot (r (ta p.1)) (r (tb p.1)) (r (ta p.1 + la p.1))
      else
        (1 - (4 * p.2 - 3)) • chordFoot (r (ta p.1)) (r (tb p.1)) (r (ta p.1 + la p.1))
          + (4 * p.2 - 3) • r (ta p.1 + la p.1)) := by
    refine Continuous.if_le (f := fun p : ℝ × ℝ => p.2) (g := fun _ : ℝ × ℝ => 3 / 4)
      hseg2 hseg3 continuous_snd continuous_const ?_
    intro x hx
    rw [hx]
    norm_num
  have hBCD : Continuous (fun p : ℝ × ℝ =>
      if p.2 ≤ 1 / 2 then
        (1 - (4 * p.2 - 1)) • r (tb p.1 - lb p.1)
          + (4 * p.2 - 1) • chordFoot (r (ta p.1)) (r (tb p.1)) (r (tb p.1 - lb p.1))
      else
        if p.2 ≤ 3 / 4 then
          (1 - (4 * p.2 - 2)) • chordFoot (r (ta p.1)) (r (tb p.1)) (r (tb p.1 - lb p.1))
            + (4 * p.2 - 2) • chordFoot (r (ta p.1)) (r (tb p.1)) (r (ta p.1 + la p.1))
        else
          (1 - (4 * p.2 - 3)) • chordFoot (r (ta p.1)) (r (tb p.1)) (r (ta p.1 + la p.1))
            + (4 * p.2 - 3) • r (ta p.1 + la p.1)) := by
    refine Continuous.if_le (f := fun p : ℝ × ℝ => p.2) (g := fun _ : ℝ × ℝ => 1 / 2)
      hseg1 hCD continuous_snd continuous_const ?_
    intro x hx
    rw [hx]
    norm_num
  have hmain : Continuous (fun p : ℝ × ℝ =>
      if p.2 ≤ 1 / 4 then r (thinθ (ta p.1) (tb p.1) (la p.1) (lb p.1) p.2)
      else
        if p.2 ≤ 1 / 2 then
          (1 - (4 * p.2 - 1)) • r (tb p.1 - lb p.1)
            + (4 * p.2 - 1) • chordFoot (r (ta p.1)) (r (tb p.1)) (r (tb p.1 - lb p.1))
        else
          if p.2 ≤ 3 / 4 then
            (1 - (4 * p.2 - 2)) • chordFoot (r (ta p.1)) (r (tb p.1)) (r (tb p.1 - lb p.1))
              + (4 * p.2 - 2) • chordFoot (r (ta p.1)) (r (tb p.1)) (r (ta p.1 + la p.1))
          else
            (1 - (4 * p.2 - 3)) • chordFoot (r (ta p.1)) (r (tb p.1)) (r (ta p.1 + la p.1))
              + (4 * p.2 - 3) • r (ta p.1 + la p.1)) := by
    refine Continuous.if_le (f := fun p : ℝ × ℝ => p.2) (g := fun _ : ℝ × ℝ => 1 / 4)
      harc hBCD continuous_snd continuous_const ?_
    intro x hx
    rw [hx]
    have : thinθ (ta x.1) (tb x.1) (la x.1) (lb x.1) (1 / 4 : ℝ) = tb x.1 - lb x.1 :=
      thinθ_quarter (ta x.1) (tb x.1) (la x.1) (lb x.1)
    rw [this]
    norm_num
  exact hmain

/-- `thinProfFam` at profile `u = 1` and `u = 0` agree (the loop closes). -/
lemma thinProfFam_one_eq_zero (r : ℝ → Space) (ta tb la lb : ℝ → ℝ) (s : ℝ) :
    thinProfFam r ta tb la lb (s, 1) = thinProfFam r ta tb la lb (s, 0) :=
  thinProf_one_eq_zero r (ta s) (tb s) (la s) (lb s)

/-- **Joint continuity of the thin family** `(σ, t) ↦ thinFam r ta tb la lb σ t`. -/
theorem thinFam_continuous_of_bound {r : ℝ → Space} (hr : Continuous r)
    {ta tb la lb : ℝ → ℝ} (hta : Continuous ta) (htb : Continuous tb)
    (hla : Continuous la) (hlb : Continuous lb)
    {δ : ℝ} (hδ : 0 < δ) (hbd : ∀ s : ℝ, δ ≤ ‖r (tb s) - r (ta s)‖) (s : ℝ) :
    Continuous (thinFam r ta tb la lb s) := by
  have hG : Continuous (thinProfFam r ta tb la lb) :=
    thinProfFam_continuous_of_bound hr hta htb hla hlb hδ hbd
  have hfix : Continuous (fun t : ℝ => thinProfFam r ta tb la lb (s, t)) :=
    hG.comp (continuous_const.prodMk continuous_id)
  have hf : Continuous (fun u : ℝ => thinProfFam r ta tb la lb (s, Int.fract u)) :=
    ContinuousOn.comp_fract'' hfix.continuousOn (thinProfFam_one_eq_zero r ta tb la lb s).symm
  have heq : (fun t : ℝ => thinFam r ta tb la lb s t)
      = (fun u : ℝ => thinProfFam r ta tb la lb (s, Int.fract u)) ∘ (fun t : ℝ => t / period) := by
    funext t
    show thinProf r (ta s) (tb s) (la s) (lb s) (sweepParam t)
      = thinProfFam r ta tb la lb (s, Int.fract (t / period))
    rw [sweepParam_eq_fract]
    rfl
  change Continuous (fun t : ℝ => thinFam r ta tb la lb s t)
  rw [heq]
  exact hf.comp (continuous_id.div_const period)


end Work.Drive
