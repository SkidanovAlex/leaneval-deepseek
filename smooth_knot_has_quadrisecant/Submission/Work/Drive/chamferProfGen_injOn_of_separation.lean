import Mathlib
import Submission.Work.Drive.chamferProfDefs

open LeanEval.KnotTheory.Quadrisecant

set_option linter.unusedVariables false

namespace Work.Drive


/-! ## Vector-space helpers about a point of a segment -/

/-- A convex combination of `A` and `B` that equals `A` is either at `A` (`c = 0`) or `A = B`. -/
private lemma cc_eq_left {A B : Space} {c : ℝ}
    (h : (1 - c) • A + c • B = A) : c = 0 ∨ A = B := by
  have key : c • (B - A) = 0 := by
    have h1 : (1 - c) • A + c • B - A = c • (B - A) := by module
    rw [h, sub_self] at h1
    exact h1.symm
  rcases smul_eq_zero.mp key with hc | hBA
  · exact Or.inl hc
  · exact Or.inr (sub_eq_zero.mp hBA).symm

/-- A convex combination of `A` and `B` that equals `B` is either at `B` (`c = 1`) or `A = B`. -/
private lemma cc_eq_right {A B : Space} {c : ℝ}
    (h : (1 - c) • A + c • B = B) : c = 1 ∨ A = B := by
  have key : (1 - c) • (A - B) = 0 := by
    have h1 : (1 - c) • A + c • B - B = (1 - c) • (A - B) := by module
    rw [h, sub_self] at h1
    exact h1.symm
  rcases smul_eq_zero.mp key with hc | hBA
  · exact Or.inl (by linarith)
  · exact Or.inr (sub_eq_zero.mp hBA)

/-- Two points of the segment `[A,B]` coincide only if they have the same parameter or `A = B`. -/
private lemma cc_inj {A B : Space} {c₁ c₂ : ℝ}
    (h : (1 - c₁) • A + c₁ • B = (1 - c₂) • A + c₂ • B) : c₁ = c₂ ∨ A = B := by
  have key : (c₁ - c₂) • (B - A) = 0 := by
    have h1 : (1 - c₁) • A + c₁ • B - ((1 - c₂) • A + c₂ • B) = (c₁ - c₂) • (B - A) := by
      module
    rw [h, sub_self] at h1
    exact h1.symm
  rcases smul_eq_zero.mp key with hcc | hBA
  · exact Or.inl (sub_eq_zero.mp hcc)
  · exact Or.inr (sub_eq_zero.mp hBA).symm

/-! ## The four branch parameters of the generalised chamfer profile

`chamferProfGen r D lay a b σ` runs, on the profile variable `u ∈ [0,1]`:

* `u ≤ 1/2`: the retained arc, at the fraction `a + (1-2a)·(2u)`;
* `u ≤ 1/2 + lay/2`: the head chamfer, the segment from `sweepArc' (1-a)` to `sweepChord' (1-b)`,
  with parameter `(2u-1)/lay`;
* `u ≤ 1 - lay/2`: the chord, at the fraction `(1-b) - ((u-(1/2+lay/2))/(1/2-lay))·(1-2b)`;
* else: the tail chamfer, the segment from `sweepChord' b` to `sweepArc' a`, with parameter
  `(u-(1-lay/2))/(lay/2)`.

The lemmas below record, for each branch, that its parameter lies in the required interval and is
strictly monotone in `u` (plus the two endpoint values of the arc and the head/tail parameters). -/

/-- Branch 1: the arc fraction lies in `[a, 1-a]`. -/
private lemma arcF_mem {a w : ℝ} (ha : a < 1 / 2) (hw0 : 0 ≤ w) (hw : w ≤ 1 / 2) :
    a + (1 - 2 * a) * (2 * w) ∈ Set.Icc a (1 - a) := by
  have hcoef : 0 ≤ 1 - 2 * a := by linarith
  constructor
  · have : 0 ≤ (1 - 2 * a) * (2 * w) := mul_nonneg hcoef (by linarith)
    linarith
  · have h2w : 2 * w ≤ 1 := by linarith
    have h := mul_le_mul_of_nonneg_left h2w hcoef
    have h' : (1 - 2 * a) * (2 * w) ≤ 1 - 2 * a := by simpa using h
    linarith

/-- Branch 1: the arc fraction is strictly increasing in `w`. -/
private lemma arcF_strict {a w₁ w₂ : ℝ} (ha : a < 1 / 2) (h : w₁ < w₂) :
    a + (1 - 2 * a) * (2 * w₁) < a + (1 - 2 * a) * (2 * w₂) := by
  have hcoef : 0 < 1 - 2 * a := by linarith
  have h2 : 2 * w₁ < 2 * w₂ := by linarith
  have h3 := mul_lt_mul_of_pos_left h2 hcoef
  linarith

/-- Branch 1: the arc fraction equals `a` exactly at `w = 0`. -/
private lemma arcF_eq_a {a w : ℝ} (ha : a < 1 / 2) :
    a + (1 - 2 * a) * (2 * w) = a ↔ w = 0 := by
  constructor
  · intro h
    have h2 : (1 - 2 * a) * (2 * w) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (by linarith)
    · linarith
  · intro h; rw [h]; ring

/-- Branch 1: the arc fraction equals `1 - a` exactly at `w = 1/2`. -/
private lemma arcF_eq_one_sub {a w : ℝ} (ha : a < 1 / 2) :
    a + (1 - 2 * a) * (2 * w) = 1 - a ↔ w = 1 / 2 := by
  constructor
  · intro h
    have hc : (1 - 2 * a) ≠ 0 := by linarith
    have h2 : (1 - 2 * a) * (2 * w) = (1 - 2 * a) * 1 := by linarith
    have h3 : 2 * w = 1 := mul_left_cancel₀ hc h2
    linarith
  · intro h; rw [h]; ring

/-- Branch 2: the chamfer parameter is positive. -/
private lemma headF_pos {lay w : ℝ} (hlay : 0 < lay) (h : ¬ w ≤ 1 / 2) :
    0 < (2 * w - 1) / lay := div_pos (by linarith [not_le.mp h]) hlay

/-- Branch 2: the chamfer parameter lies in `[0,1]`. -/
private lemma headF_mem {lay w : ℝ} (hlay : 0 < lay) (h1 : ¬ w ≤ 1 / 2)
    (h2 : w ≤ 1 / 2 + lay / 2) : (2 * w - 1) / lay ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(headF_pos hlay h1).le, by rw [div_le_one hlay]; linarith⟩

/-- Branch 2: the chamfer parameter is strictly increasing in `w`. -/
private lemma headF_strict {lay w₁ w₂ : ℝ} (hlay : 0 < lay) (h : w₁ < w₂) :
    (2 * w₁ - 1) / lay < (2 * w₂ - 1) / lay :=
  div_lt_div_of_pos_right (by linarith) hlay

/-- Branch 2: the chamfer parameter vanishes exactly at `w = 1/2`. -/
private lemma headF_eq_zero {lay w : ℝ} (hlay : 0 < lay) :
    (2 * w - 1) / lay = 0 ↔ w = 1 / 2 := by
  constructor
  · intro h
    have h2 : 2 * w - 1 = 0 := by
      have := congrArg (fun x => x * lay) h
      rwa [div_mul_cancel₀ _ (ne_of_gt hlay), zero_mul] at this
    linarith
  · intro h; rw [h]; ring_nf

/-- Branch 2: the chamfer parameter equals one exactly at `w = 1/2 + lay/2`. -/
private lemma headF_eq_one {lay w : ℝ} (hlay : 0 < lay) :
    (2 * w - 1) / lay = 1 ↔ w = 1 / 2 + lay / 2 := by
  constructor
  · intro h
    have h2 : 2 * w - 1 = lay := by
      have := congrArg (fun x => x * lay) h
      rwa [div_mul_cancel₀ _ (ne_of_gt hlay), one_mul] at this
    linarith
  · intro h
    rw [h]
    have h2 : 2 * (1 / 2 + lay / 2) - 1 = lay := by ring
    rw [h2, div_self (ne_of_gt hlay)]

/-- Branch 3: the chord fraction lies in `[b, 1-b]`. -/
private lemma chordF_mem_Icc {lay b w : ℝ} (hlay : lay < 1 / 2) (hb : b < 1 / 2)
    (h1 : ¬ w ≤ 1 / 2 + lay / 2) (h2 : w ≤ 1 - lay / 2) :
    (1 - b) - ((w - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b) ∈ Set.Icc b (1 - b) := by
  have hden : 0 < 1 / 2 - lay := by linarith
  have ht0 : 0 < (w - (1 / 2 + lay / 2)) / (1 / 2 - lay) :=
    div_pos (by linarith [not_le.mp h1]) hden
  have ht1 : (w - (1 / 2 + lay / 2)) / (1 / 2 - lay) ≤ 1 := by
    rw [div_le_one hden]; linarith
  have hc : 0 < 1 - 2 * b := by linarith
  constructor
  · have h1' : (w - (1 / 2 + lay / 2)) / (1 / 2 - lay) * (1 - 2 * b) ≤ (1 - 2 * b) := by
      simpa using mul_le_mul_of_nonneg_right ht1 hc.le
    linarith
  · have h0' : 0 ≤ (w - (1 / 2 + lay / 2)) / (1 / 2 - lay) * (1 - 2 * b) :=
      mul_nonneg ht0.le hc.le
    linarith

/-- Branch 3: the chord fraction lies in the open interval `(0,1)`. -/
private lemma chordF_mem_Ioo {lay b w : ℝ} (hlay : lay < 1 / 2) (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : ¬ w ≤ 1 / 2 + lay / 2) (h2 : w ≤ 1 - lay / 2) :
    (1 - b) - ((w - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b) ∈ Set.Ioo (0 : ℝ) 1 := by
  have h := chordF_mem_Icc hlay hb h1 h2
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Branch 3: the chord fraction is strictly below `1 - b` at the (open) start of the branch. -/
private lemma chordF_lt {lay b w : ℝ} (hlay : lay < 1 / 2) (hb : b < 1 / 2)
    (h1 : ¬ w ≤ 1 / 2 + lay / 2) :
    (1 - b) - ((w - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b) < 1 - b := by
  have hden : 0 < 1 / 2 - lay := by linarith
  have ht0 : 0 < (w - (1 / 2 + lay / 2)) / (1 / 2 - lay) :=
    div_pos (by linarith [not_le.mp h1]) hden
  have hc : 0 < 1 - 2 * b := by linarith
  have := mul_pos ht0 hc
  linarith

/-- Branch 3: the chord fraction is strictly decreasing in `w`. -/
private lemma chordF_strict {lay b w₁ w₂ : ℝ} (hlay : lay < 1 / 2) (hb : b < 1 / 2) (h : w₁ < w₂) :
    (1 - b) - ((w₂ - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b)
      < (1 - b) - ((w₁ - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b) := by
  have hden : 0 < 1 / 2 - lay := by linarith
  have ht : (w₁ - (1 / 2 + lay / 2)) / (1 / 2 - lay)
      < (w₂ - (1 / 2 + lay / 2)) / (1 / 2 - lay) :=
    div_lt_div_of_pos_right (by linarith) hden
  have hc : 0 < 1 - 2 * b := by linarith
  have := mul_lt_mul_of_pos_right ht hc
  linarith

/-- Branch 4: the chamfer parameter is positive. -/
private lemma tailF_pos {lay w : ℝ} (hlay : 0 < lay) (h : ¬ w ≤ 1 - lay / 2) :
    0 < (w - (1 - lay / 2)) / (lay / 2) :=
  div_pos (by linarith [not_le.mp h]) (by linarith)

/-- Branch 4: the chamfer parameter is below one for `w < 1`. -/
private lemma tailF_lt_one {lay w : ℝ} (hlay : 0 < lay) (hw : w < 1) :
    (w - (1 - lay / 2)) / (lay / 2) < 1 := by
  rw [div_lt_one (by linarith : 0 < lay / 2)]; linarith

/-- Branch 4: the chamfer parameter lies in `[0,1]`. -/
private lemma tailF_mem {lay w : ℝ} (hlay : 0 < lay) (hw : w < 1) (h : ¬ w ≤ 1 - lay / 2) :
    (w - (1 - lay / 2)) / (lay / 2) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(tailF_pos hlay h).le, (tailF_lt_one hlay hw).le⟩

/-- Branch 4: the chamfer parameter is strictly increasing in `w`. -/
private lemma tailF_strict {lay w₁ w₂ : ℝ} (hlay : 0 < lay) (h : w₁ < w₂) :
    (w₁ - (1 - lay / 2)) / (lay / 2) < (w₂ - (1 - lay / 2)) / (lay / 2) :=
  div_lt_div_of_pos_right (by linarith) (by linarith)

/-- Branch 4: the chamfer parameter equals one exactly at `w = 1`. -/
private lemma tailF_eq_one {lay w : ℝ} (hlay : 0 < lay) :
    (w - (1 - lay / 2)) / (lay / 2) = 1 ↔ w = 1 := by
  constructor
  · intro h
    have h2 : w - (1 - lay / 2) = lay / 2 := by
      have := congrArg (fun x => x * (lay / 2)) h
      rwa [div_mul_cancel₀ _ (by linarith : lay / 2 ≠ 0), one_mul] at this
    linarith
  · intro h
    rw [h]
    have h2 : (1 : ℝ) - (1 - lay / 2) = lay / 2 := by ring
    rw [h2, div_self (by linarith : lay / 2 ≠ 0)]

/-! ## The injectivity of the generalised chamfer profile -/

/-- **Injectivity of the generalised chamfer profile from the separation statements.**  The
profile `chamferProfGen r D lay a b σ` runs through the retained arc (`[a, 1-a]`), the head
chamfer, the chord (`[b, 1-b]`) and the tail chamfer.  If the arc and the chord are each injective
on their own intervals, if the arc meets the chord only at the two endpoint fractions
`1 - b, b ∈ (0,1)` (in the sense of `hac`), if each chamfer meets the arc (resp. the chord) only at
its own endpoint, and if the two chamfers are disjoint, then the profile is injective on `[0,1)`.
-/

theorem chamferProfGen_injOn_of_separation {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {σ lay a b : ℝ} (h0 : 0 < lay) (h1 : lay < 1 / 2) (ha0 : 0 < a) (ha2 : 2 * a < 1)
    (hb0 : 0 < b) (hb2 : 2 * b < 1)
    (harc : Set.InjOn (fun ξ : ℝ => Work.Drive.sweepArc' r D σ ξ) (Set.Icc a (1 - a)))
    (hchord : Set.InjOn (fun ξ : ℝ => Work.Drive.sweepChord' r D σ ξ) (Set.Icc b (1 - b)))
    (hac : ∀ ξ ∈ Set.Icc a (1 - a), ∀ ξ' ∈ Set.Ioo (0 : ℝ) 1,
      Work.Drive.sweepArc' r D σ ξ ≠ Work.Drive.sweepChord' r D σ ξ')
    (harc_head : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc a (1 - a),
      (1 - c) • Work.Drive.sweepArc' r D σ (1 - a) + c • Work.Drive.sweepChord' r D σ (1 - b)
        = Work.Drive.sweepArc' r D σ ξ → ξ = 1 - a)
    (harc_tail : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc a (1 - a),
      (1 - c) • Work.Drive.sweepChord' r D σ b + c • Work.Drive.sweepArc' r D σ a
        = Work.Drive.sweepArc' r D σ ξ → ξ = a)
    (hchord_tail : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc b (1 - b),
      (1 - c) • Work.Drive.sweepChord' r D σ b + c • Work.Drive.sweepArc' r D σ a
        = Work.Drive.sweepChord' r D σ ξ → c = 0)
    (hchord_head : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc b (1 - b),
      (1 - c) • Work.Drive.sweepArc' r D σ (1 - a) + c • Work.Drive.sweepChord' r D σ (1 - b)
        = Work.Drive.sweepChord' r D σ ξ → c = 1)
    (hchamfers : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ c' ∈ Set.Icc (0 : ℝ) 1,
      (1 - c) • Work.Drive.sweepChord' r D σ b + c • Work.Drive.sweepArc' r D σ a
        ≠ (1 - c') • Work.Drive.sweepArc' r D σ (1 - a) + c' • Work.Drive.sweepChord' r D σ (1 - b)) :
    Set.InjOn (Work.Drive.chamferProfGen r D lay a b σ) (Set.Ico (0 : ℝ) 1) := by
/-
The proof is a hand case analysis on the four branches, exactly as in
`Work.Drive.sweepLoopProfile_injOn_of_separation`.  On each branch the value of the profile is
either `sweepArc'`/`sweepChord'` at a fraction depending strictly monotonically on `u`, or a convex
combination of two of the four junction points `arc a`, `arc (1-a)`, `chord b`, `chord (1-b)`.  The
same-branch cases use the injectivity of the arc/chord together with the strict monotonicity of the
parameter; the cross-branch cases use the corresponding separation hypothesis (with the two
degenerate endpoint cases — a chamfer meeting the arc or the chord at its own endpoint — resolved by
`cc_eq_left`/`cc_eq_right` into a contradiction with `hac` or with the strict inequality
`u < 1`). -/
  have ha_lt : a < 1 / 2 := by linarith
  have hb_lt : b < 1 / 2 := by linarith
  have ha_icc : a ∈ Set.Icc a (1 - a) := ⟨le_rfl, by linarith⟩
  have h1a_icc : (1 - a) ∈ Set.Icc a (1 - a) := ⟨by linarith, le_rfl⟩
  have hb_ioo : b ∈ Set.Ioo (0 : ℝ) 1 := ⟨hb0, by linarith⟩
  have h1b_ioo : (1 - b) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h1b_icc : (1 - b) ∈ Set.Icc b (1 - b) := ⟨by linarith, le_rfl⟩
  intro w₁ hw₁ w₂ hw₂ heq
  have main : ∀ w₁ w₂ : ℝ, w₁ ∈ Set.Ico (0 : ℝ) 1 → w₂ ∈ Set.Ico (0 : ℝ) 1 → w₁ < w₂ →
      chamferProfGen r D lay a b σ w₁ = chamferProfGen r D lay a b σ w₂ → False := by
    intro w₁ w₂ hw₁ hw₂ hlt heq
    have hvalA : ∀ w : ℝ, w ≤ 1 / 2 → chamferProfGen r D lay a b σ w
        = sweepArc' r D σ (a + (1 - 2 * a) * (2 * w)) :=
      fun w hu1 => chamferProfGen_arc D hu1
    have hvalB : ∀ w : ℝ, ¬ w ≤ 1 / 2 → w ≤ 1 / 2 + lay / 2 →
        chamferProfGen r D lay a b σ w = (1 - (2 * w - 1) / lay) • sweepArc' r D σ (1 - a)
          + ((2 * w - 1) / lay) • sweepChord' r D σ (1 - b) :=
      fun w hu1 hu2 => chamferProfGen_head D hu1 hu2
    have hvalC : ∀ w : ℝ, ¬ w ≤ 1 / 2 → ¬ w ≤ 1 / 2 + lay / 2 → w ≤ 1 - lay / 2 →
        chamferProfGen r D lay a b σ w
          = sweepChord' r D σ ((1 - b) - ((w - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b)) :=
      fun w hu1 hu2 hu3 => chamferProfGen_chord D hu1 hu2 hu3
    have hvalD : ∀ w : ℝ, ¬ w ≤ 1 / 2 → ¬ w ≤ 1 / 2 + lay / 2 → ¬ w ≤ 1 - lay / 2 →
        chamferProfGen r D lay a b σ w = (1 - (w - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D σ b
          + ((w - (1 - lay / 2)) / (lay / 2)) • sweepArc' r D σ a :=
      fun w hu1 hu2 hu3 => chamferProfGen_tail D hu1 hu2 hu3
    by_cases h11 : w₁ ≤ 1 / 2
    · by_cases h12 : w₂ ≤ 1 / 2
      · -- arc / arc
        rw [hvalA w₁ h11, hvalA w₂ h12] at heq
        exact absurd (harc (arcF_mem ha_lt hw₁.1 h11) (arcF_mem ha_lt hw₂.1 h12) heq)
          (ne_of_lt (arcF_strict ha_lt hlt))
      · by_cases h13 : w₂ ≤ 1 / 2 + lay / 2
        · -- arc / head chamfer
          rw [hvalA w₁ h11, hvalB w₂ h12 h13] at heq
          have hξeq : a + (1 - 2 * a) * (2 * w₁) = 1 - a :=
            harc_head ((2 * w₂ - 1) / lay) (headF_mem h0 h12 h13)
              (a + (1 - 2 * a) * (2 * w₁)) (arcF_mem ha_lt hw₁.1 h11) heq.symm
          rw [hξeq] at heq
          rcases cc_eq_left (A := sweepArc' r D σ (1 - a)) (B := sweepChord' r D σ (1 - b))
            heq.symm with hc0 | hAB
          · have hw2 : w₂ = 1 / 2 := (headF_eq_zero h0).mp hc0
            have hw1 : w₁ = 1 / 2 := (arcF_eq_one_sub ha_lt).mp hξeq
            linarith
          · exact hac (1 - a) h1a_icc (1 - b) h1b_ioo hAB
        · by_cases h14 : w₂ ≤ 1 - lay / 2
          · -- arc / chord
            rw [hvalA w₁ h11, hvalC w₂ h12 h13 h14] at heq
            exact hac (a + (1 - 2 * a) * (2 * w₁)) (arcF_mem ha_lt hw₁.1 h11)
              ((1 - b) - ((w₂ - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b))
              (chordF_mem_Ioo h1 hb0 hb_lt h13 h14) heq
          · -- arc / tail chamfer
            rw [hvalA w₁ h11, hvalD w₂ h12 h13 h14] at heq
            have hξeq : a + (1 - 2 * a) * (2 * w₁) = a :=
              harc_tail ((w₂ - (1 - lay / 2)) / (lay / 2)) (tailF_mem h0 hw₂.2 h14)
                (a + (1 - 2 * a) * (2 * w₁)) (arcF_mem ha_lt hw₁.1 h11) heq.symm
            rw [hξeq] at heq
            rcases cc_eq_right (A := sweepChord' r D σ b) (B := sweepArc' r D σ a) heq.symm
              with ht1 | hAB
            · have hw2 : w₂ = 1 := (tailF_eq_one h0).mp ht1
              linarith [hw₂.2]
            · exact hac a ha_icc b hb_ioo hAB.symm
    · by_cases h1b : w₁ ≤ 1 / 2 + lay / 2
      · by_cases h22 : w₂ ≤ 1 / 2 + lay / 2
        · -- head chamfer / head chamfer
          have h21 : ¬ w₂ ≤ 1 / 2 := by intro h; linarith [not_le.mp h11, hlt, h]
          rw [hvalB w₁ h11 h1b, hvalB w₂ h21 h22] at heq
          rcases cc_inj (A := sweepArc' r D σ (1 - a)) (B := sweepChord' r D σ (1 - b)) heq
            with heq' | hAB
          · exact absurd heq' (ne_of_lt (headF_strict h0 hlt))
          · exact hac (1 - a) h1a_icc (1 - b) h1b_ioo hAB
        · by_cases h23 : w₂ ≤ 1 - lay / 2
          · -- head chamfer / chord
            have h21 : ¬ w₂ ≤ 1 / 2 := by intro h; linarith [not_le.mp h11, hlt, h]
            rw [hvalB w₁ h11 h1b, hvalC w₂ h21 h22 h23] at heq
            have hc₁ : (2 * w₁ - 1) / lay ∈ Set.Icc (0 : ℝ) 1 := headF_mem h0 h11 h1b
            have hφ : (1 - b) - ((w₂ - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b)
                ∈ Set.Icc b (1 - b) := chordF_mem_Icc h1 hb_lt h22 h23
            have hc₁eq : (2 * w₁ - 1) / lay = 1 :=
              hchord_head ((2 * w₁ - 1) / lay) hc₁
                ((1 - b) - ((w₂ - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b)) hφ heq
            rw [hc₁eq] at heq
            simp only [sub_self, zero_smul, zero_add, one_smul] at heq
            have hltφ : (1 - b) - ((w₂ - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b)
                < 1 - b := chordF_lt h1 hb_lt h22
            have := hchord h1b_icc hφ heq
            linarith
          · -- head chamfer / tail chamfer
            have h21 : ¬ w₂ ≤ 1 / 2 := by intro h; linarith [not_le.mp h11, hlt, h]
            rw [hvalB w₁ h11 h1b, hvalD w₂ h21 h22 h23] at heq
            exact hchamfers ((w₂ - (1 - lay / 2)) / (lay / 2)) (tailF_mem h0 hw₂.2 h23)
              ((2 * w₁ - 1) / lay) (headF_mem h0 h11 h1b) heq.symm
      · by_cases h1c : w₁ ≤ 1 - lay / 2
        · by_cases h2c : w₂ ≤ 1 - lay / 2
          · -- chord / chord
            have h21 : ¬ w₂ ≤ 1 / 2 + lay / 2 := by intro h; linarith [not_le.mp h1b, hlt, h]
            have h20 : ¬ w₂ ≤ 1 / 2 := by intro h; linarith [not_le.mp h11, hlt, h]
            rw [hvalC w₁ h11 h1b h1c, hvalC w₂ h20 h21 h2c] at heq
            have hne : (1 - b) - ((w₁ - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b)
                ≠ (1 - b) - ((w₂ - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b) :=
              ne_of_gt (chordF_strict h1 hb_lt hlt)
            exact absurd (hchord (chordF_mem_Icc h1 hb_lt h1b h1c)
              (chordF_mem_Icc h1 hb_lt h21 h2c) heq) hne
          · -- chord / tail chamfer
            have h21 : ¬ w₂ ≤ 1 / 2 + lay / 2 := by intro h; linarith [not_le.mp h1b, hlt, h]
            have h20 : ¬ w₂ ≤ 1 / 2 := by intro h; linarith [not_le.mp h11, hlt, h]
            rw [hvalC w₁ h11 h1b h1c, hvalD w₂ h20 h21 h2c] at heq
            have ht0 : (w₂ - (1 - lay / 2)) / (lay / 2) = 0 :=
              hchord_tail ((w₂ - (1 - lay / 2)) / (lay / 2)) (tailF_mem h0 hw₂.2 h2c)
                ((1 - b) - ((w₁ - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b))
                (chordF_mem_Icc h1 hb_lt h1b h1c) heq.symm
            have := tailF_pos h0 h2c
            linarith
        · by_cases h2c : w₂ ≤ 1 - lay / 2
          · -- impossible order of the branches
            linarith [not_le.mp h1c, hlt, h2c]
          · -- tail chamfer / tail chamfer
            have h20 : ¬ w₂ ≤ 1 / 2 := by intro h; linarith [not_le.mp h11, hlt, h]
            have h21 : ¬ w₂ ≤ 1 / 2 + lay / 2 := by intro h; linarith [not_le.mp h1b, hlt, h]
            rw [hvalD w₁ h11 h1b h1c, hvalD w₂ h20 h21 h2c] at heq
            rcases cc_inj (A := sweepChord' r D σ b) (B := sweepArc' r D σ a) heq with heq' | hAB
            · exact absurd heq' (ne_of_lt (tailF_strict h0 hlt))
            · exact hac a ha_icc b hb_ioo hAB.symm
  rcases lt_trichotomy w₁ w₂ with hlt | heq' | hgt
  · exact (main w₁ w₂ hw₁ hw₂ hlt heq).elim
  · exact heq'
  · exact (main w₂ w₁ hw₂ hw₁ hgt heq.symm).elim

end Work.Drive
