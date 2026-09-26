import Mathlib
import Submission.Work.Drive.sweepLoopProfile_uniformCont_loop

/-!
# Injectivity of the chamfered sweep profile from the four separation statements

`sweepLoopProfile r D lam s : ℝ → Space` is the chamfered sweep loop written in terms of its
*profile* variable `w`; on `[0,1]` it runs

* `w ∈ [0, 1/2]`          : the retained arc, from fraction `lam` to fraction `1-lam`;
* `w ∈ [1/2, 1/2+lam/2]`  : the head chamfer, the segment from `sweepArc' (1-lam)` to
  `sweepChord' (1-lam)`;
* `w ∈ [1/2+lam/2, 1-lam/2]` : the chord, from fraction `1-lam` back to fraction `lam`;
* `w ∈ [1-lam/2, 1]`      : the tail chamfer, the segment from `sweepChord' lam` to
  `sweepArc' lam`.

If the retained arc and the chord are each injective on `[0,1]`, if the arc meets the chord only
at the two endpoints of the loop, if each chamfer meets the retained arc (resp. the chord) only
at its own endpoint, and if the two chamfers are disjoint, then the profile loop is injective on
`[0,1)` — that is, it is a simple closed curve.  This is the purely combinatorial (point-set)
part of "the chamfered sweep loop is a knot for small `lam`"; the five separation hypotheses are
the geometric content supplied by the `O`-avoidance of the band arc.

The proof is a hand case analysis on the four branches of the profile loop (with the "impossible"
branch pairs — those whose order contradicts `w₁ < w₂` — disposed of by `linarith`).
-/


namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-! ## Vector-space helpers about a point of a segment -/

/-- A convex combination of `A` and `B` that equals `A` is either at `A` (`c = 0`) or `A = B`. -/
private lemma convex_combo_eq_left {A B : Space} {c : ℝ}
    (h : (1 - c) • A + c • B = A) : c = 0 ∨ A = B := by
  have key : c • (B - A) = 0 := by
    have h1 : (1 - c) • A + c • B - A = c • (B - A) := by module
    rw [h, sub_self] at h1
    exact h1.symm
  rcases smul_eq_zero.mp key with hc | hBA
  · exact Or.inl hc
  · exact Or.inr (sub_eq_zero.mp hBA).symm

/-- A convex combination of `A` and `B` that equals `B` is either at `B` (`c = 1`) or `A = B`. -/
private lemma convex_combo_eq_right {A B : Space} {c : ℝ}
    (h : (1 - c) • A + c • B = B) : c = 1 ∨ A = B := by
  have key : (1 - c) • (A - B) = 0 := by
    have h1 : (1 - c) • A + c • B - B = (1 - c) • (A - B) := by module
    rw [h, sub_self] at h1
    exact h1.symm
  rcases smul_eq_zero.mp key with hc | hBA
  · exact Or.inl (by linarith)
  · exact Or.inr (sub_eq_zero.mp hBA)

/-- Two points of the segment `[A,B]` coincide only if they have the same parameter or `A = B`. -/
private lemma convex_combo_inj {A B : Space} {c₁ c₂ : ℝ}
    (h : (1 - c₁) • A + c₁ • B = (1 - c₂) • A + c₂ • B) : c₁ = c₂ ∨ A = B := by
  have key : (c₁ - c₂) • (B - A) = 0 := by
    have h1 : (1 - c₁) • A + c₁ • B - ((1 - c₂) • A + c₂ • B) = (c₁ - c₂) • (B - A) := by
      module
    rw [h, sub_self] at h1
    exact h1.symm
  rcases smul_eq_zero.mp key with hcc | hBA
  · exact Or.inl (sub_eq_zero.mp hcc)
  · exact Or.inr (sub_eq_zero.mp hBA).symm

/-! ## The four branch arguments of the profile loop -/

/-- Branch 1 (`w ≤ 1/2`): the arc fraction `lam + (1-2*lam)*(2*w)` lies in `[lam, 1-lam]`. -/
private lemma zoneA_mem {lam w : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 4)
    (hw0 : 0 ≤ w) (hw : w ≤ 1 / 2) :
    lam + (1 - 2 * lam) * (2 * w) ∈ Set.Icc lam (1 - lam) := by
  have hcoef : 0 ≤ 1 - 2 * lam := by linarith
  constructor
  · have : 0 ≤ (1 - 2 * lam) * (2 * w) := mul_nonneg hcoef (by linarith)
    linarith
  · have h2w : 2 * w ≤ 1 := by linarith
    have h := mul_le_mul_of_nonneg_left h2w hcoef
    have h' : (1 - 2 * lam) * (2 * w) ≤ 1 - 2 * lam := by simpa using h
    linarith

/-- Branch 1: the arc fraction is strictly increasing in `w`. -/
private lemma zoneA_strict {lam w₁ w₂ : ℝ} (hlam : lam ≤ 1 / 4) (h : w₁ < w₂) :
    lam + (1 - 2 * lam) * (2 * w₁) < lam + (1 - 2 * lam) * (2 * w₂) := by
  have hcoef : 0 < 1 - 2 * lam := by linarith
  have h2 : 2 * w₁ < 2 * w₂ := by linarith
  have h3 := mul_lt_mul_of_pos_left h2 hcoef
  linarith

/-- Branch 1: the arc fraction at `w` is `lam` exactly at `w = 0`. -/
private lemma zoneA_eq_lam {lam w : ℝ} (hlam : lam ≤ 1 / 4) :
    lam + (1 - 2 * lam) * (2 * w) = lam ↔ w = 0 := by
  constructor
  · intro h
    have h2 : (1 - 2 * lam) * (2 * w) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (by linarith)
    · linarith
  · intro h; rw [h]; ring

/-- Branch 1: the arc fraction at `w` is `1 - lam` exactly at `w = 1/2`. -/
private lemma zoneA_eq_one_sub {lam w : ℝ} (hlam : lam ≤ 1 / 4) :
    lam + (1 - 2 * lam) * (2 * w) = 1 - lam ↔ w = 1 / 2 := by
  constructor
  · intro h
    have hc : (1 - 2 * lam) ≠ 0 := by linarith
    have h2 : (1 - 2 * lam) * (2 * w) = (1 - 2 * lam) * 1 := by linarith
    have h3 : 2 * w = 1 := mul_left_cancel₀ hc h2
    linarith
  · intro h; rw [h]; ring

/-- Branch 2 (`1/2 ≤ w ≤ 1/2+lam/2`): the chamfer parameter lies in `[0,1]`. -/
private lemma zoneB_mem {lam w : ℝ} (hlam0 : 0 < lam) (h1 : ¬ w ≤ 1 / 2)
    (h2 : w ≤ 1 / 2 + lam / 2) : (2 * w - 1) / lam ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (by linarith [not_le.mp h1]) hlam0.le
  · rw [div_le_one hlam0]; linarith

/-- Branch 2: the chamfer parameter is strictly increasing in `w`. -/
private lemma zoneB_strict {lam w₁ w₂ : ℝ} (hlam0 : 0 < lam) (h : w₁ < w₂) :
    (2 * w₁ - 1) / lam < (2 * w₂ - 1) / lam :=
  div_lt_div_of_pos_right (by linarith) hlam0

/-- Branch 2: the chamfer parameter vanishes exactly at `w = 1/2`. -/
private lemma zoneB_eq_zero {lam w : ℝ} (hlam0 : 0 < lam) :
    (2 * w - 1) / lam = 0 ↔ w = 1 / 2 := by
  constructor
  · intro h
    have h2 : 2 * w - 1 = 0 := by
      have := congrArg (fun x => x * lam) h
      rwa [div_mul_cancel₀ _ (ne_of_gt hlam0), zero_mul] at this
    linarith
  · intro h; rw [h]; ring_nf

/-- Branch 2: the chamfer parameter equals one exactly at `w = 1/2 + lam/2`. -/
private lemma zoneB_eq_one {lam w : ℝ} (hlam0 : 0 < lam) :
    (2 * w - 1) / lam = 1 ↔ w = 1 / 2 + lam / 2 := by
  constructor
  · intro h
    have h2 : 2 * w - 1 = lam := by
      have := congrArg (fun x => x * lam) h
      rwa [div_mul_cancel₀ _ (ne_of_gt hlam0), one_mul] at this
    linarith
  · intro h
    rw [h]
    have h2 : 2 * (1 / 2 + lam / 2) - 1 = lam := by ring
    rw [h2, div_self (ne_of_gt hlam0)]

/-- Branch 3 (`1/2+lam/2 ≤ w ≤ 1-lam/2`): the chord fraction `2-2w` lies in `[lam, 1-lam]`. -/
private lemma zoneC_mem_Icc {lam w : ℝ} (h1 : ¬ w ≤ 1 / 2 + lam / 2) (h2 : w ≤ 1 - lam / 2) :
    2 - 2 * w ∈ Set.Icc lam (1 - lam) := by
  have hw : 1 / 2 + lam / 2 < w := not_le.mp h1
  constructor <;> linarith

/-- Branch 3: the chord fraction `2-2w` lies in the open interval `(0,1)`. -/
private lemma zoneC_mem_Ioo {lam w : ℝ} (hlam0 : 0 < lam) (h1 : ¬ w ≤ 1 / 2 + lam / 2)
    (h2 : w ≤ 1 - lam / 2) : 2 - 2 * w ∈ Set.Ioo (0 : ℝ) 1 := by
  have hw : 1 / 2 + lam / 2 < w := not_le.mp h1
  constructor <;> linarith

/-- Branch 4 (`1-lam/2 ≤ w ≤ 1`): the chamfer parameter lies in `[0,1]`. -/
private lemma zoneD_mem {lam w : ℝ} (hlam0 : 0 < lam) (hw1 : w < 1) (h : ¬ w ≤ 1 - lam / 2) :
    (w - (1 - lam / 2)) / (lam / 2) ∈ Set.Icc (0 : ℝ) 1 := by
  have hw : 1 - lam / 2 < w := not_le.mp h
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · rw [div_le_one (by linarith)]; linarith

/-- Branch 4: the chamfer parameter is strictly increasing in `w`. -/
private lemma zoneD_strict {lam w₁ w₂ : ℝ} (hlam0 : 0 < lam) (h : w₁ < w₂) :
    (w₁ - (1 - lam / 2)) / (lam / 2) < (w₂ - (1 - lam / 2)) / (lam / 2) :=
  div_lt_div_of_pos_right (by linarith) (by linarith)

/-- Branch 4: the chamfer parameter equals one exactly at `w = 1`. -/
private lemma zoneD_eq_one {lam w : ℝ} (hlam0 : 0 < lam) :
    (w - (1 - lam / 2)) / (lam / 2) = 1 ↔ w = 1 := by
  constructor
  · intro h
    have h2 : w - (1 - lam / 2) = lam / 2 := by
      have := congrArg (fun x => x * (lam / 2)) h
      rwa [div_mul_cancel₀ _ (by linarith : lam / 2 ≠ 0), one_mul] at this
    linarith
  · intro h
    rw [h]
    have h2 : (1 : ℝ) - (1 - lam / 2) = lam / 2 := by ring
    rw [h2, div_self (by linarith : lam / 2 ≠ 0)]

/-! ## The theorem -/

theorem sweepLoopProfile_injOn_of_separation_nt {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lam s : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 4)
    (harc : Set.InjOn (Work.Drive.sweepArc' r D s) (Set.Icc (0 : ℝ) 1))
    (hchord : Set.InjOn (Work.Drive.sweepChord' r D s) (Set.Icc (0 : ℝ) 1))
    (hac : ∀ ξ ∈ Set.Icc lam (1 - lam), ∀ ξ' ∈ Set.Ioo (0 : ℝ) 1,
      Work.Drive.sweepArc' r D s ξ ≠ Work.Drive.sweepChord' r D s ξ')
    (harc_head : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc lam (1 - lam),
      (1 - c) • Work.Drive.sweepArc' r D s (1 - lam) + c • Work.Drive.sweepChord' r D s (1 - lam)
        = Work.Drive.sweepArc' r D s ξ → ξ = 1 - lam)
    (harc_tail : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc lam (1 - lam),
      (1 - c) • Work.Drive.sweepChord' r D s lam + c • Work.Drive.sweepArc' r D s lam
        = Work.Drive.sweepArc' r D s ξ → ξ = lam)
    (hchord_tail : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc lam (1 - lam),
      (1 - c) • Work.Drive.sweepChord' r D s lam + c • Work.Drive.sweepArc' r D s lam
        = Work.Drive.sweepChord' r D s ξ → c = 0)
    (hchord_head : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc lam (1 - lam),
      (1 - c) • Work.Drive.sweepArc' r D s (1 - lam) + c • Work.Drive.sweepChord' r D s (1 - lam)
        = Work.Drive.sweepChord' r D s ξ → c = 1)
    (hchamfers : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ c' ∈ Set.Icc (0 : ℝ) 1,
      (1 - c) • Work.Drive.sweepChord' r D s lam + c • Work.Drive.sweepArc' r D s lam ≠
        (1 - c') • Work.Drive.sweepArc' r D s (1 - lam)
          + c' • Work.Drive.sweepChord' r D s (1 - lam)) :
    Set.InjOn (Work.Drive.sweepLoopProfile r D lam s) (Set.Ico (0 : ℝ) 1) := by
  have h1ml_icc : (1 - lam) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h1ml_ioo : (1 - lam) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hlam_icc : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨hlam0.le, by linarith⟩
  have hlam_ioo : lam ∈ Set.Ioo (0 : ℝ) 1 := ⟨hlam0, by linarith⟩
  intro w₁ hw₁ w₂ hw₂ heq
  have main : ∀ w₁ w₂ : ℝ, w₁ ∈ Set.Ico (0 : ℝ) 1 → w₂ ∈ Set.Ico (0 : ℝ) 1 → w₁ < w₂ →
      Work.Drive.sweepLoopProfile r D lam s w₁
        = Work.Drive.sweepLoopProfile r D lam s w₂ → False := by
    intro w₁ w₂ hw₁ hw₂ hlt heq
    have hvalA : ∀ w : ℝ, w ≤ 1 / 2 →
        Work.Drive.sweepLoopProfile r D lam s w
          = Work.Drive.sweepArc' r D s (lam + (1 - 2 * lam) * (2 * w)) :=
      fun w h => sweepLoopProfile_eq_arc D h
    have hvalB : ∀ w : ℝ, ¬ w ≤ 1 / 2 → w ≤ 1 / 2 + lam / 2 →
        Work.Drive.sweepLoopProfile r D lam s w
          = (1 - (2 * w - 1) / lam) • Work.Drive.sweepArc' r D s (1 - lam)
            + ((2 * w - 1) / lam) • Work.Drive.sweepChord' r D s (1 - lam) :=
      fun w h1 h2 => sweepLoopProfile_eq_lin2 D (le_of_lt (not_le.mp h1)) h2
    have hvalC : ∀ w : ℝ, ¬ w ≤ 1 / 2 → ¬ w ≤ 1 / 2 + lam / 2 → w ≤ 1 - lam / 2 →
        Work.Drive.sweepLoopProfile r D lam s w
          = Work.Drive.sweepChord' r D s (2 - 2 * w) :=
      fun w _ h2 h3 => sweepLoopProfile_eq_chord3 D hlam0 (le_of_lt (not_le.mp h2)) h3
    have hvalD : ∀ w : ℝ, ¬ w ≤ 1 - lam / 2 →
        Work.Drive.sweepLoopProfile r D lam s w
          = (1 - (w - (1 - lam / 2)) / (lam / 2)) • Work.Drive.sweepChord' r D s lam
            + ((w - (1 - lam / 2)) / (lam / 2)) • Work.Drive.sweepArc' r D s lam :=
      fun w h => sweepLoopProfile_eq_lin4 D hlam0 hlam (le_of_lt (not_le.mp h))
    by_cases h11 : w₁ ≤ 1 / 2
    · by_cases h12 : w₂ ≤ 1 / 2
      · -- arc / arc
        have h₁ := hvalA w₁ h11
        have h₂ := hvalA w₂ h12
        rw [h₁, h₂] at heq
        have hξ₁' := zoneA_mem hlam0 hlam hw₁.1 h11
        have hξ₂' := zoneA_mem hlam0 hlam hw₂.1 h12
        have hξ₁ : lam + (1 - 2 * lam) * (2 * w₁) ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨by linarith [hξ₁'.1], by linarith [hξ₁'.2]⟩
        have hξ₂ : lam + (1 - 2 * lam) * (2 * w₂) ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨by linarith [hξ₂'.1], by linarith [hξ₂'.2]⟩
        have hstrict := zoneA_strict hlam hlt
        have := harc hξ₁ hξ₂ heq
        linarith
      · by_cases h13 : w₂ ≤ 1 / 2 + lam / 2
        · -- arc / head chamfer
          have h₁ := hvalA w₁ h11
          have h₂ := hvalB w₂ h12 h13
          rw [h₁, h₂] at heq
          have hξ := zoneA_mem hlam0 hlam hw₁.1 h11
          have hc := zoneB_mem hlam0 h12 h13
          have hξeq : lam + (1 - 2 * lam) * (2 * w₁) = 1 - lam :=
            harc_head ((2 * w₂ - 1) / lam) hc (lam + (1 - 2 * lam) * (2 * w₁)) hξ heq.symm
          rw [hξeq] at heq
          rcases convex_combo_eq_left (A := Work.Drive.sweepArc' r D s (1 - lam))
            (B := Work.Drive.sweepChord' r D s (1 - lam)) heq.symm with hc0 | hAB
          · have hw2 : w₂ = 1 / 2 := (zoneB_eq_zero hlam0).mp hc0
            have hw1 : w₁ = 1 / 2 := (zoneA_eq_one_sub hlam).mp hξeq
            linarith
          · exact hac (1 - lam) ⟨by linarith [hlam], le_rfl⟩ (1 - lam) h1ml_ioo hAB
        · by_cases h14 : w₂ ≤ 1 - lam / 2
          · -- arc / chord
            have h₁ := hvalA w₁ h11
            have h₂ := hvalC w₂ h12 h13 h14
            rw [h₁, h₂] at heq
            have hξ' := zoneA_mem hlam0 hlam hw₁.1 h11
            have hξ : lam + (1 - 2 * lam) * (2 * w₁) ∈ Set.Icc (0 : ℝ) 1 :=
              ⟨by linarith [hξ'.1], by linarith [hξ'.2]⟩
            have hk := zoneC_mem_Ioo hlam0 h13 h14
            exact hac (lam + (1 - 2 * lam) * (2 * w₁)) hξ' (2 - 2 * w₂) hk heq
          · -- arc / tail chamfer
            have h₁ := hvalA w₁ h11
            have h₂ := hvalD w₂ h14
            rw [h₁, h₂] at heq
            have hξ := zoneA_mem hlam0 hlam hw₁.1 h11
            have hc := zoneD_mem hlam0 hw₂.2 h14
            have hξeq : lam + (1 - 2 * lam) * (2 * w₁) = lam :=
              harc_tail ((w₂ - (1 - lam / 2)) / (lam / 2)) hc
                (lam + (1 - 2 * lam) * (2 * w₁)) hξ heq.symm
            rw [hξeq] at heq
            rcases convex_combo_eq_right (A := Work.Drive.sweepChord' r D s lam)
              (B := Work.Drive.sweepArc' r D s lam) heq.symm with hc1 | hAB
            · have hw2 : w₂ = 1 := (zoneD_eq_one hlam0).mp hc1
              linarith [hw₂.2]
            · exact hac lam ⟨le_rfl, by linarith⟩ lam hlam_ioo hAB.symm
    · by_cases h1b : w₁ ≤ 1 / 2 + lam / 2
      · by_cases h22 : w₂ ≤ 1 / 2 + lam / 2
        · -- head chamfer / head chamfer
          have h12 : ¬ w₂ ≤ 1 / 2 := by intro h; linarith [not_le.mp h11, hlt, h]
          have h₁ := hvalB w₁ h11 h1b
          have h₂ := hvalB w₂ h12 h22
          rw [h₁, h₂] at heq
          have hne : (2 * w₁ - 1) / lam ≠ (2 * w₂ - 1) / lam :=
            ne_of_lt (zoneB_strict hlam0 hlt)
          rcases convex_combo_inj (A := Work.Drive.sweepArc' r D s (1 - lam))
            (B := Work.Drive.sweepChord' r D s (1 - lam)) heq with heq' | hAB
          · exact absurd heq' hne
          · exact hac (1 - lam) ⟨by linarith [hlam], le_rfl⟩ (1 - lam) h1ml_ioo hAB
        · by_cases h23 : w₂ ≤ 1 - lam / 2
          · -- head chamfer / chord
            have h12 : ¬ w₂ ≤ 1 / 2 := by intro h; linarith [not_le.mp h11, hlt, h]
            have h₁ := hvalB w₁ h11 h1b
            have h₂ := hvalC w₂ h12 h22 h23
            rw [h₁, h₂] at heq
            have hc1 := zoneB_mem hlam0 h11 h1b
            have hk2 := zoneC_mem_Icc h22 h23
            have hc1eq : (2 * w₁ - 1) / lam = 1 :=
              hchord_head ((2 * w₁ - 1) / lam) hc1 (2 - 2 * w₂) hk2 heq
            rw [hc1eq] at heq
            simp only [sub_self, zero_smul, zero_add, one_smul] at heq
            have hw1 : w₁ = 1 / 2 + lam / 2 := (zoneB_eq_one hlam0).mp hc1eq
            have hk2' := zoneC_mem_Ioo hlam0 h22 h23
            have hk2mem : 2 - 2 * w₂ ∈ Set.Icc (0 : ℝ) 1 := ⟨hk2'.1.le, hk2'.2.le⟩
            have heqlam : 1 - lam = 2 - 2 * w₂ := hchord h1ml_icc hk2mem heq
            linarith
          · -- head chamfer / tail chamfer
            have h12 : ¬ w₂ ≤ 1 / 2 := by intro h; linarith [not_le.mp h11, hlt, h]
            have h₁ := hvalB w₁ h11 h1b
            have h₂ := hvalD w₂ h23
            rw [h₁, h₂] at heq
            have hc1 := zoneB_mem hlam0 h11 h1b
            have hc2 := zoneD_mem hlam0 hw₂.2 h23
            exact hchamfers ((w₂ - (1 - lam / 2)) / (lam / 2)) hc2 ((2 * w₁ - 1) / lam) hc1
              heq.symm
      · by_cases h1c : w₁ ≤ 1 - lam / 2
        · by_cases h2c : w₂ ≤ 1 - lam / 2
          · -- chord / chord
            have h12 : ¬ w₂ ≤ 1 / 2 + lam / 2 := by
              intro h; linarith [not_le.mp h1b, hlt, h]
            have h₁ := hvalC w₁ h11 h1b h1c
            have h₂ := hvalC w₂ (by intro h; linarith [not_le.mp h11, hlt, h]) h12 h2c
            rw [h₁, h₂] at heq
            have hk1 := zoneC_mem_Ioo hlam0 h1b h1c
            have hk2 := zoneC_mem_Ioo hlam0 h12 h2c
            have hk1' : 2 - 2 * w₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨hk1.1.le, hk1.2.le⟩
            have hk2' : 2 - 2 * w₂ ∈ Set.Icc (0 : ℝ) 1 := ⟨hk2.1.le, hk2.2.le⟩
            have := hchord hk1' hk2' heq
            linarith
          · -- chord / tail chamfer
            have h₁ := hvalC w₁ h11 h1b h1c
            have h₂ := hvalD w₂ h2c
            rw [h₁, h₂] at heq
            have hk1 := zoneC_mem_Icc h1b h1c
            have hc2 := zoneD_mem hlam0 hw₂.2 h2c
            have hc2eq : (w₂ - (1 - lam / 2)) / (lam / 2) = 0 :=
              hchord_tail ((w₂ - (1 - lam / 2)) / (lam / 2)) hc2 (2 - 2 * w₁) hk1 heq.symm
            have hpos : 0 < (w₂ - (1 - lam / 2)) / (lam / 2) :=
              div_pos (by linarith [not_le.mp h2c]) (by linarith)
            linarith
        · by_cases h2c : w₂ ≤ 1 - lam / 2
          · -- impossible: `w₁ < w₂` with `w₁ > 1 - lam/2 ≥ w₂`
            linarith [not_le.mp h1c, hlt, h2c]
          · -- tail chamfer / tail chamfer
            have h₁ := hvalD w₁ h1c
            have h₂ := hvalD w₂ h2c
            rw [h₁, h₂] at heq
            have hne : (w₁ - (1 - lam / 2)) / (lam / 2) ≠ (w₂ - (1 - lam / 2)) / (lam / 2) :=
              ne_of_lt (zoneD_strict hlam0 hlt)
            rcases convex_combo_inj (A := Work.Drive.sweepChord' r D s lam)
              (B := Work.Drive.sweepArc' r D s lam) heq with heq' | hAB
            · exact absurd heq' hne
            · exact hac lam ⟨le_rfl, by linarith⟩ lam hlam_ioo hAB.symm
  rcases lt_trichotomy w₁ w₂ with hlt | heq' | hgt
  · exact (main w₁ w₂ hw₁ hw₂ hlt heq).elim
  · exact heq'
  · exact (main w₂ w₁ hw₂ hw₁ hgt heq.symm).elim

end Work.Drive
