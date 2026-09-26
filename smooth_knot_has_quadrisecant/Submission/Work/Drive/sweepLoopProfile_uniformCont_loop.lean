import Mathlib
import Submission.Work.Drive.sweepLoopProfileDefs
import Submission.Work.Drive.sweepLoopChamfer_locallyIntegrable

/-!
# Uniform continuity of the chamfered sweep loop in the profile variable

The main result of this file is `Work.Drive.sweepLoopProfile_uniformCont_loop`: the profile loop
`w ↦ sweepLoopProfile r D lam σ w` is uniformly continuous on `[0,1]` with a modulus that is
*independent* of the chamfer `lam ∈ (0,1/4]` and of the sweep parameter `σ`.

The loop is a concatenation of four pieces, whose junctions move with `lam`:

* on `[0,1/2]` the arc point `sweepArc' r D σ (lam + (1-2*lam)*(2*w))`;
* on `[1/2, 1/2+lam/2]` the straight chamfer between `sweepArc' r D σ (1-lam)` and
  `sweepChord' r D σ (1-lam)`;
* on `[1/2+lam/2, 1-lam/2]` the chord point `sweepChord' r D σ (2-2*w)`;
* on `[1-lam/2, 1]` the straight chamfer between `sweepChord' r D σ lam` and `sweepArc' r D σ lam`.

The estimate is obtained by cutting `[a,b]` at the (moving) junctions
`u₁ = min b (max a 1/2)`, `u₂ = min b (max u₁ (1/2+lam/2))`, `u₃ = min b (max u₂ (1-lam/2))`
and bounding each of the four resulting pieces.  The two "hard" pieces are the chamfers: their
two endpoints differ by `O(lam)` only, and each chamfer is traversed over a profile interval of
length `lam/2`, which is exactly what makes the estimate uniform in `lam`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-! ## Bounds for the clamped lift data -/

/-- The clamped lift data are bounded: there is `A ≥ 1` with `|taR D x| ≤ A` and
`|tbR D x| ≤ A` for all `x`. -/
lemma sweepLift_bound {d : BandArcData} (D : SweepData d) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A := by
  obtain ⟨A₀, hA₀⟩ :=
    (isCompact_univ (X := Set.Icc (0:ℝ) 1)).exists_bound_of_continuousOn D.cont_ta.continuousOn
  obtain ⟨A₁, hA₁⟩ :=
    (isCompact_univ (X := Set.Icc (0:ℝ) 1)).exists_bound_of_continuousOn D.cont_tb.continuousOn
  refine ⟨max 1 (max A₀ A₁), le_max_left _ _, fun x => ⟨?_, ?_⟩⟩
  · have h : |taR D x| ≤ A₀ := by
      have h' := hA₀ (clampI x) (Set.mem_univ _)
      simpa [taR, Real.norm_eq_abs] using h'
    exact h.trans ((le_max_left A₀ A₁).trans (le_max_right (1:ℝ) (max A₀ A₁)))
  · have h : |tbR D x| ≤ A₁ := by
      have h' := hA₁ (clampI x) (Set.mem_univ _)
      simpa [tbR, Real.norm_eq_abs] using h'
    exact h.trans ((le_max_right A₀ A₁).trans (le_max_right (1:ℝ) (max A₀ A₁)))

/-- A point `taR D s + ξ * sweepW' D s` of the retained arc is a convex combination of the two
branch endpoints, hence lies in the interval where `A` bounds the lift data. -/
lemma sweepArc'_arg_abs_le {d : BandArcData} (D : SweepData d) {A : ℝ}
    (hA : ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A) (s ξ : ℝ) (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) :
    |taR D s + ξ * sweepW' D s| ≤ A := by
  have hrew : taR D s + ξ * sweepW' D s = (1 - ξ) * taR D s + ξ * tbR D s := by
    simp only [sweepW']; ring
  rw [hrew]
  exact (sweepLoopChamfer_abs_convex_le h0 h1).trans (max_le (hA s).1 (hA s).2)

/-- Difference of two chord points. -/
lemma sweepChord'_sub (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s ξ ξ' : ℝ) :
    sweepChord' r D s ξ' - sweepChord' r D s ξ
      = (ξ' - ξ) • (r (tbR D s) - r (taR D s)) := by
  simp only [sweepChord']
  module

/-- Splitting helper: if `min b y < x ≤ y` then `min b y = b`. -/
private lemma min_eq_left_of_lt {b x y : ℝ} (h : min b y < x) (hxy : x ≤ y) : min b y = b := by
  rcases le_total b y with hby | hyb
  · exact min_eq_left hby
  · exfalso
    rw [min_eq_right hyb] at h
    linarith


/-- A numerical normal form: `m * b * (a / (n * b)) = m * a / n`. -/
private lemma mul_div_right_const (m : ℝ) {b n a : ℝ} (hb : b ≠ 0) :
    m * b * (a / (n * b)) = m * a / n := by
  rw [← mul_div_assoc, show m * b * a = m * a * b by ring, mul_div_mul_right (m * a) n hb]

/-! ## The value of the profile loop on the four pieces (closed forms) -/

/-- On `[0,1/2]` the profile loop is the arc point at parameter `lam + (1-2*lam)*(2*w)`. -/
lemma sweepLoopProfile_eq_arc {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam s w : ℝ} (hw : w ≤ 1 / 2) :
    sweepLoopProfile r D lam s w = sweepArc' r D s (lam + (1 - 2 * lam) * (2 * w)) := by
  rw [sweepLoopProfile, if_pos hw]

/-- On `[1/2, 1/2+lam/2]` the profile loop is the interpolation between the arc point and the
chord point at fraction `1-lam`. -/
lemma sweepLoopProfile_eq_lin2 {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam s w : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 1 / 2 + lam / 2) :
    sweepLoopProfile r D lam s w
      = (1 - (2 * w - 1) / lam) • sweepArc' r D s (1 - lam)
        + ((2 * w - 1) / lam) • sweepChord' r D s (1 - lam) := by
  rcases lt_or_eq_of_le hw1 with h | h
  · rw [sweepLoopProfile, if_neg (not_le.mpr h), if_pos hw2]
  · subst h
    rw [sweepLoopProfile_eq_arc (D := D) (w := 1 / 2) le_rfl]
    have h1 : lam + (1 - 2 * lam) * (2 * (1 / 2 : ℝ)) = 1 - lam := by ring
    have h2 : (2 * (1 / 2 : ℝ) - 1) / lam = 0 := by simp
    rw [h1, h2]
    simp

/-- On `[1/2+lam/2, 1-lam/2]` the profile loop is the chord point at fraction `2-2*w`. -/
lemma sweepLoopProfile_eq_chord3 {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam s w : ℝ} (hl0 : 0 < lam)
    (hw1 : 1 / 2 + lam / 2 ≤ w) (hw2 : w ≤ 1 - lam / 2) :
    sweepLoopProfile r D lam s w = sweepChord' r D s (2 - 2 * w) := by
  rcases lt_or_eq_of_le hw1 with h | h
  · have h12 : (1 / 2 : ℝ) < w := by linarith
    rw [sweepLoopProfile, if_neg (not_le.mpr h12), if_neg (not_le.mpr h), if_pos hw2]
    have hden : (1 / 2 : ℝ) - lam ≠ 0 := by linarith
    have hkey : ((w - (1 / 2 + lam / 2)) / ((1:ℝ) / 2 - lam)) * ((1:ℝ) - 2 * lam)
        = 2 * (w - (1 / 2 + lam / 2)) := by
      rw [show ((1:ℝ) - 2 * lam) = 2 * ((1:ℝ) / 2 - lam) by ring,
        div_mul_eq_mul_div,
        show (w - (1 / 2 + lam / 2)) * (2 * ((1:ℝ) / 2 - lam))
          = (2 * (w - (1 / 2 + lam / 2))) * ((1:ℝ) / 2 - lam) by ring,
        mul_div_cancel_right₀ _ hden]
    rw [hkey]
    congr 1
    ring
  · subst h
    rw [sweepLoopProfile_eq_lin2 (D := D) (w := 1 / 2 + lam / 2) (by linarith) le_rfl]
    have h2 : (2 * (1 / 2 + lam / 2) - 1) / lam = 1 := by
      rw [show 2 * (1 / 2 + lam / 2) - 1 = lam by ring, div_self (ne_of_gt hl0)]
    have h3 : (2:ℝ) - 2 * (1 / 2 + lam / 2) = 1 - lam := by ring
    rw [h2, h3]
    simp

/-- On `[1-lam/2, 1]` the profile loop is the interpolation between the chord point and the arc
point at fraction `lam`. -/
lemma sweepLoopProfile_eq_lin4 {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam s w : ℝ} (hl0 : 0 < lam) (hl4 : lam ≤ 1 / 4) (hw : 1 - lam / 2 ≤ w) :
    sweepLoopProfile r D lam s w
      = (1 - (w - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D s lam
        + ((w - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D s lam := by
  rcases lt_or_eq_of_le hw with h | h
  · have h12 : (1 / 2 : ℝ) < w := by linarith
    have h23 : (1 / 2 : ℝ) + lam / 2 < w := by linarith
    rw [sweepLoopProfile, if_neg (not_le.mpr h12), if_neg (not_le.mpr h23),
      if_neg (not_le.mpr h)]
  · subst h
    rw [sweepLoopProfile_eq_chord3 (D := D) (w := 1 - lam / 2) hl0 (by linarith) le_rfl]
    have h2 : (2:ℝ) - 2 * (1 - lam / 2) = lam := by ring
    rw [h2]
    have h3 : ((1 - lam / 2) - (1 - lam / 2)) / (lam / 2) = 0 := by simp
    rw [h3]
    simp

/-! ## The main two-point estimate -/

/-- **The two-point estimate.**  For `0 < lam ≤ 1/4` and `a ≤ b` in `[0,1]`, the profile loop
changes by at most `2α + 2·min(1, 2(b-a)/lam)·β`, where `α` bounds the variation of the arc and
chord pieces over profile intervals of length `2(b-a)`, and `β` bounds the length of each
chamfer. -/
lemma sweepLoopProfile_diff_le {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam σ α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hl0 : 0 < lam) (hl4 : lam ≤ 1 / 4)
    {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) (hab : a ≤ b)
    (harc : ∀ x x' : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ x' → x' ≤ 1 → |x - x'| ≤ 2 * (b - a) →
      ‖sweepArc' r D σ x' - sweepArc' r D σ x‖ ≤ α)
    (hbeta : ‖sweepChord' r D σ (1 - lam) - sweepArc' r D σ (1 - lam)‖ ≤ β)
    (hbeta' : ‖sweepChord' r D σ lam - sweepArc' r D σ lam‖ ≤ β)
    (hchord : 2 * ‖r (tbR D σ) - r (taR D σ)‖ * (b - a) ≤ α) :
    ‖sweepLoopProfile r D lam σ b - sweepLoopProfile r D lam σ a‖
      ≤ 2 * α + 2 * (min 1 (2 * (b - a) / lam)) * β := by
  have ha0 : 0 ≤ a := ha.1
  have hb1 : b ≤ 1 := hb.2
  have hd0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hlam0 : 0 ≤ lam := hl0.le
  -- the three moving junctions
  set u1 : ℝ := min b (max a (1 / 2)) with hu1
  set u2 : ℝ := min b (max u1 (1 / 2 + lam / 2)) with hu2
  set u3 : ℝ := min b (max u2 (1 - lam / 2)) with hu3
  have ha1 : a ≤ u1 := by rw [hu1]; exact le_min hab (le_max_left _ _)
  have h1b : u1 ≤ b := by rw [hu1]; exact min_le_left _ _
  have h12 : u1 ≤ u2 := by rw [hu2]; exact le_min h1b (le_max_left _ _)
  have h2b : u2 ≤ b := by rw [hu2]; exact min_le_left _ _
  have h23 : u2 ≤ u3 := by rw [hu3]; exact le_min h2b (le_max_left _ _)
  have h3b : u3 ≤ b := by rw [hu3]; exact min_le_left _ _
  -- where the junctions sit
  have hreg1 : u1 = a ∨ (a ≤ 1 / 2 ∧ u1 ≤ 1 / 2) := by
    by_cases hac : a ≤ 1 / 2
    · refine Or.inr ⟨hac, ?_⟩
      rw [hu1, max_eq_right hac]; exact min_le_right _ _
    · refine Or.inl ?_
      rw [hu1, max_eq_left (le_of_not_ge hac), min_eq_right hab]
  have hreg2 : u2 = u1 ∨ (1 / 2 ≤ u1 ∧ u2 ≤ 1 / 2 + lam / 2) := by
    rcases eq_or_lt_of_le h12 with heq | hlt
    · exact Or.inl heq.symm
    · have hu1ge : 1 / 2 ≤ u1 := by
        by_contra hcon
        push_neg at hcon
        have hu2eq : u2 = u1 := by
          by_cases ha' : a ≤ 1 / 2
          · have hmax : max a (1 / 2) = 1 / 2 := max_eq_right ha'
            have hb_lt : b < 1 / 2 := by
              by_contra hge
              push_neg at hge
              rw [hu1, hmax, min_eq_right hge] at hcon
              linarith
            have hu1b : u1 = b := by rw [hu1, hmax, min_eq_left hb_lt.le]
            rw [hu2, hu1b, max_eq_right (by linarith), min_eq_left (by linarith)]
          · exfalso
            rw [hu1, max_eq_left (le_of_not_ge ha'), min_eq_right hab] at hcon
            exact absurd (le_of_not_ge ha') (not_le.mpr hcon)
        exact absurd hu2eq (ne_of_gt hlt)
      have hu2le : u2 ≤ 1 / 2 + lam / 2 := by
        by_contra hcon
        push_neg at hcon
        have hX : 1 / 2 + lam / 2 < max u1 (1 / 2 + lam / 2) :=
          lt_of_lt_of_le hcon (min_le_right _ _)
        have hu1gt : 1 / 2 + lam / 2 < u1 := by
          by_contra hle
          push_neg at hle
          rw [max_eq_right hle] at hX
          exact absurd hX (lt_irrefl _)
        have hu2eq : u2 = u1 := by
          rw [hu2, max_eq_left hu1gt.le, min_eq_right h1b]
        exact absurd hu2eq (ne_of_gt hlt)
      exact Or.inr ⟨hu1ge, hu2le⟩
  have hreg3 : u3 = u2 ∨ (1 / 2 + lam / 2 ≤ u2 ∧ u3 ≤ 1 - lam / 2) := by
    rcases eq_or_lt_of_le h23 with heq | hlt
    · exact Or.inl heq.symm
    · have hu2ge : 1 / 2 + lam / 2 ≤ u2 := by
        by_contra hcon
        push_neg at hcon
        have hu2b : u2 = b := by
          rw [hu2]
          exact min_eq_left_of_lt (by rw [hu2] at hcon; exact hcon) (le_max_right _ _)
        have hb' : b ≤ 1 - lam / 2 := by rw [← hu2b]; linarith
        have hu3eq : u3 = u2 := by
          rw [hu3, hu2b, max_eq_right hb', min_eq_left hb']
        exact absurd hu3eq (ne_of_gt hlt)
      have hu3le : u3 ≤ 1 - lam / 2 := by
        by_contra hcon
        push_neg at hcon
        have hX : 1 - lam / 2 < max u2 (1 - lam / 2) :=
          lt_of_lt_of_le hcon (min_le_right _ _)
        have hu2gt : 1 - lam / 2 < u2 := by
          by_contra hle
          push_neg at hle
          rw [max_eq_right hle] at hX
          exact absurd hX (lt_irrefl _)
        have hu3eq : u3 = u2 := by
          rw [hu3, max_eq_left hu2gt.le, min_eq_right h2b]
        exact absurd hu3eq (ne_of_gt hlt)
      exact Or.inr ⟨hu2ge, hu3le⟩
  have hreg4 : u3 = b ∨ 1 - lam / 2 ≤ u3 := by
    rcases eq_or_lt_of_le h3b with heq | hlt
    · exact Or.inl heq
    · refine Or.inr ?_
      by_contra hcon
      push_neg at hcon
      have hu3b : u3 = b := by
        rw [hu3]
        exact min_eq_left_of_lt (by rw [hu3] at hcon; exact hcon) (le_max_right _ _)
      exact absurd hu3b (ne_of_lt hlt)
  -- telescoping through the junctions
  have htele : ‖sweepLoopProfile r D lam σ b - sweepLoopProfile r D lam σ a‖
      ≤ ‖sweepLoopProfile r D lam σ u1 - sweepLoopProfile r D lam σ a‖
        + ‖sweepLoopProfile r D lam σ u2 - sweepLoopProfile r D lam σ u1‖
        + ‖sweepLoopProfile r D lam σ u3 - sweepLoopProfile r D lam σ u2‖
        + ‖sweepLoopProfile r D lam σ b - sweepLoopProfile r D lam σ u3‖ := by
    have hdec : sweepLoopProfile r D lam σ b - sweepLoopProfile r D lam σ a
        = (sweepLoopProfile r D lam σ u1 - sweepLoopProfile r D lam σ a)
          + (sweepLoopProfile r D lam σ u2 - sweepLoopProfile r D lam σ u1)
          + (sweepLoopProfile r D lam σ u3 - sweepLoopProfile r D lam σ u2)
          + (sweepLoopProfile r D lam σ b - sweepLoopProfile r D lam σ u3) := by abel
    rw [hdec]
    have h1 := norm_add_le ((sweepLoopProfile r D lam σ u1 - sweepLoopProfile r D lam σ a)
        + (sweepLoopProfile r D lam σ u2 - sweepLoopProfile r D lam σ u1)
        + (sweepLoopProfile r D lam σ u3 - sweepLoopProfile r D lam σ u2))
        (sweepLoopProfile r D lam σ b - sweepLoopProfile r D lam σ u3)
    have h2 := norm_add_le ((sweepLoopProfile r D lam σ u1 - sweepLoopProfile r D lam σ a)
        + (sweepLoopProfile r D lam σ u2 - sweepLoopProfile r D lam σ u1))
        (sweepLoopProfile r D lam σ u3 - sweepLoopProfile r D lam σ u2)
    have h3 := norm_add_le (sweepLoopProfile r D lam σ u1 - sweepLoopProfile r D lam σ a)
        (sweepLoopProfile r D lam σ u2 - sweepLoopProfile r D lam σ u1)
    linarith
  -- piece 1: the arc
  have hterm1 : ‖sweepLoopProfile r D lam σ u1 - sweepLoopProfile r D lam σ a‖ ≤ α := by
    rcases hreg1 with heq | ⟨hale, hu1le⟩
    · rw [heq, sub_self, norm_zero]; exact hα
    · rw [sweepLoopProfile_eq_arc (D := D) (w := u1) hu1le,
        sweepLoopProfile_eq_arc (D := D) (w := a) hale]
      refine harc _ _ ?_ ?_ ?_ ?_ ?_
      · have h : 0 ≤ (1 - 2 * lam) * (2 * a) := mul_nonneg (by linarith) (by linarith)
        linarith
      · have h : (1 - 2 * lam) * (2 * a) ≤ (1 - 2 * lam) * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith
      · have h : 0 ≤ (1 - 2 * lam) * (2 * u1) := mul_nonneg (by linarith) (by linarith)
        linarith
      · have h : (1 - 2 * lam) * (2 * u1) ≤ (1 - 2 * lam) * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith
      · rw [abs_sub_comm]
        have he : lam + (1 - 2 * lam) * (2 * u1) - (lam + (1 - 2 * lam) * (2 * a))
            = 2 * (1 - 2 * lam) * (u1 - a) := by ring
        rw [he, abs_mul]
        have hcoef : |2 * (1 - 2 * lam)| ≤ 2 := by
          rw [abs_of_nonneg (by linarith)]; linarith
        calc |2 * (1 - 2 * lam)| * |u1 - a| ≤ 2 * |u1 - a| :=
              mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
          _ = 2 * (u1 - a) := by rw [abs_of_nonneg (by linarith)]
          _ ≤ 2 * (b - a) := by linarith
  -- piece 2: the first chamfer
  have hterm2 : ‖sweepLoopProfile r D lam σ u2 - sweepLoopProfile r D lam σ u1‖
      ≤ min 1 (2 * (b - a) / lam) * β := by
    rcases hreg2 with heq | ⟨hu1ge, hu2le⟩
    · rw [heq, sub_self, norm_zero]
      exact mul_nonneg (le_min zero_le_one (div_nonneg (by linarith) hlam0)) hβ
    · have hu2ge : 1 / 2 ≤ u2 := by linarith
      rw [sweepLoopProfile_eq_lin2 (D := D) (w := u2) hu2ge hu2le,
        sweepLoopProfile_eq_lin2 (D := D) (w := u1) hu1ge (by linarith)]
      have hsub : ((1 - (2 * u2 - 1) / lam) • sweepArc' r D σ (1 - lam)
            + ((2 * u2 - 1) / lam) • sweepChord' r D σ (1 - lam))
          - ((1 - (2 * u1 - 1) / lam) • sweepArc' r D σ (1 - lam)
            + ((2 * u1 - 1) / lam) • sweepChord' r D σ (1 - lam))
          = ((2 * u2 - 1) / lam - (2 * u1 - 1) / lam)
            • (sweepChord' r D σ (1 - lam) - sweepArc' r D σ (1 - lam)) := by
        module
      rw [hsub, norm_smul, Real.norm_eq_abs]
      have hmin0 : 0 ≤ min 1 (2 * (b - a) / lam) :=
        le_min zero_le_one (div_nonneg (by linarith : (0:ℝ) ≤ 2 * (b - a)) hlam0)
      have ht : |(2 * u2 - 1) / lam - (2 * u1 - 1) / lam| ≤ min 1 (2 * (b - a) / lam) := by
        have he : (2 * u2 - 1) / lam - (2 * u1 - 1) / lam = 2 * (u2 - u1) / lam := by ring
        rw [he, abs_of_nonneg (div_nonneg (by linarith : (0:ℝ) ≤ 2 * (u2 - u1)) hlam0)]
        refine le_min ?_ ?_
        · rw [div_le_one hl0]; linarith
        · exact div_le_div_of_nonneg_right (by linarith) hlam0
      exact mul_le_mul ht hbeta (norm_nonneg _) hmin0
  -- piece 3: the chord
  have hterm3 : ‖sweepLoopProfile r D lam σ u3 - sweepLoopProfile r D lam σ u2‖ ≤ α := by
    rcases hreg3 with heq | ⟨hu2ge, hu3le⟩
    · rw [heq, sub_self, norm_zero]; exact hα
    · have hu3ge : 1 / 2 + lam / 2 ≤ u3 := by linarith
      have hu2le' : u2 ≤ 1 - lam / 2 := by linarith
      rw [sweepLoopProfile_eq_chord3 (D := D) (w := u3) hl0 hu3ge hu3le,
        sweepLoopProfile_eq_chord3 (D := D) (w := u2) hl0 hu2ge hu2le']
      have hsub : sweepChord' r D σ (2 - 2 * u3) - sweepChord' r D σ (2 - 2 * u2)
          = (2 * (u2 - u3)) • (r (tbR D σ) - r (taR D σ)) := by
        rw [sweepChord'_sub]
        congr 1
        ring
      rw [hsub, norm_smul, Real.norm_eq_abs,
        abs_of_nonpos (by linarith : 2 * (u2 - u3) ≤ 0),
        show -(2 * (u2 - u3)) = 2 * (u3 - u2) by ring]
      calc 2 * (u3 - u2) * ‖r (tbR D σ) - r (taR D σ)‖
          = 2 * ‖r (tbR D σ) - r (taR D σ)‖ * (u3 - u2) := by ring
        _ ≤ 2 * ‖r (tbR D σ) - r (taR D σ)‖ * (b - a) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            linarith
        _ ≤ α := hchord
  -- piece 4: the second chamfer
  have hterm4 : ‖sweepLoopProfile r D lam σ b - sweepLoopProfile r D lam σ u3‖
      ≤ min 1 (2 * (b - a) / lam) * β := by
    rcases hreg4 with heq | hu3ge
    · rw [heq, sub_self, norm_zero]
      exact mul_nonneg (le_min zero_le_one (div_nonneg (by linarith) hlam0)) hβ
    · have ha3 : a ≤ u3 := by linarith
      rw [sweepLoopProfile_eq_lin4 (D := D) (w := b) hl0 hl4 (by linarith),
        sweepLoopProfile_eq_lin4 (D := D) (w := u3) hl0 hl4 hu3ge]
      have hsub : ((1 - (b - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D σ lam
            + ((b - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D σ lam)
          - ((1 - (u3 - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D σ lam
            + ((u3 - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D σ lam)
          = ((b - (1 - lam / 2)) / (lam / 2) - (u3 - (1 - lam / 2)) / (lam / 2))
            • (sweepArc' r D σ lam - sweepChord' r D σ lam) := by
        module
      have hb' : ‖sweepArc' r D σ lam - sweepChord' r D σ lam‖ ≤ β := by
        rwa [norm_sub_rev]
      rw [hsub, norm_smul, Real.norm_eq_abs]
      have hmin0 : 0 ≤ min 1 (2 * (b - a) / lam) :=
        le_min zero_le_one (div_nonneg (by linarith : (0:ℝ) ≤ 2 * (b - a)) hlam0)
      have ht : |(b - (1 - lam / 2)) / (lam / 2) - (u3 - (1 - lam / 2)) / (lam / 2)|
          ≤ min 1 (2 * (b - a) / lam) := by
        have he : (b - (1 - lam / 2)) / (lam / 2) - (u3 - (1 - lam / 2)) / (lam / 2)
            = (b - u3) / (lam / 2) := by ring
        rw [he, abs_of_nonneg (div_nonneg (by linarith : (0:ℝ) ≤ b - u3) (by linarith))]
        refine le_min ?_ ?_
        · rw [div_le_one (by linarith : (0:ℝ) < lam / 2)]; linarith
        · rw [show 2 * (b - a) / lam = (b - a) / (lam / 2) by ring]
          exact div_le_div_of_nonneg_right (by linarith) (by linarith)
      exact mul_le_mul ht hb' (norm_nonneg _) hmin0
  linarith [htele, hterm1, hterm2, hterm3, hterm4]

/-! ## The uniform continuity statement -/

theorem sweepLoopProfile_uniformCont_loop {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    (hr : Continuous r) :
    ∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 < θ ∧
      ∀ (lam : ℝ), 0 < lam → lam ≤ 1 / 4 →
        ∀ (σ : ℝ) (w w' : ℝ), w ∈ Set.Icc (0 : ℝ) 1 → w' ∈ Set.Icc (0 : ℝ) 1 →
          |w - w'| ≤ θ →
            ‖Work.Drive.sweepLoopProfile r D lam σ w' - Work.Drive.sweepLoopProfile r D lam σ w‖ ≤ ε := by
  intro ε hε
  obtain ⟨A, hA1, hA⟩ := sweepLift_bound D
  have hApos : (0:ℝ) < A := by linarith
  obtain ⟨B₀, hB₀⟩ :=
    (isCompact_Icc (a := -A) (b := A)).exists_bound_of_continuousOn hr.continuousOn
  set B : ℝ := max 1 B₀ with hBdef
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBpos : (0:ℝ) < B := by linarith
  have hBle : ∀ x : ℝ, |x| ≤ A → ‖r x‖ ≤ B := by
    intro x hx
    have hmem : x ∈ Set.Icc (-A) A := by rw [Set.mem_Icc]; exact abs_le.mp hx
    exact (hB₀ x hmem).trans (le_max_right _ _)
  obtain ⟨ηU, hηUpos, hηU⟩ :=
    (Metric.uniformContinuousOn_iff_le.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hr.continuousOn))
      (ε / 8) (by linarith)
  have hηU' : ∀ x y : ℝ, |x| ≤ A → |y| ≤ A → |x - y| ≤ ηU → ‖r x - r y‖ ≤ ε / 8 := by
    intro x y hx hy hxy
    have hx' : x ∈ Set.Icc (-A) A := by rw [Set.mem_Icc]; exact abs_le.mp hx
    have hy' : y ∈ Set.Icc (-A) A := by rw [Set.mem_Icc]; exact abs_le.mp hy
    have h := hηU x hx' y hy' (by rwa [Real.dist_eq])
    rwa [dist_eq_norm] at h
  set lam₀ : ℝ := min (1 / 4) (min (ε / (16 * B)) (ηU / (2 * A))) with hlam₀def
  have hlam₀pos : 0 < lam₀ :=
    lt_min (by norm_num) (lt_min (div_pos hε (by linarith)) (div_pos hηUpos (by linarith)))
  have hlam₀B : lam₀ ≤ ε / (16 * B) := (min_le_right _ _).trans (min_le_left _ _)
  have hlam₀η : lam₀ ≤ ηU / (2 * A) := (min_le_right _ _).trans (min_le_right _ _)
  set θ : ℝ := min (ηU / (4 * A)) (min (ε / (32 * B)) (ε * lam₀ / (16 * B))) with hθdef
  have hθpos : 0 < θ :=
    lt_min (div_pos hηUpos (by linarith))
      (lt_min (div_pos hε (by linarith)) (div_pos (mul_pos hε hlam₀pos) (by linarith)))
  have hθη : θ ≤ ηU / (4 * A) := min_le_left _ _
  have hθB : θ ≤ ε / (32 * B) := (min_le_right _ _).trans (min_le_left _ _)
  have hθlam : θ ≤ ε * lam₀ / (16 * B) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨θ, hθpos, ?_⟩
  intro lam hl0 hl4 σ w w' hw hw' hww'
  have main : ∀ a b : ℝ, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 → a ≤ b → b - a ≤ θ →
      ‖sweepLoopProfile r D lam σ b - sweepLoopProfile r D lam σ a‖ ≤ ε := by
    intro a b ha hb hab hd
    have hd0 : 0 ≤ b - a := sub_nonneg.mpr hab
    have harc : ∀ x x' : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ x' → x' ≤ 1 → |x - x'| ≤ 2 * (b - a) →
        ‖sweepArc' r D σ x' - sweepArc' r D σ x‖ ≤ ε / 8 := by
      intro x x' hx0 hx1 hx'0 hx'1 hxx'
      have hargs : |taR D σ + x' * sweepW' D σ - (taR D σ + x * sweepW' D σ)| ≤ ηU := by
        rw [show taR D σ + x' * sweepW' D σ - (taR D σ + x * sweepW' D σ)
            = (x' - x) * sweepW' D σ by ring, abs_mul]
        have h1 : |x' - x| ≤ 2 * (b - a) := by rw [abs_sub_comm]; exact hxx'
        calc |x' - x| * |sweepW' D σ| ≤ (2 * (b - a)) * (2 * A) :=
              mul_le_mul h1 (sweepLoopChamfer_sweepW'_abs_le D hA σ) (abs_nonneg _) (by linarith)
          _ ≤ ηU := by
              have h2 : b - a ≤ ηU / (4 * A) := le_trans hd hθη
              have h4 : (2 * (b - a)) * (2 * A) = 4 * A * (b - a) := by ring
              have h5 : 4 * A * (b - a) ≤ ηU := by
                have h6 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 4 * A)
                rwa [mul_div_cancel₀ _ (by linarith : (4:ℝ) * A ≠ 0)] at h6
              linarith [h4, h5]
      exact hηU' _ _ (sweepArc'_arg_abs_le D hA σ x' hx'0 hx'1)
        (sweepArc'_arg_abs_le D hA σ x hx0 hx1) hargs
    have hba : ‖r (tbR D σ) - r (taR D σ)‖ ≤ 2 * B := by
      calc ‖r (tbR D σ) - r (taR D σ)‖ ≤ ‖r (tbR D σ)‖ + ‖r (taR D σ)‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add (hBle _ (hA σ).2) (hBle _ (hA σ).1)
        _ = 2 * B := by ring
    have hchord : 2 * ‖r (tbR D σ) - r (taR D σ)‖ * (b - a) ≤ ε / 8 := by
      have h4 : 4 * B * (b - a) ≤ ε / 8 := by
        have h5 : 4 * B * (b - a) ≤ 4 * B * (ε / (32 * B)) :=
          mul_le_mul_of_nonneg_left (le_trans hd hθB) (by linarith : (0:ℝ) ≤ 4 * B)
        have h6 : 4 * B * (ε / (32 * B)) = ε / 8 := by
          rw [mul_div_right_const 4 (b := B) (a := ε) (ne_of_gt hBpos)]
          ring
        linarith [h5, h6.le, h6.ge]
      calc 2 * ‖r (tbR D σ) - r (taR D σ)‖ * (b - a) ≤ 2 * (2 * B) * (b - a) :=
            mul_le_mul_of_nonneg_right (by linarith) hd0
        _ = 4 * B * (b - a) := by ring
        _ ≤ ε / 8 := h4
    by_cases hsmall : lam ≤ lam₀
    · -- small chamfer: the two endpoints of each chamfer differ by at most `ε/4`
      have hlamη : lam * (2 * A) ≤ ηU := by
        have h1 : lam ≤ ηU / (2 * A) := le_trans hsmall hlam₀η
        have h2 : lam * (2 * A) ≤ ηU / (2 * A) * (2 * A) :=
          mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ 2 * A)
        have h3 : ηU / (2 * A) * (2 * A) = ηU :=
          div_mul_cancel₀ ηU (by linarith : (2:ℝ) * A ≠ 0)
        linarith [h2, h3.le, h3.ge]
      have hsmallB : 2 * B * lam ≤ ε / 8 := by
        have h1 : lam ≤ ε / (16 * B) := le_trans hsmall hlam₀B
        have h2 : 2 * B * lam ≤ 2 * B * (ε / (16 * B)) :=
          mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 2 * B)
        have h3 : 2 * B * (ε / (16 * B)) = ε / 8 := by
          rw [mul_div_right_const 2 (b := B) (a := ε) (ne_of_gt hBpos)]
          ring
        linarith [h2, h3.le, h3.ge]
      have hbeta : ‖sweepChord' r D σ (1 - lam) - sweepArc' r D σ (1 - lam)‖ ≤ ε / 4 := by
        have h1 : ‖sweepChord' r D σ (1 - lam) - r (tbR D σ)‖ ≤ 2 * B * lam := by
          have hsub : sweepChord' r D σ (1 - lam) - r (tbR D σ)
              = lam • (r (taR D σ) - r (tbR D σ)) := by
            simp only [sweepChord']
            module
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl0.le]
          calc lam * ‖r (taR D σ) - r (tbR D σ)‖ ≤ lam * (2 * B) :=
                mul_le_mul_of_nonneg_left (by rw [norm_sub_rev]; exact hba) hl0.le
            _ = 2 * B * lam := by ring
        have h2 : ‖r (tbR D σ) - sweepArc' r D σ (1 - lam)‖ ≤ ε / 8 := by
          have harg : |tbR D σ - (taR D σ + (1 - lam) * sweepW' D σ)| ≤ ηU := by
            rw [show tbR D σ - (taR D σ + (1 - lam) * sweepW' D σ) = lam * sweepW' D σ by
              simp only [sweepW']; ring, abs_mul, abs_of_nonneg hl0.le]
            calc lam * |sweepW' D σ| ≤ lam * (2 * A) :=
                  mul_le_mul_of_nonneg_left (sweepLoopChamfer_sweepW'_abs_le D hA σ) hl0.le
              _ ≤ ηU := hlamη
          exact hηU' _ _ (hA σ).2
            (sweepArc'_arg_abs_le D hA σ (1 - lam) (by linarith) (by linarith)) harg
        have htri := dist_triangle (sweepChord' r D σ (1 - lam)) (r (tbR D σ))
          (sweepArc' r D σ (1 - lam))
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at htri
        calc ‖sweepChord' r D σ (1 - lam) - sweepArc' r D σ (1 - lam)‖
            ≤ ‖sweepChord' r D σ (1 - lam) - r (tbR D σ)‖
              + ‖r (tbR D σ) - sweepArc' r D σ (1 - lam)‖ := htri
          _ ≤ 2 * B * lam + ε / 8 := add_le_add h1 h2
          _ ≤ ε / 4 := by linarith
      have hbeta' : ‖sweepChord' r D σ lam - sweepArc' r D σ lam‖ ≤ ε / 4 := by
        have h1 : ‖sweepChord' r D σ lam - r (taR D σ)‖ ≤ 2 * B * lam := by
          have hsub : sweepChord' r D σ lam - r (taR D σ)
              = lam • (r (tbR D σ) - r (taR D σ)) := by
            simp only [sweepChord']
            module
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl0.le]
          calc lam * ‖r (tbR D σ) - r (taR D σ)‖ ≤ lam * (2 * B) :=
                mul_le_mul_of_nonneg_left hba hl0.le
            _ = 2 * B * lam := by ring
        have h2 : ‖r (taR D σ) - sweepArc' r D σ lam‖ ≤ ε / 8 := by
          have harg : |taR D σ - (taR D σ + lam * sweepW' D σ)| ≤ ηU := by
            rw [show taR D σ - (taR D σ + lam * sweepW' D σ) = -(lam * sweepW' D σ) by ring,
              abs_neg, abs_mul, abs_of_nonneg hl0.le]
            calc lam * |sweepW' D σ| ≤ lam * (2 * A) :=
                  mul_le_mul_of_nonneg_left (sweepLoopChamfer_sweepW'_abs_le D hA σ) hl0.le
              _ ≤ ηU := hlamη
          exact hηU' _ _ (hA σ).1
            (sweepArc'_arg_abs_le D hA σ lam hl0.le (by linarith)) harg
        have htri := dist_triangle (sweepChord' r D σ lam) (r (taR D σ))
          (sweepArc' r D σ lam)
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at htri
        calc ‖sweepChord' r D σ lam - sweepArc' r D σ lam‖
            ≤ ‖sweepChord' r D σ lam - r (taR D σ)‖
              + ‖r (taR D σ) - sweepArc' r D σ lam‖ := htri
          _ ≤ 2 * B * lam + ε / 8 := add_le_add h1 h2
          _ ≤ ε / 4 := by linarith
      have h := sweepLoopProfile_diff_le (D := D) (σ := σ) (α := ε / 8) (β := ε / 4)
        (by linarith) (by linarith) hl0 hl4 ha hb hab harc hbeta hbeta' hchord
      have hmin : min 1 (2 * (b - a) / lam) * (ε / 4) ≤ ε / 4 := by
        have h1 : min 1 (2 * (b - a) / lam) ≤ 1 := min_le_left _ _
        nlinarith [hε]
      linarith
    · -- large chamfer: bound each chamfer crudely by `2*B` and use `lam ≥ lam₀`
      have hbig : lam₀ ≤ lam := le_of_lt (not_le.mp hsmall)
      have hbound : ∀ ξ : ℝ, (ξ = lam ∨ ξ = 1 - lam) →
          ‖sweepArc' r D σ ξ‖ ≤ B ∧ ‖sweepChord' r D σ ξ‖ ≤ B := by
        intro ξ hξ
        have hξ0 : 0 ≤ ξ := by
          rcases hξ with h | h
          · rw [h]; exact hl0.le
          · rw [h]; linarith
        have hξ1 : ξ ≤ 1 := by
          rcases hξ with h | h
          · rw [h]; linarith
          · rw [h]; linarith
        constructor
        · exact hBle _ (sweepArc'_arg_abs_le D hA σ ξ hξ0 hξ1)
        · calc ‖sweepChord' r D σ ξ‖
              = ‖(1 - ξ) • r (taR D σ) + ξ • r (tbR D σ)‖ := rfl
            _ ≤ (1 - ξ) * ‖r (taR D σ)‖ + ξ * ‖r (tbR D σ)‖ := by
                calc ‖(1 - ξ) • r (taR D σ) + ξ • r (tbR D σ)‖
                    ≤ ‖(1 - ξ) • r (taR D σ)‖ + ‖ξ • r (tbR D σ)‖ := norm_add_le _ _
                  _ = (1 - ξ) * ‖r (taR D σ)‖ + ξ * ‖r (tbR D σ)‖ := by
                      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
                        Real.norm_of_nonneg hξ0]
            _ ≤ (1 - ξ) * B + ξ * B :=
                add_le_add (mul_le_mul_of_nonneg_left (hBle _ (hA σ).1) (by linarith))
                  (mul_le_mul_of_nonneg_left (hBle _ (hA σ).2) hξ0)
            _ ≤ B := by nlinarith [hξ0, hξ1]
      have hb2 : ‖sweepChord' r D σ (1 - lam) - sweepArc' r D σ (1 - lam)‖ ≤ 2 * B := by
        have h1 := (hbound (1 - lam) (Or.inr rfl)).1
        have h2 := (hbound (1 - lam) (Or.inr rfl)).2
        have htri := dist_triangle (sweepChord' r D σ (1 - lam)) 0 (sweepArc' r D σ (1 - lam))
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, sub_zero, zero_sub, norm_neg] at htri
        linarith
      have hb2' : ‖sweepChord' r D σ lam - sweepArc' r D σ lam‖ ≤ 2 * B := by
        have h1 := (hbound lam (Or.inl rfl)).1
        have h2 := (hbound lam (Or.inl rfl)).2
        have htri := dist_triangle (sweepChord' r D σ lam) 0 (sweepArc' r D σ lam)
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, sub_zero, zero_sub, norm_neg] at htri
        linarith
      have h := sweepLoopProfile_diff_le (D := D) (σ := σ) (α := ε / 8) (β := 2 * B)
        (by linarith) (by linarith) hl0 hl4 ha hb hab harc hb2 hb2' hchord
      have hmin : min 1 (2 * (b - a) / lam) * (2 * B) ≤ ε / 4 := by
        have h1 : min 1 (2 * (b - a) / lam) ≤ 2 * (b - a) / lam := min_le_right _ _
        have h2 : 2 * (b - a) / lam ≤ 2 * θ / lam₀ := by
          have h2a : 2 * (b - a) / lam ≤ 2 * θ / lam :=
            div_le_div_of_nonneg_right (by linarith) hl0.le
          have h2b : 2 * θ / lam ≤ 2 * θ / lam₀ :=
            div_le_div_of_nonneg_left (by linarith) hlam₀pos hbig
          linarith
        have h3 : 2 * θ / lam₀ * (2 * B) ≤ ε / 4 := by
          have h5 : 2 * θ / lam₀ * (2 * B) = 4 * B * θ / lam₀ := by ring
          rw [h5]
          have h6 : 4 * B * θ / lam₀ ≤ 4 * B * (ε * lam₀ / (16 * B)) / lam₀ := by
            gcongr
          have h7 : 4 * B * (ε * lam₀ / (16 * B)) / lam₀ = ε / 4 := by
            have h8 : 4 * B * (ε * lam₀ / (16 * B)) = ε * lam₀ / 4 := by
              rw [mul_div_right_const 4 (b := B) (a := ε * lam₀) (ne_of_gt hBpos)]
              ring
            rw [h8, div_div, mul_div_mul_right ε 4 (ne_of_gt hlam₀pos)]
          linarith [h6, h7.le, h7.ge]
        calc min 1 (2 * (b - a) / lam) * (2 * B) ≤ 2 * θ / lam₀ * (2 * B) :=
              mul_le_mul_of_nonneg_right (le_trans h1 h2) (by linarith)
          _ ≤ ε / 4 := h3
      linarith
  rcases le_total w w' with h | h
  · have hd : w' - w ≤ θ := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)] at hww'
      exact hww'
    exact main w w' hw hw' h hd
  · have hd : w - w' ≤ θ := by
      rw [abs_of_nonneg (sub_nonneg.mpr h)] at hww'
      exact hww'
    rw [norm_sub_rev]
    exact main w' w hw' hw h hd

end Work.Drive
