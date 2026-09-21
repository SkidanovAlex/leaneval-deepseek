import Mathlib
import Submission.Work.OddVolterra.Free.FreeSetup
import Submission.Work.OddVolterra.Free.envelopeLeft_gap_dev_orders_two

/-!
# Absolute bounds on the jets of the anchor's bump

The bump `h` of the odd construction is supported in the open window
`(1 - 2τ, 1 - τ) = (4/5, 9/10)` and is only ever assumed to be smooth there — no size class is
available in the statement.  Nevertheless its first two jets are *absolutely* bounded on
`[7/10, 1]`, with a constant independent of `(h, X, Y)`, because the four *coupling* fields of
`Work.OddEnvelope.IsEnvelopeCurve` tie the bump to the chord curve `(X, Y)`:

* `mono_y`, `mono_x` : `0 < Y s + s Y' s + h' s` and `0 < X s + s X' s - h' s` — these give
  `h' s` between `-(Y s + s Y' s)` and `X s + s X' s`;
* `shape_y`, `shape_x` : the two second-order concavity conditions, which are linear in
  `h'' s` with coefficients `∓ Y' s`, `∓ X' s` of a definite sign
  (`x_deriv_neg`, `y_deriv_neg`), and therefore give two-sided bounds on `h'' s`.

The chord curve is `C²`-close to the semicircle chord function `profileX` (`CloseToProfileX`) and
`X' , Y'` are bounded below by `|profileX'| - 1/100 ≥ 3/20` on `[7/10, 1]`, so all the right-hand
sides are bounded by explicit absolute constants.  The value `|h σ|` then follows from the
support hypothesis together with the mean value inequality on `[4/5, 9/10]`.

The resulting constant is `41` (`|h σ| ≤ 3/10`, `|h' σ| ≤ 3`, `|h'' σ| ≤ 41`).
-/

namespace Work.OddVolterra.Free

open Set Filter
open scoped Topology

noncomputable section

namespace AnchorBumpAux

/-! ## Numerical facts about the semicircle chord function -/

/-- `|profileX''| ≤ 1` on `(0, 1]` (the workspace's `profileX_deriv2_abs_le_one` only covers
`[3/4, 9/10]`). -/
lemma profileX_deriv2_abs_le_one_of_le_one {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    |deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 := by
  rw [(Work.OddEnvelope.Close.profileX_deriv_formulas s).2.1, abs_mul]
  have h1 : Work.OddEnvelope.profileX s ≤ 1 := le_of_lt (Work.OddEnvelope.profileX_lt_one hs)
  have h0 : 0 ≤ Work.OddEnvelope.profileX s := le_of_lt (Work.OddEnvelope.profileX_pos s)
  have h2 : |2 * s ^ 2 - 1| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
  have h3 : |Work.OddEnvelope.profileX s ^ 5| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_one₀ h0 h1
  calc |2 * s ^ 2 - 1| * |Work.OddEnvelope.profileX s ^ 5| ≤ 1 * 1 :=
        mul_le_mul h2 h3 (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- `|profileX'| ≥ 7/30` on `[7/10, 1]`. -/
lemma profileX_deriv_abs_ge_of_mem {s : ℝ} (hs : 7 / 10 ≤ s) (hs1 : s ≤ 1) :
    7 / 30 ≤ |deriv Work.OddEnvelope.profileX s| := by
  have hs0 : 0 < s := by linarith
  have hp0 : 0 < Work.OddEnvelope.profileX s := Work.OddEnvelope.profileX_pos s
  have hpsq : (1 : ℝ) / 2 ≤ Work.OddEnvelope.profileX s ^ 2 := by
    rw [Work.OddEnvelope.profileX_sq s, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + s ^ 2)]
    nlinarith
  have hpge : (7 : ℝ) / 10 ≤ Work.OddEnvelope.profileX s := by
    have h57 : ((7 : ℝ) / 10) ^ 2 ≤ Work.OddEnvelope.profileX s ^ 2 := by
      norm_num at hpsq ⊢; linarith
    have h := sq_le_sq.mp h57
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 7 / 10), abs_of_pos hp0] at h
  rw [(Work.OddEnvelope.Close.profileX_deriv_formulas s).1, abs_mul, abs_neg,
      abs_of_pos hs0, abs_of_pos (by positivity : (0 : ℝ) < Work.OddEnvelope.profileX s ^ 3)]
  have hp3 : (7 : ℝ) / 20 ≤ Work.OddEnvelope.profileX s ^ 3 := by
    have h := mul_le_mul hpge hpsq (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_of_lt hp0)
    calc (7 : ℝ) / 20 = (7 / 10) * (1 / 2) := by norm_num
      _ ≤ Work.OddEnvelope.profileX s * Work.OddEnvelope.profileX s ^ 2 := h
      _ = Work.OddEnvelope.profileX s ^ 3 := by ring
  nlinarith [hp3, hs, hs0]

/-! ## Absolute `C²`-bounds for the chord curve -/

/-- `|X|`, `|X'|`, `|X''| ≤ 101/100` on `(0, 1]` for a chord function `C²`-close to
`profileX`. -/
lemma curve_abs_bounds {X : ℝ → ℝ} (hcX : Work.OddCurve.LowSlope.CloseToProfileX X)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    |X s| ≤ 101 / 100 ∧ |deriv X s| ≤ 101 / 100 ∧ |deriv (deriv X) s| ≤ 101 / 100 := by
  obtain ⟨h0, h1, h2⟩ := hcX s hs
  have hp0 : |Work.OddEnvelope.profileX s| ≤ 1 := by
    rw [abs_of_pos (Work.OddEnvelope.profileX_pos s)]
    exact le_of_lt (Work.OddEnvelope.profileX_lt_one hs)
  have hp1 : |deriv Work.OddEnvelope.profileX s| ≤ 1 :=
    Work.OddVolterra.Free.LeftGapAux.profileX_deriv_abs_le_one hs
  have hp2 : |deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 :=
    profileX_deriv2_abs_le_one_of_le_one hs hs1
  refine ⟨?_, ?_, ?_⟩
  · linarith [abs_sub_abs_le_abs_sub (X s) (Work.OddEnvelope.profileX s), h0, hp0]
  · linarith [abs_sub_abs_le_abs_sub (deriv X s) (deriv Work.OddEnvelope.profileX s), h1, hp1]
  · linarith [abs_sub_abs_le_abs_sub (deriv (deriv X) s)
      (deriv (deriv Work.OddEnvelope.profileX) s), h2, hp2]

/-- `|X'| ≥ 3/20` on `[7/10, 1]`. -/
lemma curve_deriv_abs_lower {X : ℝ → ℝ} (hcX : Work.OddCurve.LowSlope.CloseToProfileX X)
    {s : ℝ} (hs : 7 / 10 ≤ s) (hs1 : s ≤ 1) : (3 : ℝ) / 20 ≤ |deriv X s| := by
  have hs0 : 0 < s := by linarith
  obtain ⟨-, h1, -⟩ := hcX s hs0
  have hp1 : 7 / 30 ≤ |deriv Work.OddEnvelope.profileX s| :=
    profileX_deriv_abs_ge_of_mem hs hs1
  have h := abs_sub_abs_le_abs_sub (deriv Work.OddEnvelope.profileX s) (deriv X s)
  rw [abs_sub_comm] at h
  linarith

/-- `|a + s * b| ≤ 101/50` for `|s| ≤ 1`, `|a|, |b| ≤ 101/100`. -/
lemma abs_add_mul_le {a b s : ℝ} (hs : |s| ≤ 1) (ha : |a| ≤ 101 / 100)
    (hb : |b| ≤ 101 / 100) : |a + s * b| ≤ 101 / 50 := by
  calc |a + s * b| ≤ |a| + |s * b| := abs_add_le _ _
    _ = |a| + |s| * |b| := by rw [abs_mul]
    _ ≤ 101 / 100 + 1 * (101 / 100) := by
          have hm := mul_le_mul hs hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
          linarith
    _ = 101 / 50 := by norm_num

/-! ## Two-sided bounds on the jets of the bump -/

/-- **The monotonicity conditions bound `h'` two-sidedly.**  For `0 < s ≤ 1`,
`|h' s| ≤ 101/50`: `mono_y` gives `h' s > -(Y s + s Y' s)` and `mono_x` gives
`h' s < X s + s X' s`, and both right-hand sides are `O(1)`. -/
lemma deriv_h_bounds {h X Y : ℝ → ℝ} (hE : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hcX : Work.OddCurve.LowSlope.CloseToProfileX X)
    (hcY : Work.OddCurve.LowSlope.CloseToProfileX Y)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    -(101 / 50) < deriv h s ∧ deriv h s < 101 / 50 := by
  obtain ⟨hX0, hX1, -⟩ := curve_abs_bounds hcX hs hs1
  obtain ⟨hY0, hY1, -⟩ := curve_abs_bounds hcY hs hs1
  have hsabs : |s| ≤ 1 := by rw [abs_of_pos hs]; exact hs1
  have hXb : |X s + s * deriv X s| ≤ 101 / 50 := abs_add_mul_le hsabs hX0 hX1
  have hYb : |Y s + s * deriv Y s| ≤ 101 / 50 := abs_add_mul_le hsabs hY0 hY1
  constructor
  · have hmono := hE.mono_y s hs
    have h2 : -(101 / 50) ≤ -(Y s + s * deriv Y s) := by
      linarith [le_abs_self (Y s + s * deriv Y s), hYb]
    linarith
  · have hmono := hE.mono_x s hs
    have h2 : X s + s * deriv X s ≤ 101 / 50 := by
      linarith [le_abs_self (X s + s * deriv X s), hXb]
    linarith

/-- `|h' s| ≤ 3` for `0 < s ≤ 1`. -/
lemma abs_deriv_h_le {h X Y : ℝ → ℝ} (hE : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hcX : Work.OddCurve.LowSlope.CloseToProfileX X)
    (hcY : Work.OddCurve.LowSlope.CloseToProfileX Y)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) : |deriv h s| ≤ 3 := by
  obtain ⟨h1, h2⟩ := deriv_h_bounds hE hcX hcY hs hs1
  rw [abs_le]; constructor <;> linarith

/-- **The shape conditions bound `h''` two-sidedly.**  For `7/10 ≤ s ≤ 1`, `|h'' s| ≤ 41`:
`shape_y` reads `0 < (2 (Y')² - Y Y'' - h' Y'') + h'' Y'` with `Y' < 0`, giving
`h'' (-Y') < 2 (Y')² - Y Y'' - h' Y'' ≤ 6`, and `shape_x` reads
`0 < (2 (X')² - X X'' + h' X'') - h'' X'` with `X' < 0`, giving
`h'' (-X') > -(2 (X')² - X X'' + h' X'') ≥ -6`.  Since `|X'|, |Y'| ≥ 3/20`, this gives
`-41 < h'' s < 41`. -/
lemma abs_deriv_deriv_h_le {h X Y : ℝ → ℝ} (hE : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hcX : Work.OddCurve.LowSlope.CloseToProfileX X)
    (hcY : Work.OddCurve.LowSlope.CloseToProfileX Y)
    {s : ℝ} (hs : 7 / 10 ≤ s) (hs1 : s ≤ 1) : |deriv (deriv h) s| ≤ 41 := by
  have hs0 : 0 < s := by linarith
  obtain ⟨hX0, hX1, hX2⟩ := curve_abs_bounds hcX hs0 hs1
  obtain ⟨hY0, hY1, hY2⟩ := curve_abs_bounds hcY hs0 hs1
  have hXl : (3 : ℝ) / 20 ≤ |deriv X s| := curve_deriv_abs_lower hcX hs hs1
  have hYl : (3 : ℝ) / 20 ≤ |deriv Y s| := curve_deriv_abs_lower hcY hs hs1
  obtain ⟨hh1, hh2⟩ := deriv_h_bounds hE hcX hcY hs0 hs1
  have hha : |deriv h s| ≤ 101 / 50 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hXneg : deriv X s < 0 := hE.x_deriv_neg s hs0
  have hYneg : deriv Y s < 0 := hE.y_deriv_neg s hs0
  have hgY : (3 : ℝ) / 20 ≤ -(deriv Y s) := by rw [← abs_of_neg hYneg]; exact hYl
  have hgX : (3 : ℝ) / 20 ≤ -(deriv X s) := by rw [← abs_of_neg hXneg]; exact hXl
  have hnum : 2 * (101 / 100) ^ 2 + (101 / 100) ^ 2 + 101 / 50 * (101 / 100) ≤ (6 : ℝ) := by
    norm_num
  have hYabs : |Y s * deriv (deriv Y) s| ≤ (101 / 100) * (101 / 100) := by
    rw [abs_mul]; exact mul_le_mul hY0 hY2 (abs_nonneg _) (by norm_num)
  have hXabs : |X s * deriv (deriv X) s| ≤ (101 / 100) * (101 / 100) := by
    rw [abs_mul]; exact mul_le_mul hX0 hX2 (abs_nonneg _) (by norm_num)
  have hhYabs : |deriv h s * deriv (deriv Y) s| ≤ (101 / 50) * (101 / 100) := by
    rw [abs_mul]; exact mul_le_mul hha hY2 (abs_nonneg _) (by norm_num)
  have hhXabs : |deriv h s * deriv (deriv X) s| ≤ (101 / 50) * (101 / 100) := by
    rw [abs_mul]; exact mul_le_mul hha hX2 (abs_nonneg _) (by norm_num)
  have hU : deriv (deriv h) s < 41 := by
    have hp1 : 2 * (deriv Y s) ^ 2 ≤ 2 * (101 / 100) ^ 2 := by
      have hp := pow_le_pow_left₀ (abs_nonneg (deriv Y s)) hY1 2
      rw [sq_abs] at hp
      linarith
    have hBY : 2 * (deriv Y s) ^ 2 - Y s * deriv (deriv Y) s - deriv h s * deriv (deriv Y) s
        ≤ 6 := by
      linarith [(abs_le.mp hYabs).1, (abs_le.mp hhYabs).1, hnum, hp1]
    have hstep1 : -(deriv (deriv h) s * deriv Y s) <
        2 * (deriv Y s) ^ 2 - Y s * deriv (deriv Y) s - deriv h s * deriv (deriv Y) s := by
      have := hE.shape_y s hs0
      linarith
    have h6 : -(deriv (deriv h) s * deriv Y s) < 6 := by linarith [hstep1, hBY]
    have h41 : (6 : ℝ) < 41 * (-(deriv Y s)) := by nlinarith [hgY]
    exact lt_of_mul_lt_mul_right
      (by linarith : deriv (deriv h) s * (-(deriv Y s)) < 41 * (-(deriv Y s)))
      (by linarith : (0 : ℝ) ≤ -(deriv Y s))
  have hL : -41 < deriv (deriv h) s := by
    have hp1 : 2 * (deriv X s) ^ 2 ≤ 2 * (101 / 100) ^ 2 := by
      have hp := pow_le_pow_left₀ (abs_nonneg (deriv X s)) hX1 2
      rw [sq_abs] at hp
      linarith
    have hDX : 2 * (deriv X s) ^ 2 - X s * deriv (deriv X) s + deriv h s * deriv (deriv X) s
        ≤ 6 := by
      linarith [(abs_le.mp hXabs).1, (abs_le.mp hhXabs).2, hnum, hp1]
    have hstep1 : deriv (deriv h) s * (-(deriv X s)) >
        -(2 * (deriv X s) ^ 2 - X s * deriv (deriv X) s + deriv h s * deriv (deriv X) s) := by
      have := hE.shape_x s hs0
      linarith
    have h6 : -6 < deriv (deriv h) s * (-(deriv X s)) := by linarith [hstep1, hDX]
    have h41 : (-41) * (-(deriv X s)) < -6 := by nlinarith [hgX]
    exact lt_of_mul_lt_mul_right
      (by linarith : (-41) * (-(deriv X s)) < deriv (deriv h) s * (-(deriv X s)))
      (by linarith : (0 : ℝ) ≤ -(deriv X s))
  rw [abs_le]; exact ⟨by linarith, by linarith⟩

/-- **The bump itself is bounded on `[7/10, 1]`.**  Its support lies in `(4/5, 9/10)`, it vanishes
at `4/5`, and `|h'| ≤ 3` on `[4/5, 9/10]`; the mean value inequality on `[4/5, 9/10]` gives
`|h σ| ≤ 3 * (9/10 - 4/5) = 3/10`. -/
lemma abs_h_le {h X Y : ℝ → ℝ} (hE : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hcX : Work.OddCurve.LowSlope.CloseToProfileX X)
    (hcY : Work.OddCurve.LowSlope.CloseToProfileX Y)
    (hsupp : Function.support h ⊆ Set.Ioo (4 / 5 : ℝ) (9 / 10)) {σ : ℝ} :
    |h σ| ≤ 3 / 10 := by
  by_cases h4 : σ ≤ 4 / 5
  · have hz : h σ = 0 := by
      by_contra hne
      have := hsupp (Function.mem_support.mpr hne)
      linarith [this.1]
    rw [hz]; norm_num
  · have h4' : (4 : ℝ) / 5 < σ := lt_of_not_ge h4
    by_cases h9 : σ < 9 / 10
    · have hzero : h (4 / 5) = 0 := by
        by_contra hne
        have := hsupp (Function.mem_support.mpr hne)
        have h1 := this.1
        norm_num at h1
      have hdiff : ∀ x ∈ Set.Icc (4 / 5 : ℝ) (9 / 10), DifferentiableAt ℝ h x := by
        intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        exact (hE.smooth_h.differentiableOn (by simp)).differentiableAt
          (IsOpen.mem_nhds isOpen_Ioi hx0)
      have hbound : ∀ x ∈ Set.Icc (4 / 5 : ℝ) (9 / 10), ‖deriv h x‖ ≤ 3 := by
        intro x hx
        rw [Real.norm_eq_abs]
        exact abs_deriv_h_le hE hcX hcY (by linarith [hx.1]) (by linarith [hx.2])
      have hmain := Convex.norm_image_sub_le_of_norm_deriv_le (f := h) hdiff hbound
        (convex_Icc _ _)
        (show (4 / 5 : ℝ) ∈ Set.Icc (4 / 5 : ℝ) (9 / 10) from ⟨le_rfl, by norm_num⟩)
        (show σ ∈ Set.Icc (4 / 5 : ℝ) (9 / 10) from ⟨le_of_lt h4', le_of_lt h9⟩)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, hzero, sub_zero,
        abs_of_pos (by linarith : (0 : ℝ) < σ - 4 / 5)] at hmain
      linarith
    · have h9' : (9 : ℝ) / 10 ≤ σ := le_of_not_gt h9
      have hz : h σ = 0 := by
        by_contra hne
        have := hsupp (Function.mem_support.mpr hne)
        linarith [this.2]
      rw [hz]; norm_num

end AnchorBumpAux

open AnchorBumpAux in
/-- **Absolute bounds on the bump's jets.**  There is an absolute constant `K` such that for every
envelope-curve datum `(h, X, Y)` whose chord curve is `C²`-close to the semicircle's and whose
bump is supported in the open transition window `(1 - 2τ, 1 - τ)`, the value, the first and the
second derivative of `h` are bounded by `K` on the whole interval `[7/10, 1]`. -/
theorem anchorBumpJetsAbs (n : ℕ) (hn : 1 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ {h X Y : ℝ → ℝ},
      Work.OddEnvelope.IsEnvelopeCurve h X Y →
      Work.OddCurve.LowSlope.CloseToProfileX X →
      Work.OddCurve.LowSlope.CloseToProfileX Y →
      Function.support h ⊆ Set.Ioo (1 - 2 * Work.OddEnvelope.tau) (1 - Work.OddEnvelope.tau) →
      ∀ σ : ℝ, 7 / 10 ≤ σ → σ ≤ 1 →
        |h σ| ≤ K ∧ |deriv h σ| ≤ K ∧ |deriv (deriv h) σ| ≤ K := by
  refine ⟨41, by norm_num, ?_⟩
  intro h X Y hE hcX hcY hsupp σ hσ1 hσ2
  have hsupp' : Function.support h ⊆ Set.Ioo (4 / 5 : ℝ) (9 / 10) := by
    intro t ht
    have hmem := hsupp ht
    rw [show Work.OddEnvelope.tau = (1 : ℝ) / 10 from rfl] at hmem
    simp only [Set.mem_Ioo] at hmem ⊢
    constructor
    · have := hmem.1; linarith
    · have := hmem.2; linarith
  have hh := abs_h_le hE hcX hcY hsupp' (σ := σ)
  have hd := abs_deriv_h_le hE hcX hcY (by linarith : (0 : ℝ) < σ) hσ2
  have hdd := abs_deriv_deriv_h_le hE hcX hcY hσ1 hσ2
  exact ⟨by linarith, by linarith, by linarith⟩

end

end Work.OddVolterra.Free
