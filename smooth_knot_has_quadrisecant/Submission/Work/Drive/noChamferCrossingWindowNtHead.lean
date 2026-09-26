import Mathlib
import Submission.Work.Drive.no_chamfer_crossing_window_nt
import Submission.Work.Drive.arcChamferMirror

/-!
# The head no-chamfer-crossing theorem (non-tangency at both ends)

This is the mirror of `Work.Drive.no_chamfer_crossing_window_nt`, covering the *head* chamfer
instead of the tail one.  The mirror is the reversal `x ↦ r (-x)` of the knot
(`Work.Drive.mirror_isSmoothKnot` at `c = 0`, `Work.Drive.mirror_velocity`): under it the head
chamfer of the chord `(ta s, tb s)` becomes the tail chamfer of the chord `(-tb s, -ta s)`, and the
non-tangency hypotheses at the two endpoints are interchanged.  The statement is arranged in the
form the profile-injectivity assembly consumes: the crossing point ranges over the *retained* arc
`[ta + lam*(tb-ta), tb - lam*(tb-ta)]`.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The reversal of a smooth knot is a smooth knot.** -/
lemma isSmoothKnot_neg {r : ℝ → Space} (hr : IsSmoothKnot r) :
    IsSmoothKnot (fun x : ℝ => r (-x)) := by
  simpa only [zero_sub] using mirror_isSmoothKnot hr 0

/-- **The velocity of the reversal.** -/
lemma velocity_negKnot {r : ℝ → Space} (hr : IsSmoothKnot r) (x : ℝ) :
    velocity (fun y : ℝ => r (-y)) x = -velocity r (-x) := by
  simpa only [zero_sub] using mirror_velocity hr.smooth 0 x

/-- **No head chamfer crossing on a compact window carrying a non-tangency margin.** -/
theorem no_chamfer_crossing_window_nt_head {r : ℝ → Space} (hr : IsSmoothKnot r)
    (ta tb : ℝ → ℝ) (hta : Continuous ta) (htb : Continuous tb)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hpos : ∀ s ∈ Set.Icc a b, 0 < tb s - ta s ∧ tb s - ta s < period)
    (hntA : ∀ s ∈ Set.Icc a b, ∀ m : ℝ, r (tb s) - r (ta s) ≠ m • velocity r (ta s))
    (hntB : ∀ s ∈ Set.Icc a b, ∀ m : ℝ, r (tb s) - r (ta s) ≠ m • velocity r (tb s)) :
    ∃ L : ℝ, 0 < L ∧ ∀ (lam x c : ℝ), 0 < lam → lam ≤ L → 0 < c → c < 1 →
      ∀ s ∈ Set.Icc a b,
        ta s + lam * (tb s - ta s) ≤ x → x ≤ tb s - lam * (tb s - ta s) →
        (1 - c) • r (tb s - lam * (tb s - ta s))
          + c • (lam • r (ta s) + (1 - lam) • r (tb s)) = r x →
        x = tb s - lam * (tb s - ta s) := by
  have hr' : IsSmoothKnot (fun y : ℝ => r (-y)) := isSmoothKnot_neg hr
  obtain ⟨L, hLpos, hL⟩ := no_chamfer_crossing_window_nt hr' (fun s => -tb s) (fun s => -ta s)
    htb.neg hta.neg ha hab hb
    (fun s hs => by
      obtain ⟨h1, h2⟩ := hpos s hs
      exact ⟨by linarith, by linarith⟩)
    (fun s hs m hcon => by
      refine hntB s hs m ?_
      have h1 : r (tb s) - r (ta s) = -(r (ta s) - r (tb s)) := by abel
      have h2 : -(r (ta s) - r (tb s)) = m • velocity r (tb s) := by
        have hcon' : r (ta s) - r (tb s) = m • (-velocity r (tb s)) := by
          simpa only [velocity_negKnot hr, neg_neg] using hcon
        rw [hcon', smul_neg, neg_neg]
      rw [h1]; exact h2)
    (fun s hs m hcon => by
      refine hntA s hs m ?_
      have h1 : r (tb s) - r (ta s) = -(r (ta s) - r (tb s)) := by abel
      have h2 : -(r (ta s) - r (tb s)) = m • velocity r (ta s) := by
        have hcon' : r (ta s) - r (tb s) = m • (-velocity r (ta s)) := by
          simpa only [velocity_negKnot hr, neg_neg] using hcon
        rw [hcon', smul_neg, neg_neg]
      rw [h1]; exact h2)
  refine ⟨L, hLpos, ?_⟩
  intro lam x c hlam hLle hc0 hc1 s hs hxlo hxhi hcross
  obtain ⟨hw1, hw2⟩ := hpos s hs
  have hltx : ta s ≤ x := by nlinarith [hxlo, hw1, hlam]
  have hc'0 : 0 < 1 - c := by linarith
  have hc'1 : 1 - c < 1 := by linarith
  have key := hL lam (-x) (1 - c) hlam hLle hc'0 hc'1 s hs
    (by linarith [hxhi])
    (by linarith [hltx])
    (by
      rw [show (1 - (1 - c)) = c by ring]
      have h3 : r (-(-tb s + lam * (-ta s - -tb s))) = r (tb s - lam * (tb s - ta s)) := by
        congr 1
        ring
      rw [h3]
      simp only [neg_neg]
      have h5 : (1 - lam) • r (tb s) + lam • r (ta s)
          = lam • r (ta s) + (1 - lam) • r (tb s) := by rw [add_comm]
      rw [h5, add_comm]
      exact hcross)
  have hkeyEq : (-tb s) + lam * ((-ta s) - (-tb s)) = -(tb s - lam * (tb s - ta s)) := by ring
  rw [hkeyEq] at key
  linarith

end Work.Drive
