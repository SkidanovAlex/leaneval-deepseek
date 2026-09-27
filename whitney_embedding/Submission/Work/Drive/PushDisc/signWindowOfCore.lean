import Mathlib
import Submission.Work.Drive.PushDisc.coreHeightNegNear
import Submission.Work.Drive.PushDisc.heightAmplitudesNear

/-!
# The sign window of the core's height (the `hwneg`/`hwsmall` rows of the amplitude)

`Work.Drive.PushDisc.heightAmplitudesNear` (the amplitude construction of `AsymChartData`) consumes
two rows about the core's height `w x = (h (x,0)).1`:

* `hwneg` : `w x < 0` for `1 < |x| < X'` (the core is strictly below the first sheet just outside
  the two double points), and
* `hwsmall` : `|w x| < η` on the same annulus (so that the amplitude's shift can be taken as small
  as the isolation radius of the Whitney-disc argument).

Both follow from the *sign of the core's derivative* at the two double points:
`w (-1) = w 1 = 0`, `HasDerivAt w a (-1)`, `HasDerivAt w b 1` with `a > 0 > b`
(`Work.Drive.PushDisc.coreHeightNegNear` gives `hwneg` directly; `hwsmall` then follows by
shrinking the annulus, using continuity of `w` at `±1` and `w (±1) = 0`).

The hypothesis `a * b < 0` alone (opposite slopes) does not fix *which* sign appears on the annulus;
the opposite orientation is obtained by flipping the model's `y`-coordinate (which fixes the plane
`{y = 0, v = 0}` and both pinned points), and then the sign pattern reverts to
`a > 0 > b`.  The brick therefore comes in the two orientations:
`exists_window_neg_of_slopes` (`a > 0 > b`) and `exists_window_pos_of_slopes` (`a < 0 < b`,
proved by applying the first to `-w`).
-/

namespace Work.Drive.PushDisc

open Filter Set
open scoped Topology

/-- **The sign window of the core's height** (the orientation with `a > 0 > b`).

If `w` vanishes at `±1` with `HasDerivAt w a (-1)`, `HasDerivAt w b 1` and `0 < a`, `b < 0`, then for
every `η > 0` there is a window `1 < X < X'` with `w < 0` and `|w| < η` on the annulus
`1 < |x| < X'`. -/
theorem exists_window_neg_of_slopes {w : ℝ → ℝ} (hw : Continuous w)
    (hm : w (-1) = 0) (h1 : w 1 = 0)
    {a b : ℝ} (ha : HasDerivAt w a (-1)) (hb : HasDerivAt w b 1)
    (ha' : 0 < a) (hb' : b < 0) :
    ∀ η : ℝ, 0 < η → ∃ X X' : ℝ, 1 < X ∧ X < X' ∧
      (∀ x : ℝ, 1 < |x| → |x| < X' → w x < 0) ∧
      (∀ x : ℝ, 1 < |x| → |x| < X' → |w x| < η) := by
  intro η hη
  obtain ⟨δ, hδpos, hδ⟩ := coreHeightNegNear w a b hm ha ha' h1 hb hb'
  -- continuity at `1` and at `-1`, in the form `|w| < η` near each point
  have hcont1 : ∀ᶠ x in 𝓝 (1 : ℝ), |w x| < η := by
    have h := (hw.continuousAt (x := (1 : ℝ))).tendsto
    have h2 : w 1 ∈ Set.Ioo (-η) η := by rw [h1]; exact ⟨by linarith, hη⟩
    have := h (isOpen_Ioo.mem_nhds h2)
    filter_upwards [this] with x hx
    rwa [abs_lt]
  have hcontm : ∀ᶠ x in 𝓝 (-1 : ℝ), |w x| < η := by
    have h := (hw.continuousAt (x := (-1 : ℝ))).tendsto
    have h2 : w (-1) ∈ Set.Ioo (-η) η := by rw [hm]; exact ⟨by linarith, hη⟩
    have := h (isOpen_Ioo.mem_nhds h2)
    filter_upwards [this] with x hx
    rwa [abs_lt]
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.eventually_nhds_iff.mp hcont1
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := Metric.eventually_nhds_iff.mp hcontm
  set ε : ℝ := min δ (min ε₁ ε₂) with hεdef
  have hεpos : 0 < ε := lt_min hδpos (lt_min hε₁pos hε₂pos)
  refine ⟨1 + ε / 4, 1 + ε / 2, by linarith, by linarith, ?_, ?_⟩
  · intro x hx1 hx2
    have hεδ : ε ≤ δ := min_le_left _ _
    exact hδ x hx1 (by linarith)
  · intro x hx1 hx2
    have hεδ : ε ≤ δ := min_le_left _ _
    have hx2' := abs_lt.mp hx2
    have hε₁le : ε ≤ ε₁ := le_trans (min_le_right _ _) (min_le_left _ _)
    have hε₂le : ε ≤ ε₂ := le_trans (min_le_right _ _) (min_le_right _ _)
    rcases lt_abs.mp hx1 with hx1 | hx1
    · -- `x > 1`: close to `1`
      have hd : dist x 1 < ε₁ := by
        rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < x - 1)]
        linarith
      exact hε₁ hd
    · -- `x < -1`: close to `-1`
      have hd : dist x (-1) < ε₂ := by
        rw [Real.dist_eq]
        have h3 : x + 1 < 0 := by linarith
        rw [show x - -1 = x + 1 by ring, abs_of_neg h3]
        linarith
      exact hε₂ hd

/-- **The sign window of the core's height**, opposite orientation (`a < 0 < b`): `w > 0` on the
annulus.  Obtained from `exists_window_neg_of_slopes` applied to `-w`. -/
theorem exists_window_pos_of_slopes {w : ℝ → ℝ} (hw : Continuous w)
    (hm : w (-1) = 0) (h1 : w 1 = 0)
    {a b : ℝ} (ha : HasDerivAt w a (-1)) (hb : HasDerivAt w b 1)
    (ha' : a < 0) (hb' : 0 < b) :
    ∀ η : ℝ, 0 < η → ∃ X X' : ℝ, 1 < X ∧ X < X' ∧
      (∀ x : ℝ, 1 < |x| → |x| < X' → 0 < w x) ∧
      (∀ x : ℝ, 1 < |x| → |x| < X' → |w x| < η) := by
  have hw' : Continuous (fun x : ℝ => -w x) := hw.neg
  have hm' : (fun x : ℝ => -w x) (-1) = 0 := by show -w (-1) = 0; rw [hm]; ring
  have h1' : (fun x : ℝ => -w x) 1 = 0 := by show -w 1 = 0; rw [h1]; ring
  have ha'' : HasDerivAt (fun x : ℝ => -w x) (-a) (-1) := ha.neg
  have hb'' : HasDerivAt (fun x : ℝ => -w x) (-b) 1 := hb.neg
  intro η hη
  obtain ⟨X, X', h1X, hXX', hneg, hsmall⟩ :=
    exists_window_neg_of_slopes hw' hm' h1' ha'' hb'' (by linarith) (by linarith) η hη
  refine ⟨X, X', h1X, hXX', ?_, ?_⟩
  · intro x hx1 hx2
    have := hneg x hx1 hx2
    linarith
  · intro x hx1 hx2
    have := hsmall x hx1 hx2
    rwa [abs_neg] at this

/-- **The amplitude rows of `AsymChartData` from the sign data of the core.**  If the core's height
`w` vanishes at `±1` and has opposite slopes `a > 0 > b` there, then there is a full set of
amplitudes `X < X'`, `m`, `l` with

* `m, l ≥ 0`, `m` supported in `|x| ≤ X`, `l` supported in `t ≤ 1/2`, `l 0 ≠ 0`, both `C^∞`, and
* **`havoid`**: `w x ≠ 2 m x l 0` for every `|x| < X'`.

This is `Work.Drive.PushDisc.heightAmplitudesNear` fed with the two rows `hwneg`/`hwsmall` produced by
`exists_window_neg_of_slopes`; the orientation `a > 0 > b` is the one in which the shear (with
`m ≥ 0`) can avoid the core (the opposite orientation is obtained by flipping the model's
`y`-coordinate, which fixes the plane `{y = 0, v = 0}` and both pinned points). -/
theorem exists_amplitudes_of_core {w : ℝ → ℝ} (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hm : w (-1) = 0) (h1 : w 1 = 0)
    {a b : ℝ} (ha : HasDerivAt w a (-1)) (hb : HasDerivAt w b 1)
    (ha' : 0 < a) (hb' : b < 0) :
    ∃ (X X' : ℝ) (m l : ℝ → ℝ), 1 < X ∧ X < X' ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) l ∧
      (∀ x : ℝ, 0 ≤ m x) ∧ (∀ t : ℝ, 0 ≤ l t) ∧
      (∀ x : ℝ, X ≤ |x| → m x = 0) ∧ (∀ t : ℝ, 1 / 2 ≤ t → l t = 0) ∧ l 0 ≠ 0 ∧
      (∀ x : ℝ, |x| < X' → w x ≠ 2 * m x * l 0) := by
  obtain ⟨X, X', h1X, hXX', hneg, hsmall⟩ :=
    exists_window_neg_of_slopes hw.continuous hm h1 ha hb ha' hb' 1 (by norm_num)
  obtain ⟨m, l, hmsm, hlsm, hmnn, hlnn, hmzero, hlzero, hl0, havoid, _⟩ :=
    heightAmplitudesNear (w := w) hw (X := X) (X' := X') (η := 1) h1X hXX' (by norm_num) hneg hsmall
  exact ⟨X, X', m, l, h1X, hXX', hmsm, hlsm, hmnn, hlnn, hmzero, hlzero,
    by rw [hl0]; norm_num, havoid⟩

end Work.Drive.PushDisc
