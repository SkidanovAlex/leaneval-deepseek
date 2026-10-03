import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.pert2v2.GatePreimageReBound.walk_fwd_re
import Submission.Work.Pert.pert2v2.GatePreimageReBound.walk_bwd_re

/-!
# `Work.Pert.pert2v2.walk_to_window`

**The unbounded-`Re` walk to the window `|Re| ≤ 2`.**  For `F` a near-translation by `1` on the
lower gate `Qm Ξ α` (with an Abel coordinate `Φ`, `Φ (F w) = Φ w + 1` on the gate) which is
*exponentially* close to `z ↦ z + 1` above a height `Ydec`, every gate point `z` of sufficiently
large height admits a gate point `z'` with

* `z'.re ∈ [-2, 2]` (the drift window),
* `z'.im ≥ z.im - 1` (the height is preserved up to one unit),
* `‖(Φ z' - z') - (Φ z - z)‖ ≤ 1` (the drift `Φ - id` is preserved).

This is the *union* of the two directional walks already on disk:

* `GatePreimageReBound.walk_fwd_re` for `z.re ≤ -1` (walk the `F`-orbit forward until `Re ∈ [0,1]`);
* `GatePreimageReBound.walk_bwd_re` for `1 ≤ z.re` (walk backwards, using the `F`-preimage step,
  until `Re ∈ [-1,0]`);
* the *middle* case `-1 < z.re < 1` is immediate: `z' := z` already lies in `[-2,2]`, and the
  drift comparison is `0 ≤ 1`.

The point of the lemma is exactly that no hypothesis on `z.re` remains: the gate point `z` is
arbitrary above the threshold. -/

namespace Work.Pert.pert2v2

open _root_.MandelDim Complex Set Metric

theorem walk_to_window {Ξ : ℝ} {α : ℂ} {F Φ : ℂ → ℂ} {M κ Ydec : ℝ}
    (hNT : MandelDim.NearTranslationOn F (Work.Pert.Qm Ξ α))
    (habel : ∀ w ∈ Work.Pert.Qm Ξ α, F w ∈ Work.Pert.Qm Ξ α → Φ (F w) = Φ w + 1)
    (hdec : ∀ w ∈ Work.Pert.Qm Ξ α, Ydec < w.im →
      ‖F w - (w + 1)‖ ≤ M * Real.exp (-(κ * w.im)))
    (hM : 0 < M) (hκ : 0 < κ) :
    ∃ K : ℝ, ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α → K ≤ z.im →
      ∃ z' : ℂ, z' ∈ Work.Pert.Qm Ξ α ∧ z'.re ∈ Set.Icc (-2 : ℝ) 2 ∧
        z.im - 1 ≤ z'.im ∧ ‖(Φ z' - z') - (Φ z - z)‖ ≤ 1 := by
  -- the two directional walks of `GatePreimageReBound`
  obtain ⟨Kf, hKf⟩ :=
    GatePreimageReBound.walk_fwd_re (Ξ := Ξ) (α := α) (F := F) (Φ := Φ) hNT habel hdec hM hκ
  obtain ⟨Kb, hKb⟩ :=
    GatePreimageReBound.walk_bwd_re (Ξ := Ξ) (α := α) (F := F) (Φ := Φ) hNT habel hdec hM hκ
  refine ⟨max Kf Kb, fun z hzQ hzim => ?_⟩
  have hKfz : Kf ≤ z.im := le_trans (le_max_left _ _) hzim
  have hKbz : Kb ≤ z.im := le_trans (le_max_right _ _) hzim
  by_cases hleft : z.re ≤ -1
  · -- walk forward
    obtain ⟨z', h1, _N, _hN, h2, h3, h4⟩ := hKf z hzQ hleft hKfz
    exact ⟨z', h1, h2, h3, h4⟩
  · by_cases hright : 1 ≤ z.re
    · -- walk backward
      obtain ⟨z', h1, _N, _hN, h2, h3, h4⟩ := hKb z hzQ hright hKbz
      exact ⟨z', h1, h2, h3, h4⟩
    · -- the middle case: `z` itself is already in the window
      push Not at hleft hright
      exact ⟨z, hzQ, ⟨by linarith, by linarith⟩, by linarith, by simp⟩

end Work.Pert.pert2v2
