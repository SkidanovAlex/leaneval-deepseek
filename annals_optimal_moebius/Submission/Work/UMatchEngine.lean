import Submission.Work.LeafContinuity
import Submission.Work.FrontierSeparation

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# U-matching engine (T1-iii glue, step 2 — analysis part)

The leaf endpoints are the boundary intersections of the leaf line:
`uBendA = leftPointOfDir x (uBendDirPos x)` (rfl).  For the U-side limit
at a frontier height we need these intersection maps to be continuous in
(base point, direction) — with non-vertical direction — plus the algebra
that a chord of data `(α,β)` (through its centre height) has seam
endpoints `(0,α)`, `(1,β)`:

* `leftPointOfDir_coord1` / `rightPointOfDir_coord1` — explicit second
  coordinates (valid for all directions);
* `continuousAt_leftPointOfDir_pair` / `continuousAt_rightPointOfDir_pair`
  — joint continuity of `(x,d) ↦ left/rightPointOfDir x d` at
  `d₀ 0 ≠ 0` (division by the continuous non-zero `d 0`);
* `tendsto_leftPointOfDir` / `tendsto_rightPointOfDir` — the sequence
  corollaries (direction and base point converging);
* `leftPointOfDir_chord_left` / `rightPointOfDir_chord_right` — for chord
  data `(α,β)` with centre height `sideH₁ α β (1/2)`, the leaf line in
  the chord direction `(1, β−α)` through the centre point meets the left
  seam at `(0, α)` and the right seam at `(1, β)`.

So once the DIRECTION of the approaching `U`-leaves converges to the
direction of the frontier chord, the leaf endpoints converge to the
frontier chord's seam endpoints (the remaining geometric input is the
direction convergence itself).

Build: `lake build Submission.Work.UMatchEngine` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- Second coordinate of the left-boundary intersection:
`(leftPointOfDir x d) 1 = x 1 − x0·d1/d0`. -/
lemma leftPointOfDir_coord1 (x d : ℝ²) :
    (leftPointOfDir x d) 1 = x 1 - (x 0) * (d 1) / (d 0) := by
  unfold leftPointOfDir leftParam
  simp [smul_eq_mul]
  ring_nf

/-- Second coordinate of the right-boundary intersection:
`(rightPointOfDir x d) 1 = x 1 + (1−x0)·d1/d0`. -/
lemma rightPointOfDir_coord1 (x d : ℝ²) :
    (rightPointOfDir x d) 1 = x 1 + (1 - x 0) * (d 1) / (d 0) := by
  unfold rightPointOfDir rightParam
  simp [smul_eq_mul]
  ring_nf

/-- Vector form of the left-boundary intersection at non-vertical
directions: `leftPointOfDir x d = (0, x1 − x0·d1/d0)`. -/
lemma leftPointOfDir_eval (x d : ℝ²) (hd0 : d 0 ≠ 0) :
    leftPointOfDir x d = !₂[(0 : ℝ), x 1 - (x 0) * (d 1) / (d 0)] := by
  ext i <;> fin_cases i
  · simpa using (leftPointOfDir_coord0 (x := x) (d := d) hd0)
  · simpa using (leftPointOfDir_coord1 x d)

/-- Vector form of the right-boundary intersection at non-vertical
directions: `rightPointOfDir x d = (1, x1 + (1−x0)·d1/d0)`. -/
lemma rightPointOfDir_eval (x d : ℝ²) (hd0 : d 0 ≠ 0) :
    rightPointOfDir x d = !₂[(1 : ℝ), x 1 + (1 - x 0) * (d 1) / (d 0)] := by
  ext i <;> fin_cases i
  · simpa using (rightPointOfDir_coord0 (x := x) (d := d) hd0)
  · simpa using (rightPointOfDir_coord1 x d)

/-- **Joint continuity of the left-boundary intersection** in
(base point, direction), at non-vertical directions. -/
theorem continuousAt_leftPointOfDir_pair {x₀ d₀ : ℝ²} (hd0 : d₀ 0 ≠ 0) :
    ContinuousAt (fun p : ℝ² × ℝ² => leftPointOfDir p.1 p.2) (x₀, d₀) := by
  unfold leftPointOfDir leftParam
  have hid : ContinuousAt (fun p : ℝ² × ℝ² => p.1) (x₀, d₀) := by
    simpa using (continuousAt_fst : ContinuousAt (fun p : ℝ² × ℝ² => p.1) (x₀, d₀))
  have hcnum : ContinuousAt (fun p : ℝ² × ℝ² => -(p.1 0)) (x₀, d₀) := by fun_prop
  have hcden : ContinuousAt (fun p : ℝ² × ℝ² => (p.2 0)) (x₀, d₀) := by fun_prop
  have hden0 : (fun p : ℝ² × ℝ² => (p.2 0)) (x₀, d₀) ≠ 0 := by simpa using hd0
  have hcdiv : ContinuousAt (fun p : ℝ² × ℝ² => -(p.1 0) / (p.2 0)) (x₀, d₀) :=
    ContinuousAt.div hcnum hcden hden0
  have hc2 : ContinuousAt (fun p : ℝ² × ℝ² => p.2) (x₀, d₀) := by
    simpa using (continuousAt_snd : ContinuousAt (fun p : ℝ² × ℝ² => p.2) (x₀, d₀))
  have hcsmul : ContinuousAt (fun p : ℝ² × ℝ² => (-(p.1 0) / (p.2 0)) • p.2) (x₀, d₀) :=
    ContinuousAt.smul hcdiv hc2
  exact ContinuousAt.add hid hcsmul

/-- **Joint continuity of the right-boundary intersection** in
(base point, direction), at non-vertical directions. -/
theorem continuousAt_rightPointOfDir_pair {x₀ d₀ : ℝ²} (hd0 : d₀ 0 ≠ 0) :
    ContinuousAt (fun p : ℝ² × ℝ² => rightPointOfDir p.1 p.2) (x₀, d₀) := by
  unfold rightPointOfDir rightParam
  have hid : ContinuousAt (fun p : ℝ² × ℝ² => p.1) (x₀, d₀) := by
    simpa using (continuousAt_fst : ContinuousAt (fun p : ℝ² × ℝ² => p.1) (x₀, d₀))
  have hcnum : ContinuousAt (fun p : ℝ² × ℝ² => 1 - p.1 0) (x₀, d₀) := by fun_prop
  have hcden : ContinuousAt (fun p : ℝ² × ℝ² => (p.2 0)) (x₀, d₀) := by fun_prop
  have hden0 : (fun p : ℝ² × ℝ² => (p.2 0)) (x₀, d₀) ≠ 0 := by simpa using hd0
  have hcdiv : ContinuousAt (fun p : ℝ² × ℝ² => (1 - p.1 0) / (p.2 0)) (x₀, d₀) :=
    ContinuousAt.div hcnum hcden hden0
  have hc2 : ContinuousAt (fun p : ℝ² × ℝ² => p.2) (x₀, d₀) := by
    simpa using (continuousAt_snd : ContinuousAt (fun p : ℝ² × ℝ² => p.2) (x₀, d₀))
  have hcsmul : ContinuousAt (fun p : ℝ² × ℝ² => ((1 - p.1 0) / (p.2 0)) • p.2) (x₀, d₀) :=
    ContinuousAt.smul hcdiv hc2
  exact ContinuousAt.add hid hcsmul

/-- **Sequence version**: left endpoints converge when base points and
directions do (non-vertical limit direction). -/
theorem tendsto_leftPointOfDir {u : ℕ → ℝ²} {v : ℕ → ℝ²} {x₀ d₀ : ℝ²}
    (hu : Tendsto u atTop (𝓝 x₀)) (hv : Tendsto v atTop (𝓝 d₀)) (hd0 : d₀ 0 ≠ 0) :
    Tendsto (fun n : ℕ => leftPointOfDir (u n) (v n)) atTop (𝓝 (leftPointOfDir x₀ d₀)) := by
  have hcont := continuousAt_leftPointOfDir_pair (x₀ := x₀) (d₀ := d₀) hd0
  have hpair : Tendsto (fun n : ℕ => (u n, v n)) atTop (𝓝 (x₀, d₀)) := hu.prodMk_nhds hv
  have h := hcont.tendsto.comp hpair
  change Tendsto (fun n : ℕ => (fun p : ℝ² × ℝ² => leftPointOfDir p.1 p.2) (u n, v n)) atTop
    (𝓝 (leftPointOfDir x₀ d₀))
  exact h

/-- **Sequence version**: right endpoints converge when base points and
directions do (non-vertical limit direction). -/
theorem tendsto_rightPointOfDir {u : ℕ → ℝ²} {v : ℕ → ℝ²} {x₀ d₀ : ℝ²}
    (hu : Tendsto u atTop (𝓝 x₀)) (hv : Tendsto v atTop (𝓝 d₀)) (hd0 : d₀ 0 ≠ 0) :
    Tendsto (fun n : ℕ => rightPointOfDir (u n) (v n)) atTop (𝓝 (rightPointOfDir x₀ d₀)) := by
  have hcont := continuousAt_rightPointOfDir_pair (x₀ := x₀) (d₀ := d₀) hd0
  have hpair : Tendsto (fun n : ℕ => (u n, v n)) atTop (𝓝 (x₀, d₀)) := hu.prodMk_nhds hv
  have h := hcont.tendsto.comp hpair
  change Tendsto (fun n : ℕ => (fun p : ℝ² × ℝ² => rightPointOfDir p.1 p.2) (u n, v n)) atTop
    (𝓝 (rightPointOfDir x₀ d₀))
  exact h

/-- **The leaf line in the chord direction through the chord's centre
point meets the left seam at the chord's left endpoint** `(0, α)`. -/
lemma leftPointOfDir_chord_left (α β : ℝ) :
    leftPointOfDir (centrePoint (sideH₁ α β (1 / 2))) (!₂[(1 : ℝ), β - α]) = !₂[(0 : ℝ), α] := by
  have hd0 : ((!₂[(1 : ℝ), β - α] : ℝ²)) 0 ≠ 0 := by
    have hc0 : ((!₂[(1 : ℝ), β - α] : ℝ²)) 0 = 1 := by rfl
    rw [hc0]
    norm_num
  rw [leftPointOfDir_eval (centrePoint (sideH₁ α β (1 / 2))) (!₂[(1 : ℝ), β - α]) hd0]
  congr 1
  have hc1 : (centrePoint (sideH₁ α β (1 / 2))) 1 = sideH₁ α β (1 / 2) := by rfl
  have hc0' : (centrePoint (sideH₁ α β (1 / 2))) 0 = (1 / 2 : ℝ) := by rfl
  have hd1 : ((!₂[(1 : ℝ), β - α] : ℝ²)) 1 = β - α := by rfl
  have hd0' : ((!₂[(1 : ℝ), β - α] : ℝ²)) 0 = 1 := by rfl
  rw [hc1, hc0', hd1, hd0']
  have hc : sideH₁ α β (1 / 2) = (α + β) / 2 := by dsimp [sideH₁]; ring
  rw [hc]
  ring

/-- **The leaf line in the chord direction through the chord's centre
point meets the right seam at the chord's right endpoint** `(1, β)`. -/
lemma rightPointOfDir_chord_right (α β : ℝ) :
    rightPointOfDir (centrePoint (sideH₁ α β (1 / 2))) (!₂[(1 : ℝ), β - α]) = !₂[(1 : ℝ), β] := by
  have hd0 : ((!₂[(1 : ℝ), β - α] : ℝ²)) 0 ≠ 0 := by
    have hc0 : ((!₂[(1 : ℝ), β - α] : ℝ²)) 0 = 1 := by rfl
    rw [hc0]
    norm_num
  rw [rightPointOfDir_eval (centrePoint (sideH₁ α β (1 / 2))) (!₂[(1 : ℝ), β - α]) hd0]
  congr 1
  have hc1 : (centrePoint (sideH₁ α β (1 / 2))) 1 = sideH₁ α β (1 / 2) := by rfl
  have hc0' : (centrePoint (sideH₁ α β (1 / 2))) 0 = (1 / 2 : ℝ) := by rfl
  have hd1 : ((!₂[(1 : ℝ), β - α] : ℝ²)) 1 = β - α := by rfl
  have hd0' : ((!₂[(1 : ℝ), β - α] : ℝ²)) 0 = 1 := by rfl
  rw [hc1, hc0', hd1, hd0']
  have hc : sideH₁ α β (1 / 2) = (α + β) / 2 := by dsimp [sideH₁]; ring
  rw [hc]
  ring

end Submission.PaperBand
