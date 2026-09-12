import Submission.Work.BendArcFacts
import Submission.Work.UMatchDirection
import Submission.Work.FlatLeafBendData

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Flat/U frontier glue — closed-interval flat leaves (T1-iii, step 1)

For a flat component `C = flatComponent f p` with canonical heights
`h₁ < h₂`, the blend leaf family `y ↦ flatCompBend … y` (valid on all of
`ℝ`) restricts to the closed interval `[h₁,h₂]`; at the boundary heights
it is the frontier chord (`genA`/`genB` at parameter `t = 0/1`), and it
is a PRE-BEND on the whole closed interval:

* `continuous_blendBend_A`/`_B`, `flatCompBend_A_cont`/`_B_cont` — the
  leaf endpoints are continuous functions of the centre height (reuse
  `continuous_blendA1`/`continuous_blendB1`);
* `flatCompBend_fA_cont`/`_fB_cont` — so are their `f`-images (`f` is
  smooth on the closed unit strip, `ContinuousOn.comp_continuous`);
* **`flatCompBend_preBend_closed`** — `∀ y ∈ Icc h₁ h₂`, the leaf is a
  pre-bend: the difference function
  `H y := ‖f B y − f A y‖ − ‖B y − A y‖` is continuous, vanishes on the
  open interval (interior pre-bend, green), and every point of the closed
  interval lies in its closure (`closure_Ioo`), so `H = 0` there
  (`eq_zero_of_continuousAt_of_closure_zero`).

This supplies `BandFoliation.preBend` at the frontier heights (the
boundary chords of a flat component are pre-bends) — the flat-side half
of the T1-iii glue — and the frontier-chord VALUES at the boundary
heights (`blendBend_upper/lower_*`, `flatCompBend_upper/lower_*`: at
`y = h₂` the leaf is the upper frontier chord with endpoints
`(0, α₂)`, `(1, β₂)`, at `y = h₁` the lower frontier chord with
`(0, α₁)`, `(1, β₁)`), for the agreement-with-neighbours arguments.

Build: `lake build Submission.Work.FlatGlue` rc=0, zero sorry.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- A real-valued function that is continuous at `x`, zero on `S`, and
whose zero set is closed at `x` (i.e. `x ∈ closure S`) is zero at `x`. -/
lemma eq_zero_of_continuousAt_of_closure_zero {X : Type*} [PseudoMetricSpace X]
    {x : X} {S : Set X} (H : X → ℝ) (hcont : ContinuousAt H x)
    (hSx : x ∈ closure S) (hzero : ∀ y ∈ S, H y = 0) : H x = 0 := by
  by_contra hne
  have habs : 0 < |H x| := abs_pos.mpr hne
  have hc := Metric.continuousAt_iff.mp hcont (|H x| / 2) (by linarith)
  rcases hc with ⟨δ, hδ0, hδ⟩
  have hmem := Metric.mem_closure_iff.mp hSx (δ / 2) (by linarith)
  rcases hmem with ⟨y, hyS, hyd⟩
  have hδy : |H y - H x| < |H x| / 2 := by
    have hd : dist (H y) (H x) < |H x| / 2 := hδ (x := y) (by
      have hyd' : dist y x < δ := by
        have : dist y x < δ / 2 := by simpa [dist_comm] using hyd
        linarith
      exact hyd')
    simpa [Real.dist_eq] using hd
  have hy0 : H y = 0 := hzero y hyS
  have : |H x| < |H x| / 2 := by
    calc
      |H x| = |H x - H y| := by rw [hy0]; ring_nf
      _ = |H y - H x| := by rw [abs_sub_comm]
      _ < |H x| / 2 := hδy
  linarith

/-- The left endpoint of the blend is a continuous function of the centre
height (it runs along the left boundary line). -/
lemma continuous_blendBend_A (α₁ β₁ α₂ β₂ : ℝ) :
    Continuous (fun y : ℝ => (blendBend α₁ β₁ α₂ β₂ y).A) := by
  have h : (fun y : ℝ => (blendBend α₁ β₁ α₂ β₂ y).A) =
      fun y : ℝ => ((genA α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 1) • (!₂[(0 : ℝ), 1] : ℝ²) := by
    funext y
    rw [blendBend_A_eq]
    have h0 : (genA α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 0 = 0 := by
      dsimp [genA]
      exact genP_coord0 α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y) 0
    calc
      genA α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)
          = !₂[0, (genA α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 1] := Submission.PaperBand.leftEdge_eq_vec h0
      _ = ((genA α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 1) • (!₂[(0 : ℝ), 1] : ℝ²) := by
            ext i <;> fin_cases i <;> simp [smul_eq_mul]
  rw [h]
  exact Continuous.smul (continuous_blendA1 (α₁ := α₁) (β₁ := β₁) (α₂ := α₂) (β₂ := β₂))
    continuous_const

/-- The right endpoint of the blend is a continuous function of the
centre height (it runs along the right boundary line). -/
lemma continuous_blendBend_B (α₁ β₁ α₂ β₂ : ℝ) :
    Continuous (fun y : ℝ => (blendBend α₁ β₁ α₂ β₂ y).B) := by
  have h : (fun y : ℝ => (blendBend α₁ β₁ α₂ β₂ y).B) =
      fun y : ℝ => (!₂[(1 : ℝ), 0] : ℝ²) +
        ((genB α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 1) • (!₂[(0 : ℝ), 1] : ℝ²) := by
    funext y
    rw [blendBend_B_eq]
    have h1 : (genB α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 0 = 1 := by
      dsimp [genB]
      exact genP_coord0 α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y) 1
    calc
      genB α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)
          = !₂[1, (genB α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 1] := Submission.PaperBand.rightEdge_eq_vec h1
      _ = (!₂[(1 : ℝ), 0] : ℝ²) + ((genB α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 1) • (!₂[(0 : ℝ), 1] : ℝ²) := by
            ext i <;> fin_cases i <;> simp [smul_eq_mul]
  rw [h]
  exact continuous_const.add (Continuous.smul
    (continuous_blendB1 (α₁ := α₁) (β₁ := β₁) (α₂ := α₂) (β₂ := β₂)) continuous_const)

/-- The blend endpoints stay in the closed unit strip (they are on the
seams). -/
lemma blendBend_A_mem_unitStrip (α₁ β₁ α₂ β₂ y : ℝ) :
    (blendBend α₁ β₁ α₂ β₂ y).A ∈ unitStrip := by
  rw [blendBend_A_eq]
  exact genA_mem_unitStrip α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)

/-- The blend endpoints stay in the closed unit strip (they are on the
seams). -/
lemma blendBend_B_mem_unitStrip (α₁ β₁ α₂ β₂ y : ℝ) :
    (blendBend α₁ β₁ α₂ β₂ y).B ∈ unitStrip := by
  rw [blendBend_B_eq]
  exact genB_mem_unitStrip α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)

/-- The left endpoint of the component leaf is continuous in the centre
height. -/
lemma flatCompBend_A_cont {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) :
    Continuous (fun y : ℝ => (flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).A) := by
  unfold flatCompBend
  exact continuous_blendBend_A (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
    (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2

/-- The right endpoint of the component leaf is continuous in the centre
height. -/
lemma flatCompBend_B_cont {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) :
    Continuous (fun y : ℝ => (flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).B) := by
  unfold flatCompBend
  exact continuous_blendBend_B (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
    (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2

/-- The component-leaf endpoints stay in the closed unit strip. -/
lemma flatCompBend_A_mem_unitStrip {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ y : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) :
    (flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).A ∈ unitStrip := by
  unfold flatCompBend
  exact blendBend_A_mem_unitStrip (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
    (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 y

/-- The component-leaf endpoints stay in the closed unit strip. -/
lemma flatCompBend_B_mem_unitStrip {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ y : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) :
    (flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).B ∈ unitStrip := by
  unfold flatCompBend
  exact blendBend_B_mem_unitStrip (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
    (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 y

/-- The image of the component-leaf left endpoint is continuous in the
centre height. -/
lemma flatCompBend_fA_cont {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) :
    Continuous (fun y : ℝ => f ((flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).A)) := by
  exact ContinuousOn.comp_continuous (hf.smooth.continuousOn)
    (flatCompBend_A_cont hf ha p hp hh₁ hh₂) (fun y => flatCompBend_A_mem_unitStrip hf ha p hp hh₁ hh₂)

/-- The image of the component-leaf right endpoint is continuous in the
centre height. -/
lemma flatCompBend_fB_cont {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) :
    Continuous (fun y : ℝ => f ((flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).B)) := by
  exact ContinuousOn.comp_continuous (hf.smooth.continuousOn)
    (flatCompBend_B_cont hf ha p hp hh₁ hh₂) (fun y => flatCompBend_B_mem_unitStrip hf ha p hp hh₁ hh₂)

/-- **The component leaves are pre-bends on the whole closed centre
interval** `[h₁,h₂]` — in particular the two frontier chords (at the
boundary heights) are pre-bends. -/
theorem flatCompBend_preBend_closed {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2) :
    ∀ y ∈ Set.Icc h₁ h₂,
      ‖f ((flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).B) -
          f ((flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).A)‖ =
      ‖(flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).B -
          (flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).A‖ := by
  intro y hy
  have hcont : Continuous (fun w : ℝ =>
      ‖f ((flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).B) -
          f ((flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).A)‖ -
      ‖(flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).B -
          (flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).A‖) := by
    have h1 : Continuous (fun w : ℝ =>
        f ((flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).B) -
          f ((flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).A)) :=
      (flatCompBend_fB_cont hf ha p hp hh₁ hh₂).sub (flatCompBend_fA_cont hf ha p hp hh₁ hh₂)
    have hn1 : Continuous (fun w : ℝ =>
        ‖f ((flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).B) -
          f ((flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).A)‖) := h1.norm
    have h2 : Continuous (fun w : ℝ =>
        (flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).B -
          (flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).A) :=
      (flatCompBend_B_cont hf ha p hp hh₁ hh₂).sub (flatCompBend_A_cont hf ha p hp hh₁ hh₂)
    have hn2 : Continuous (fun w : ℝ =>
        ‖(flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).B -
          (flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).A‖) := h2.norm
    exact hn1.sub hn2
  have hzero : ∀ w ∈ Set.Ioo h₁ h₂,
      (‖f ((flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).B) -
          f ((flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).A)‖ -
        ‖(flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).B -
          (flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).A‖) = 0 := by
    intro w hw
    have hpb := flatCompBend_preBend hf ha p hp hh₁ hh₂ hlt hC hw
    linarith
  have hcl : y ∈ closure (Set.Ioo h₁ h₂) := by
    rw [closure_Ioo (ne_of_lt hlt)]
    exact hy
  have hH := eq_zero_of_continuousAt_of_closure_zero (X := ℝ) (x := y) (S := Set.Ioo h₁ h₂)
    (H := fun w : ℝ => ‖f ((flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).B) -
          f ((flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).A)‖ -
        ‖(flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).B -
          (flatCompBend hf ha p hp h₁ h₂ w hh₁ hh₂).A‖)
    hcont.continuousAt hcl hzero
  linarith


/-- The blend inverse parameter at the UPPER boundary height
(`y = sideH₂(1/2)`) is 1. -/
lemma blendT_at_upper {α₁ β₁ α₂ β₂ : ℝ}
    (hden : sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2) ≠ 0) :
    blendT α₁ β₁ α₂ β₂ (sideH₂ α₂ β₂ (1 / 2)) = 1 := by
  rw [blendT_eq]
  field_simp [hden]

/-- The blend inverse parameter at the LOWER boundary height
(`y = sideH₁(1/2)`) is 0. -/
lemma blendT_at_lower {α₁ β₁ α₂ β₂ : ℝ}
    (hden : sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2) ≠ 0) :
    blendT α₁ β₁ α₂ β₂ (sideH₁ α₁ β₁ (1 / 2)) = 0 := by
  rw [blendT_eq]
  field_simp [hden]
  ring

/-- The left blend endpoint at parameter `t = 0` is the left point of
the first boundary arc. -/
lemma genA_zero (α₁ β₁ α₂ β₂ : ℝ) : genA α₁ β₁ α₂ β₂ 0 = !₂[(0 : ℝ), α₁] := by
  ext i <;> fin_cases i
  · dsimp [genA]
    rw [genP_coord0]
  · dsimp [genA]
    rw [genP_coord1]
    rw [sideH₁_zero α₁ β₁]
    ring

/-- The left blend endpoint at parameter `t = 1` is the left point of the
second boundary arc. -/
lemma genA_one (α₁ β₁ α₂ β₂ : ℝ) : genA α₁ β₁ α₂ β₂ 1 = !₂[(0 : ℝ), α₂] := by
  ext i <;> fin_cases i
  · dsimp [genA]
    rw [genP_coord0]
  · dsimp [genA]
    rw [genP_coord1]
    rw [sideH₁_zero α₁ β₁, sideH₂_zero α₂ β₂]
    ring

/-- The right blend endpoint at parameter `t = 0` is the right point of
the first boundary arc. -/
lemma genB_zero (α₁ β₁ α₂ β₂ : ℝ) : genB α₁ β₁ α₂ β₂ 0 = !₂[(1 : ℝ), β₁] := by
  ext i <;> fin_cases i
  · dsimp [genB]
    rw [genP_coord0]
  · dsimp [genB]
    rw [genP_coord1]
    rw [sideH₁_one α₁ β₁, sideH₂_one α₂ β₂]
    ring

/-- The right blend endpoint at parameter `t = 1` is the right point of
the second boundary arc. -/
lemma genB_one (α₁ β₁ α₂ β₂ : ℝ) : genB α₁ β₁ α₂ β₂ 1 = !₂[(1 : ℝ), β₂] := by
  ext i <;> fin_cases i
  · dsimp [genB]
    rw [genP_coord0]
  · dsimp [genB]
    rw [genP_coord1]
    rw [sideH₁_one α₁ β₁, sideH₂_one α₂ β₂]
    ring

/-- At the upper boundary height the blend leaf is the UPPER frontier
chord: its left endpoint is the left point of the second boundary arc. -/
lemma blendBend_upper_A {α₁ β₁ α₂ β₂ : ℝ}
    (hden : sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2) ≠ 0) :
    (blendBend α₁ β₁ α₂ β₂ (sideH₂ α₂ β₂ (1 / 2))).A = !₂[(0 : ℝ), α₂] := by
  ext i <;> fin_cases i
  · simp [blendBend, genA, genP_coord0]
  · have h : ((blendBend α₁ β₁ α₂ β₂ (sideH₂ α₂ β₂ (1 / 2))).A) 1 = α₂ := by
      rw [blendBend_A_eq]
      rw [blendT_at_upper hden]
      dsimp [genA]
      rw [genP_coord1]
      rw [sideH₁_zero α₁ β₁, sideH₂_zero α₂ β₂]
      ring
    simpa using h

/-- At the upper boundary height the blend leaf is the UPPER frontier
chord: its right endpoint is the right point of the second boundary arc. -/
lemma blendBend_upper_B {α₁ β₁ α₂ β₂ : ℝ}
    (hden : sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2) ≠ 0) :
    (blendBend α₁ β₁ α₂ β₂ (sideH₂ α₂ β₂ (1 / 2))).B = !₂[(1 : ℝ), β₂] := by
  ext i <;> fin_cases i
  · simp [blendBend, genB, genP_coord0]
  · have h : ((blendBend α₁ β₁ α₂ β₂ (sideH₂ α₂ β₂ (1 / 2))).B) 1 = β₂ := by
      rw [blendBend_B_eq]
      rw [blendT_at_upper hden]
      dsimp [genB]
      rw [genP_coord1]
      rw [sideH₁_one α₁ β₁, sideH₂_one α₂ β₂]
      ring
    simpa using h

/-- At the lower boundary height the blend leaf is the LOWER frontier
chord: its left endpoint is the left point of the first boundary arc. -/
lemma blendBend_lower_A {α₁ β₁ α₂ β₂ : ℝ}
    (hden : sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2) ≠ 0) :
    (blendBend α₁ β₁ α₂ β₂ (sideH₁ α₁ β₁ (1 / 2))).A = !₂[(0 : ℝ), α₁] := by
  ext i <;> fin_cases i
  · simp [blendBend, genA, genP_coord0]
  · have h : ((blendBend α₁ β₁ α₂ β₂ (sideH₁ α₁ β₁ (1 / 2))).A) 1 = α₁ := by
      rw [blendBend_A_eq]
      rw [blendT_at_lower hden]
      dsimp [genA]
      rw [genP_coord1]
      rw [sideH₁_zero α₁ β₁, sideH₂_zero α₂ β₂]
      ring
    simpa using h

/-- At the lower boundary height the blend leaf is the LOWER frontier
chord: its right endpoint is the right point of the first boundary arc. -/
lemma blendBend_lower_B {α₁ β₁ α₂ β₂ : ℝ}
    (hden : sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2) ≠ 0) :
    (blendBend α₁ β₁ α₂ β₂ (sideH₁ α₁ β₁ (1 / 2))).B = !₂[(1 : ℝ), β₁] := by
  ext i <;> fin_cases i
  · simp [blendBend, genB, genP_coord0]
  · have h : ((blendBend α₁ β₁ α₂ β₂ (sideH₁ α₁ β₁ (1 / 2))).B) 1 = β₁ := by
      rw [blendBend_B_eq]
      rw [blendT_at_lower hden]
      dsimp [genB]
      rw [genP_coord1]
      rw [sideH₁_one α₁ β₁, sideH₂_one α₂ β₂]
      ring
    simpa using h

/-- The blend inverse parameter of the canonical data at the upper
boundary height `h₂` is 1. -/
lemma flatCompBend_blendT_top {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂) :
    blendT (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
           (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 h₂ = 1 := by
  rw [blendT_eq]
  have h1 := sideH₁_data_half hf ha p hp hh₁
  have h2 := sideH₁_data_half hf ha p hp hh₂
  rw [h1]
  rw [sideH₂_eq_sideH₁, h2]
  rw [div_self (sub_ne_zero.mpr (ne_of_gt hlt))]

/-- The blend inverse parameter of the canonical data at the lower
boundary height `h₁` is 0. -/
lemma flatCompBend_blendT_bot {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂) :
    blendT (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
           (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 h₁ = 0 := by
  rw [blendT_eq]
  have h1 := sideH₁_data_half hf ha p hp hh₁
  have h2 := sideH₁_data_half hf ha p hp hh₂
  rw [h1]
  rw [sideH₂_eq_sideH₁, h2]
  ring_nf

/-- **The component leaf at the upper frontier height is the upper
frontier chord**: left endpoint on the left seam at the upper data's left
height. -/

lemma flatCompBend_upper_A {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂) :
    (flatCompBend hf ha p hp h₁ h₂ h₂ hh₁ hh₂).A =
      !₂[(0 : ℝ), (frCompData hf ha p hp h₂ hh₂).1] := by
  unfold flatCompBend
  have ht := flatCompBend_blendT_top hf ha p hp hh₁ hh₂ hlt
  calc
    (blendBend (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 h₂).A
        = genA (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
            (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2
            (blendT (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
              (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 h₂) := by
            rw [blendBend_A_eq]
    _ = genA (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
            (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 1 := by
            rw [ht]
    _ = !₂[(0 : ℝ), (frCompData hf ha p hp h₂ hh₂).1] := by
            exact genA_one (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
              (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2

/-- **The component leaf at the upper frontier height is the upper
frontier chord**: right endpoint on the right seam at the upper data's
right height. -/
lemma flatCompBend_upper_B {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂) :
    (flatCompBend hf ha p hp h₁ h₂ h₂ hh₁ hh₂).B =
      !₂[(1 : ℝ), (frCompData hf ha p hp h₂ hh₂).2] := by
  unfold flatCompBend
  have ht := flatCompBend_blendT_top hf ha p hp hh₁ hh₂ hlt
  calc
    (blendBend (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 h₂).B
        = genB (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
            (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2
            (blendT (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
              (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 h₂) := by
            rw [blendBend_B_eq]
    _ = genB (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
            (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 1 := by
            rw [ht]
    _ = !₂[(1 : ℝ), (frCompData hf ha p hp h₂ hh₂).2] := by
            exact genB_one (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
              (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2

/-- **The component leaf at the lower frontier height is the lower
frontier chord** (left endpoint). -/
lemma flatCompBend_lower_A {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂) :
    (flatCompBend hf ha p hp h₁ h₂ h₁ hh₁ hh₂).A =
      !₂[(0 : ℝ), (frCompData hf ha p hp h₁ hh₁).1] := by
  unfold flatCompBend
  have ht := flatCompBend_blendT_bot hf ha p hp hh₁ hh₂ hlt
  calc
    (blendBend (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 h₁).A
        = genA (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
            (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2
            (blendT (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
              (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 h₁) := by
            rw [blendBend_A_eq]
    _ = genA (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
            (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 0 := by
            rw [ht]
    _ = !₂[(0 : ℝ), (frCompData hf ha p hp h₁ hh₁).1] := by
            exact genA_zero (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
              (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2

/-- **The component leaf at the lower frontier height is the lower
frontier chord** (right endpoint). -/
lemma flatCompBend_lower_B {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂) :
    (flatCompBend hf ha p hp h₁ h₂ h₁ hh₁ hh₂).B =
      !₂[(1 : ℝ), (frCompData hf ha p hp h₁ hh₁).2] := by
  unfold flatCompBend
  have ht := flatCompBend_blendT_bot hf ha p hp hh₁ hh₂ hlt
  calc
    (blendBend (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 h₁).B
        = genB (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
            (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2
            (blendT (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
              (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 h₁) := by
            rw [blendBend_B_eq]
    _ = genB (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
            (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 0 := by
            rw [ht]
    _ = !₂[(1 : ℝ), (frCompData hf ha p hp h₁ hh₁).2] := by
            exact genB_zero (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
              (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2



/-- **Flat-side one-sided limit (left endpoint)**: flat leaves of a
component at heights `yₙ → h₂` (the upper frontier height) have LEFT
endpoints converging to the upper frontier chord's left seam point
`(0, α₂)`.  This is the flat-side half of the frontier-height gluing:
continuity of the closed-interval leaf family at its boundary plus the
frontier-chord value `flatCompBend_upper_A`. -/
theorem flatCompBend_left_endpoint_limit {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    {y : ℕ → ℝ} (hylim : Tendsto y atTop (𝓝 h₂)) :
    Tendsto (fun n : ℕ => (flatCompBend hf ha p hp h₁ h₂ (y n) hh₁ hh₂).A) atTop
      (𝓝 (!₂[(0 : ℝ), (frCompData hf ha p hp h₂ hh₂).1])) := by
  have hcont := flatCompBend_A_cont hf ha p hp hh₁ hh₂
  have ht := (hcont.continuousAt (x := h₂)).tendsto.comp hylim
  have hval := flatCompBend_upper_A hf ha p hp hh₁ hh₂ hlt
  have hnh : (fun w : ℝ² => 𝓝 w) ((flatCompBend hf ha p hp h₁ h₂ h₂ hh₁ hh₂).A) =
      (fun w : ℝ² => 𝓝 w) (!₂[(0 : ℝ), (frCompData hf ha p hp h₂ hh₂).1]) :=
    congrArg (fun w : ℝ² => 𝓝 w) hval
  change Tendsto (fun n : ℕ => (flatCompBend hf ha p hp h₁ h₂ (y n) hh₁ hh₂).A) atTop
      ((fun w : ℝ² => 𝓝 w) (!₂[(0 : ℝ), (frCompData hf ha p hp h₂ hh₂).1]))
  rw [← hnh]
  exact ht

/-- **Flat-side one-sided limit (right endpoint)**: flat leaves of a
component at heights `yₙ → h₂` have RIGHT endpoints converging to the
upper frontier chord's right seam point `(1, β₂)`. -/
theorem flatCompBend_right_endpoint_limit {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    {y : ℕ → ℝ} (hylim : Tendsto y atTop (𝓝 h₂)) :
    Tendsto (fun n : ℕ => (flatCompBend hf ha p hp h₁ h₂ (y n) hh₁ hh₂).B) atTop
      (𝓝 (!₂[(1 : ℝ), (frCompData hf ha p hp h₂ hh₂).2])) := by
  have hcont := flatCompBend_B_cont hf ha p hp hh₁ hh₂
  have ht := (hcont.continuousAt (x := h₂)).tendsto.comp hylim
  have hval := flatCompBend_upper_B hf ha p hp hh₁ hh₂ hlt
  have hnh : (fun w : ℝ² => 𝓝 w) ((flatCompBend hf ha p hp h₁ h₂ h₂ hh₁ hh₂).B) =
      (fun w : ℝ² => 𝓝 w) (!₂[(1 : ℝ), (frCompData hf ha p hp h₂ hh₂).2]) :=
    congrArg (fun w : ℝ² => 𝓝 w) hval
  change Tendsto (fun n : ℕ => (flatCompBend hf ha p hp h₁ h₂ (y n) hh₁ hh₂).B) atTop
      ((fun w : ℝ² => 𝓝 w) (!₂[(1 : ℝ), (frCompData hf ha p hp h₂ hh₂).2]))
  rw [← hnh]
  exact ht


/-- **U-side left endpoint at a frontier height (instantiated)**: U-centre
heights approaching the upper frontier height `h₂` of a component give
U-leaf LEFT endpoints converging to the frontier chord's left seam point
`(0, α₂)`. -/
theorem frontier_glue_left_uBend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2)
    {y : ℕ → ℝ} (hyU : ∀ n : ℕ, dN f (centrePoint (y n)) ≠ 0)
    (hylim : Tendsto y atTop (𝓝 (sideH₁ (frCompData hf ha p hp h₂ hh₂).1
        (frCompData hf ha p hp h₂ hh₂).2 (1 / 2)))) :
    Tendsto (fun n : ℕ => uBendA hf ha (centrePoint_mem_stripInterior (y n)) (hyU n))
      atTop (𝓝 (!₂[(0 : ℝ), (frCompData hf ha p hp h₂ hh₂).1])) := by
  have hflat := frontier_chord_flat hf ha hp hh₁ hh₂ hlt hC
  exact uBend_left_endpoint_limit hf ha (α := (frCompData hf ha p hp h₂ hh₂).1)
    (β := (frCompData hf ha p hp h₂ hh₂).2) hyU hylim hflat

/-- **Frontier-height gluing (left endpoints)**: whether approached from
the `U` side or along the flat leaves of the component, the leaf LEFT
endpoints converge to the same limit — the upper frontier chord's left
seam point `(0, α₂)`.  This is the one-sided-limit coherence that the
splice needs at the frontier height (no classification of the "other
side" required). -/
theorem frontier_glue_left_agree {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2)
    {u : ℕ → ℝ} (huU : ∀ n : ℕ, dN f (centrePoint (u n)) ≠ 0)
    (hu : Tendsto u atTop (𝓝 (sideH₁ (frCompData hf ha p hp h₂ hh₂).1
        (frCompData hf ha p hp h₂ hh₂).2 (1 / 2))))
    {v : ℕ → ℝ} (hv : Tendsto v atTop (𝓝 (sideH₁ (frCompData hf ha p hp h₂ hh₂).1
        (frCompData hf ha p hp h₂ hh₂).2 (1 / 2)))) :
    Tendsto (fun n : ℕ => uBendA hf ha (centrePoint_mem_stripInterior (u n)) (huU n))
        atTop (𝓝 (!₂[(0 : ℝ), (frCompData hf ha p hp h₂ hh₂).1])) ∧
    Tendsto (fun n : ℕ => (flatCompBend hf ha p hp h₁ h₂ (v n) hh₁ hh₂).A)
        atTop (𝓝 (!₂[(0 : ℝ), (frCompData hf ha p hp h₂ hh₂).1])) := by
  have hc : sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 (1 / 2) = h₂ :=
    sideH₁_data_half hf ha p hp hh₂
  constructor
  · exact frontier_glue_left_uBend hf ha p hp hh₁ hh₂ hlt hC huU hu
  · have hv' : Tendsto v atTop (𝓝 h₂) := by
      rw [← hc]
      exact hv
    exact flatCompBend_left_endpoint_limit hf ha p hp hh₁ hh₂ hlt hv'


/-- **U-side right endpoint at a frontier height (instantiated)**. -/
theorem frontier_glue_right_uBend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2)
    {y : ℕ → ℝ} (hyU : ∀ n : ℕ, dN f (centrePoint (y n)) ≠ 0)
    (hylim : Tendsto y atTop (𝓝 (sideH₁ (frCompData hf ha p hp h₂ hh₂).1
        (frCompData hf ha p hp h₂ hh₂).2 (1 / 2)))) :
    Tendsto (fun n : ℕ => uBendB hf ha (centrePoint_mem_stripInterior (y n)) (hyU n))
      atTop (𝓝 (!₂[(1 : ℝ), (frCompData hf ha p hp h₂ hh₂).2])) := by
  have hflat := frontier_chord_flat hf ha hp hh₁ hh₂ hlt hC
  exact uBend_right_endpoint_limit hf ha (α := (frCompData hf ha p hp h₂ hh₂).1)
    (β := (frCompData hf ha p hp h₂ hh₂).2) hyU hylim hflat

/-- **Frontier-height gluing (right endpoints)**: U-side and flat-side
leaf RIGHT endpoints converge to the same limit, the upper frontier
chord's right seam point `(1, β₂)`. -/
theorem frontier_glue_right_agree {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2)
    {u : ℕ → ℝ} (huU : ∀ n : ℕ, dN f (centrePoint (u n)) ≠ 0)
    (hu : Tendsto u atTop (𝓝 (sideH₁ (frCompData hf ha p hp h₂ hh₂).1
        (frCompData hf ha p hp h₂ hh₂).2 (1 / 2))))
    {v : ℕ → ℝ} (hv : Tendsto v atTop (𝓝 (sideH₁ (frCompData hf ha p hp h₂ hh₂).1
        (frCompData hf ha p hp h₂ hh₂).2 (1 / 2)))) :
    Tendsto (fun n : ℕ => uBendB hf ha (centrePoint_mem_stripInterior (u n)) (huU n))
        atTop (𝓝 (!₂[(1 : ℝ), (frCompData hf ha p hp h₂ hh₂).2])) ∧
    Tendsto (fun n : ℕ => (flatCompBend hf ha p hp h₁ h₂ (v n) hh₁ hh₂).B)
        atTop (𝓝 (!₂[(1 : ℝ), (frCompData hf ha p hp h₂ hh₂).2])) := by
  have hc : sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 (1 / 2) = h₂ :=
    sideH₁_data_half hf ha p hp hh₂
  constructor
  · exact frontier_glue_right_uBend hf ha p hp hh₁ hh₂ hlt hC huU hu
  · have hv' : Tendsto v atTop (𝓝 h₂) := by
      rw [← hc]
      exact hv
    exact flatCompBend_right_endpoint_limit hf ha p hp hh₁ hh₂ hlt hv'
end Submission
