import Submission.Work.FlatLeafPreBend
import Submission.Work.SpliceLeaves
import Submission.Work.ComponentLeaves
import Submission.Work.RegionBetween

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Blend-leaf pre-bend (FlatBendData)

Connects the component blend leaves (`SpliceLeaves.blendP`) with the
seam-chord pre-bend theorem (`FlatLeafPreBend.seam_chord_preBend`): a
blended leaf through a centreline height `y` (endpoints `genA`/`genB` at
the blend parameter `t = blendT y`) whose interior points lie in a flat
component has an isometric image:

* `segP_genP` — the segment between `genA t` and `genB t` at parameter
  `u` is exactly `genP t u` (so the interior points of the leaf chord are
  the blend points);
* **`blend_leaf_preBend`** — for data with the leaf-inside hypothesis
  (e.g. supplied per component by
  `ComponentLeaves.flatComponent_blend_leaves`), `‖f B − f A‖ =
  ‖B − A‖` for the chord `[genA t, genB t]`, `t := blendT … y`,
  `y ∈ (c₁,c₂)`.

Together with `blendP_half` (the leaf crosses the centreline at its own
height), `ComponentLeaves.flatComponent_blend_leaves` (leaves inside the
component, continuous endpoint heights), this gives every flat leaf the
four `BandFoliation` properties (centre, seam coordinates, preBend,
continuity) at the component level.

Build: `lake build Submission.Work.FlatBendData` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- The segment between the two blend endpoints at parameter `u` is the
blend point itself: `segP (genA t) (genB t) u = genP t u`. -/
lemma segP_genP (α₁ β₁ α₂ β₂ t u : ℝ) :
    segP (genA α₁ β₁ α₂ β₂ t) (genB α₁ β₁ α₂ β₂ t) u =
      genP α₁ β₁ α₂ β₂ t u := by
  ext i <;> fin_cases i
  · -- coordinate 0: both sides are u
    dsimp [segP, genA, genB, genP]
    simp
  · -- coordinate 1: expand the affine side functions
    dsimp [segP, genA, genB, genP, sideH₁, sideH₂]
    ring_nf

/-- `genA t` lies in the closed unit strip (it is on the left seam). -/
lemma genA_mem_unitStrip (α₁ β₁ α₂ β₂ t : ℝ) :
    genA α₁ β₁ α₂ β₂ t ∈ unitStrip := by
  rw [unitStrip]
  change (genA α₁ β₁ α₂ β₂ t) 0 ∈ Set.Icc (0 : ℝ) 1
  rw [genA, genP_coord0]
  norm_num

/-- `genB t` lies in the closed unit strip (it is on the right seam). -/
lemma genB_mem_unitStrip (α₁ β₁ α₂ β₂ t : ℝ) :
    genB α₁ β₁ α₂ β₂ t ∈ unitStrip := by
  rw [unitStrip]
  change (genB α₁ β₁ α₂ β₂ t) 0 ∈ Set.Icc (0 : ℝ) 1
  rw [genB, genP_coord0]
  norm_num

/-- **A blend leaf whose interior lies in a flat component is a
pre-bend**: for `t := blendT α₁β₁α₂β₂ y` with `y` a centre height of the
between region, `‖f (genB t) − f (genA t)‖ = ‖genB t − genA t‖`. -/
theorem blend_leaf_preBend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} {α₁ β₁ α₂ β₂ : ℝ}
    (hip : ∀ y u : ℝ,
      y ∈ Set.Ioo (sideH₁ α₁ β₁ (1 / 2)) (sideH₁ α₂ β₂ (1 / 2)) →
      u ∈ Set.Ioo (0 : ℝ) 1 → blendP α₁ β₁ α₂ β₂ y u ∈ flatComponent f p)
    {y : ℝ} (hy : y ∈ Set.Ioo (sideH₁ α₁ β₁ (1 / 2)) (sideH₁ α₂ β₂ (1 / 2))) :
    ‖f (genB α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) -
        f (genA α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y))‖ =
    ‖genB α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y) -
        genA α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)‖ := by
  let t : ℝ := blendT α₁ β₁ α₂ β₂ y
  have hA : genA α₁ β₁ α₂ β₂ t ∈ unitStrip := genA_mem_unitStrip α₁ β₁ α₂ β₂ t
  have hB : genB α₁ β₁ α₂ β₂ t ∈ unitStrip := genB_mem_unitStrip α₁ β₁ α₂ β₂ t
  have hopen : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      segP (genA α₁ β₁ α₂ β₂ t) (genB α₁ β₁ α₂ β₂ t) s ∈ flatComponent f p := by
    intro s hs
    have hseg : segP (genA α₁ β₁ α₂ β₂ t) (genB α₁ β₁ α₂ β₂ t) s = genP α₁ β₁ α₂ β₂ t s :=
      segP_genP α₁ β₁ α₂ β₂ t s
    rw [hseg]
    dsimp [t, blendP]
    exact hip y s hy hs
  exact seam_chord_preBend hf hA hB hopen



/-- **Per-component leaf pre-bend**: for a flat component `C =
flatComponent f p`, the blended leaf at every centre height
`y ∈ (h₁,h₂)` of its canonical between representation is a pre-bend:
`‖f (genB t) − f (genA t)‖ = ‖genB t − genA t‖` with
`t := blendT (data h₁) (data h₂) y`. -/
theorem flatComponent_blend_preBend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    ∃ h₁ h₂ : ℝ, ∃ hh₁ : h₁ ∈ frHeights f p, ∃ hh₂ : h₂ ∈ frHeights f p,
      h₁ < h₂ ∧
      (∀ y : ℝ, y ∈ Set.Ioo h₁ h₂ →
        ‖f (genB (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
                 (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2
                 (blendT (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
                   (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 y)) -
            f (genA (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
                 (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2
                 (blendT (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
                   (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 y))‖ =
        ‖genB (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
              (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2
              (blendT (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
                (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 y) -
            genA (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
              (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2
              (blendT (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
                (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 y)‖) := by
  rcases flatComponent_blend_leaves hf ha hp with
    ⟨h₁, h₂, hh₁, hh₂, hlt, hcen, hin, hcA, hcB⟩
  refine ⟨h₁, h₂, hh₁, hh₂, hlt, ?_⟩
  intro y hy
  let d₁ : ℝ × ℝ := frCompData hf ha p hp h₁ hh₁
  let d₂ : ℝ × ℝ := frCompData hf ha p hp h₂ hh₂
  have hc₁ : sideH₁ d₁.1 d₁.2 (1 / 2) = h₁ := by
    dsimp [d₁]
    exact sideH₁_data_half hf ha p hp hh₁
  have hc₂ : sideH₁ d₂.1 d₂.2 (1 / 2) = h₂ := by
    dsimp [d₂]
    exact sideH₁_data_half hf ha p hp hh₂
  have hy' : y ∈ Set.Ioo (sideH₁ d₁.1 d₁.2 (1 / 2)) (sideH₁ d₂.1 d₂.2 (1 / 2)) := by
    rwa [hc₁, hc₂]
  have hip : ∀ y u : ℝ,
      y ∈ Set.Ioo (sideH₁ d₁.1 d₁.2 (1 / 2)) (sideH₁ d₂.1 d₂.2 (1 / 2)) →
      u ∈ Set.Ioo (0 : ℝ) 1 → blendP d₁.1 d₁.2 d₂.1 d₂.2 y u ∈ flatComponent f p := by
    intro y' u hyu hu
    have hyu' : y' ∈ Set.Ioo h₁ h₂ := by
      rw [← hc₁, ← hc₂]
      exact hyu
    dsimp [d₁, d₂] at hin ⊢
    exact hin y' u hyu' hu
  have hpb := blend_leaf_preBend hf (p := p) (α₁ := d₁.1) (β₁ := d₁.2)
    (α₂ := d₂.1) (β₂ := d₂.2) hip hy'
  -- hpb : ‖f (genB … t) − f (genA … t)‖ = ‖genB … t − genA … t‖ with t := blendT d-data y
  dsimp [d₁, d₂] at hpb ⊢
  exact hpb

end Submission.PaperBand
