import Submission.Work.Main0Interface
import Submission.Work.SpliceLeaves
import Submission.Work.FlatBendData
import Submission.Work.ComponentLeaves
import Submission.Work.FlatDeck
import Submission.Work.FrontierDeck

open OptimalMoebius Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Per-component flat-leaf BendData packaging

For a flat component `C = flatComponent f p` with canonical boundary-arc
data `d₁ = (α₁,β₁)`, `d₂ = (α₂,β₂)` at heights `h₁ < h₂`, the blended
leaf through the centreline height `y` is the straight chord

    A y := genA d₁ d₂ (blendT d₁ d₂ y)   (on x0 = 0)
    B y := genB d₁ d₂ (blendT d₁ d₂ y)   (on x0 = 1)

packaged here as a `Submission.BendData`:

* `blendBend` — the generic chord (`genP`-blend of two boundary arcs);
* `blendBend_centre` — it crosses the centreline at height `y`:
  `centreHeight = y` (`genP_half` + affine side arithmetic);
* `flatCompBend` — the same with the canonical data of a flat component;
  `flatCompBend_centre` (needs only `h₁ < h₂`), and
  `flatCompBend_preBend` — every leaf inside the component is a pre-bend
  (`blend_leaf_preBend`, with the leaf-inside-C membership coming from
  `blend_inside` + the between-representation `hC`);
* `blendBend_deck` — the deck at the BendData level: the flipped-data
  blend at `y + a` is the period image of the original blend at `y`
  (`blendT_deck` + `period_deck_genP`), so
  `A (y+a) = period a (B y)` and `B (y+a) = period a (A y)`;
* `flatCompBend_deck` — the component-leaf deck: with `h₁' < h₂'`
  between-representation heights of the deck-image component, the
  component leaf at `y + a` there is the period image of the component
  leaf at `y` here (B3 data-flip + `blendBend_deck`).

Namespace `Submission` (consistent with `BendData`/`BandFoliation`).

Build: `lake build Submission.Work.FlatLeafBendData` rc=0, zero sorry.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- The blended leaf of two boundary arcs at centreline height `y`, as a
`BendData`: the chord from the fraction-`t` point of the left arc to that
of the right arc, `t = blendT … y`. -/
def blendBend (α₁ β₁ α₂ β₂ y : ℝ) : BendData where
  A := genA α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)
  B := genB α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)
  left_coord := by
    dsimp [genA]
    exact genP_coord0 α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y) 0
  right_coord := by
    dsimp [genB]
    exact genP_coord0 α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y) 1

/-- The left endpoint of the blend is `genA` at the inverse parameter. -/
lemma blendBend_A_eq (α₁ β₁ α₂ β₂ y : ℝ) :
    (blendBend α₁ β₁ α₂ β₂ y).A = genA α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y) := by rfl

/-- The right endpoint of the blend is `genB` at the inverse parameter. -/
lemma blendBend_B_eq (α₁ β₁ α₂ β₂ y : ℝ) :
    (blendBend α₁ β₁ α₂ β₂ y).B = genB α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y) := by rfl

/-- `sideH₂` at `x0 = 0`. -/
lemma sideH₂_zero (α β : ℝ) : sideH₂ α β 0 = α := by
  dsimp [sideH₂]
  ring

/-- `sideH₂` at `x0 = 1`. -/
lemma sideH₂_one (α β : ℝ) : sideH₂ α β 1 = β := by
  dsimp [sideH₂]
  ring

/-- The affine side-line height at `x0 = 1/2` is the average of the
endpoint heights. -/
lemma sideH₁_half_avg (α β : ℝ) : sideH₁ α β (1 / 2) = (α + β) / 2 := by
  dsimp [sideH₁]
  ring

/-- The affine `sideH₂` height at `x0 = 1/2` is the same average. -/
lemma sideH₂_half_avg (α β : ℝ) : sideH₂ α β (1 / 2) = (α + β) / 2 := by
  dsimp [sideH₂]
  ring

/-- The left endpoint height of the blend: `A1 = (1−t)α₁ + tα₂`. -/
lemma blendA1_formula' (α₁ β₁ α₂ β₂ t : ℝ) :
    (genA α₁ β₁ α₂ β₂ t) 1 = (1 - t) * α₁ + t * α₂ := by
  dsimp [genA]
  rw [genP_coord1]
  have h1 := sideH₁_zero α₁ β₁
  have h2 := sideH₂_zero α₂ β₂
  rw [h1, h2]

/-- The right endpoint height of the blend: `B1 = (1−t)β₁ + tβ₂`. -/
lemma blendB1_formula' (α₁ β₁ α₂ β₂ t : ℝ) :
    (genB α₁ β₁ α₂ β₂ t) 1 = (1 - t) * β₁ + t * β₂ := by
  dsimp [genB]
  rw [genP_coord1]
  have h1 := sideH₁_one α₁ β₁
  have h2 := sideH₂_one α₂ β₂
  rw [h1, h2]

/-- **The blend crosses the centreline at its own height**: for data with
distinct half-heights (`sideH₂(1/2) ≠ sideH₁(1/2)`), the midpoint of the
blend at centre height `y` has height `y`. -/
lemma blendBend_centre {α₁ β₁ α₂ β₂ y : ℝ}
    (hden : sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2) ≠ 0) :
    (blendBend α₁ β₁ α₂ β₂ y).centreHeight = y := by
  unfold BendData.centreHeight
  unfold blendBend
  let t : ℝ := blendT α₁ β₁ α₂ β₂ y
  -- A1 + B1 = 2 · (genP t (1/2))1:
  have hsum : (genA α₁ β₁ α₂ β₂ t) 1 + (genB α₁ β₁ α₂ β₂ t) 1 =
      2 * (genP α₁ β₁ α₂ β₂ t (1 / 2)) 1 := by
    rw [blendA1_formula' α₁ β₁ α₂ β₂ t]
    rw [blendB1_formula' α₁ β₁ α₂ β₂ t]
    rw [genP_coord1]
    rw [sideH₁_half_avg α₁ β₁]
    rw [sideH₂_half_avg α₂ β₂]
    ring
  have hhalf : (genP α₁ β₁ α₂ β₂ t (1 / 2)) 1 = y := by
    dsimp [t, blendT]
    -- blendP_half needs hden in terms of sideH₂ - sideH₁ (it uses blendP):
    simpa [blendP] using (blendP_half (α₁ := α₁) (β₁ := β₁) (α₂ := α₂) (β₂ := β₂) (y := y) hden)
  -- ((A1+B1)/2) = y:
  have hsum2 : (genA α₁ β₁ α₂ β₂ t) 1 + (genB α₁ β₁ α₂ β₂ t) 1 = 2 * y := by
    rw [hsum, hhalf]
  have hden2 : (2 : ℝ) ≠ 0 := by norm_num
  field_simp [hden2]
  linarith

/-- The canonical data of a flat component at its two boundary heights,
packaged as a bend through centre height `y`. -/
noncomputable def flatCompBend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) (h₁ h₂ y : ℝ)
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) : BendData :=
  blendBend (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
            (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 y

/-- The half-height difference of the canonical data equals `h₂ − h₁`. -/
lemma flatCompBend_hden {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂) :
    sideH₂ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 (1 / 2) -
      sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 (1 / 2) ≠ 0 := by
  have h₁' := sideH₁_data_half hf ha p hp hh₁
  have h₂' := sideH₁_data_half hf ha p hp hh₂
  rw [sideH₂_eq_sideH₁, h₁', h₂']
  exact ne_of_gt (sub_pos.mpr hlt)

/-- **The flat-component leaf crosses the centreline at its own height**. -/
theorem flatCompBend_centre {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ y : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂) :
    (flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).centreHeight = y := by
  unfold flatCompBend
  exact blendBend_centre (flatCompBend_hden hf ha p hp hh₁ hh₂ hlt)

/-- **The flat-component leaves are pre-bends**: with the canonical data
and the between-representation, the blend leaf at centre height
`y ∈ (h₁,h₂)` has isometric image. -/
theorem flatCompBend_preBend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ y : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2)
    (hy : y ∈ Set.Ioo h₁ h₂) :
    ‖f ((flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).B) -
        f ((flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).A)‖ =
    ‖(flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).B -
        (flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).A‖ := by
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
  have hord : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ d₁.1 d₁.2 u < sideH₁ d₂.1 d₂.2 u := by
    intro u hu
    simpa [d₁, d₂] using (sideH₁_lt_of_heights hf ha p hp hh₁ hh₂ hlt u hu)
  have hip : ∀ y' u : ℝ,
      y' ∈ Set.Ioo (sideH₁ d₁.1 d₁.2 (1 / 2)) (sideH₁ d₂.1 d₂.2 (1 / 2)) →
      u ∈ Set.Ioo (0 : ℝ) 1 → blendP d₁.1 d₁.2 d₂.1 d₂.2 y' u ∈ flatComponent f p := by
    intro y' u hyu hu
    have hb := blend_inside (hord := hord) (y := y') (u := u) hyu hu
    -- hb : blendP … ∈ betweenChord d₁ d₂
    rw [hC]
    exact hb
  have hpb := blend_leaf_preBend hf (p := p) (α₁ := d₁.1) (β₁ := d₁.2)
    (α₂ := d₂.1) (β₂ := d₂.2) hip hy'
  dsimp [d₁, d₂, flatCompBend] at hpb ⊢
  exact hpb

/-- **BendData-level deck of the blend**: the flipped-data blend at
`y + a` is the period image of the original blend at `y` — left endpoint
of the deck leaf is the period of the original right endpoint, and vice
versa. -/
theorem blendBend_deck {a α₁ β₁ α₂ β₂ y : ℝ} :
    (blendBend (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) (y + a)).A =
        period a (blendBend α₁ β₁ α₂ β₂ y).B ∧
    (blendBend (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) (y + a)).B =
        period a (blendBend α₁ β₁ α₂ β₂ y).A := by
  let t : ℝ := blendT α₁ β₁ α₂ β₂ y
  have ht : blendT (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) (y + a) = t := by
    dsimp [t]
    exact blendT_deck (a := a) (α₁ := α₁) (β₁ := β₁) (α₂ := α₂) (β₂ := β₂) (y := y)
  constructor
  · -- A(y+a) = period(B y): both sides equal genP(flip, t, 0)
    calc
      (blendBend (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) (y + a)).A
          = genA (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) t := by
              unfold blendBend
              rw [ht]
      _ = period a (genB α₁ β₁ α₂ β₂ t) := by
              -- period a (genP orig t 1) = genP flip t 0
              have hper := period_deck_genP (a := a) (α₁ := α₁) (β₁ := β₁) (α₂ := α₂) (β₂ := β₂)
                (t := t) (u := 1)
              have hper0 : genP (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) t 0 =
                  period a (genP α₁ β₁ α₂ β₂ t 1) := by
                simpa [show (1 : ℝ) - 1 = 0 by norm_num] using hper.symm
              simpa [genA, genB] using hper0
      _ = period a (blendBend α₁ β₁ α₂ β₂ y).B := by
              unfold blendBend
              rfl
  · calc
      (blendBend (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) (y + a)).B
          = genB (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) t := by
              unfold blendBend
              rw [ht]
      _ = period a (genA α₁ β₁ α₂ β₂ t) := by
              have hper := period_deck_genP (a := a) (α₁ := α₁) (β₁ := β₁) (α₂ := α₂) (β₂ := β₂)
                (t := t) (u := 0)
              -- hper : period a (genP orig t 0) = genP flip t (1 - 0)
              have hper0 : genP (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) t 1 =
                  period a (genP α₁ β₁ α₂ β₂ t 0) := by
                simpa [show (1 : ℝ) - 0 = 1 by norm_num] using hper.symm
              simpa [genA, genB] using hper0
      _ = period a (blendBend α₁ β₁ α₂ β₂ y).A := by
              unfold blendBend
              rfl


/-- **BendData-level deck of the component leaves**: if `h₁' < h₂'` are
between-representation heights of the deck-image component
(`flatComponent f (period a p)`), then the component leaf at `y + a`
there is the period image of the component leaf at `y` here:
`A (y+a) = period a (B y)`, `B (y+a) = period a (A y)`.  This is the
`BandFoliation.deck` axiom content on the flat heights (B3 data-flip +
`blendBend_deck`). -/
theorem flatCompBend_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ h₁' h₂' y : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2)
    {hp' : period a p ∈ interior (FlatSet f)}
    (hh₁' : h₁' ∈ frHeights f (period a p)) (hh₂' : h₂' ∈ frHeights f (period a p))
    (hlt' : h₁' < h₂') :
    (flatCompBend hf ha (period a p) hp' h₁' h₂' (y + a) hh₁' hh₂').A =
        period a (flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).B ∧
    (flatCompBend hf ha (period a p) hp' h₁' h₂' (y + a) hh₁' hh₂').B =
        period a (flatCompBend hf ha p hp h₁ h₂ y hh₁ hh₂).A := by
  let d₁ : ℝ × ℝ := frCompData hf ha p hp h₁ hh₁
  let d₂ : ℝ × ℝ := frCompData hf ha p hp h₂ hh₂
  have hdat := between_data_deck_data hf ha hp hh₁ hh₂ hlt hC
    (hp' := hp') hh₁' hh₂' hlt'
  -- hdat.1 : frCompData (period a p) hp' h₁' hh₁' = ((d₁).2+a,(d₁).1+a) (up to d-lets)
  have hdat₁ : frCompData hf ha (period a p) hp' h₁' hh₁' = (d₁.2 + a, d₁.1 + a) := by
    simpa [d₁, d₂] using hdat.1
  have hdat₂ : frCompData hf ha (period a p) hp' h₂' hh₂' = (d₂.2 + a, d₂.1 + a) := by
    simpa [d₁, d₂] using hdat.2
  have hmain := blendBend_deck (a := a) (α₁ := d₁.1) (β₁ := d₁.2)
    (α₂ := d₂.1) (β₂ := d₂.2) (y := y)
  -- hmain : (blendBend (d₁.2+a)(d₁.1+a)(d₂.2+a)(d₂.1+a) (y+a)).A = period a (blendBend d₁.1 d₁.2 d₂.1 d₂.2 y).B ∧ …
  unfold flatCompBend
  rw [hdat₁, hdat₂]
  dsimp [d₁, d₂] at hmain ⊢
  exact hmain

end Submission
