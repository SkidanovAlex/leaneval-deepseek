import Submission.Work.DeckFrontier
import Submission.Work.FlatComponents
import Submission.Work.CentrelineUBends
import Submission.Work.FlatBetween
import Submission.Work.RegionBetween
import Submission.Work.SpliceLeaves

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Deck invariance of flat components (FlatDeck)

The flat component `flatComponent f p` is the connected component of
`p` in `s := interior (FlatSet f)`.  Since `period a` is a
homeomorphism of the plane carrying `s` onto itself
(`interior_flatSet_period_image`), it maps connected components to
connected components:

* `homeo_connectedComponentIn_eq_self` — the generic statement: a
  homeomorphism `e` with `e '' s = s` maps `connectedComponentIn s x`
  onto `connectedComponentIn s (e x)`;
* `flatComponent_deck` — `period a '' flatComponent f p =
  flatComponent f (period a p)` (for `p ∈ interior (FlatSet f)`; the
  deck map is a bijection of the flat-interior onto itself);
* `flatComponent_periodInv_deck` — the same for the inverse `periodInv`;
* centreline specialisation `flatComponent_centre_deck` — the component
  at centreline height `y + a` is the deck image of the component at
  height `y` (when the centreline point is flat-interior), via
  `centrePoint_period`.

This is the flat-side counterpart of the U-leaf deck
(`uHeightBend_deck`) needed by the Prop-main0 splice: the eventual
`BandFoliation` leaf at height `y+a` must be the period-flip of the leaf
at `y` on the flat heights too.

Build: `lake build Submission.Work.FlatDeck` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- A homeomorphism of a space onto itself maps the connected-component-in
sets of an invariant subset onto themselves: `e '' conn s x = conn s (e x)`. -/
lemma homeo_connectedComponentIn_eq_self {X : Type*} [TopologicalSpace X] (e : X ≃ₜ X)
    {s : Set X} (hs : e '' s = s) (x : X) (hx : x ∈ s) :
    e '' connectedComponentIn s x = connectedComponentIn s (e x) := by
  apply le_antisymm
  · have h1 : e '' connectedComponentIn s x ⊆ connectedComponentIn (e '' s) (e x) :=
      ContinuousOn.image_connectedComponentIn_subset (f := e) (s := s) (a := x)
        e.continuous.continuousOn hx
    simpa [hs] using h1
  · have hx' : e x ∈ s := by
      have : e x ∈ e '' s := ⟨x, hx, rfl⟩
      simpa [hs] using this
    have hcomp : e.symm ∘ e = id := by
      funext z
      exact e.left_inv z
    have hseq : e.symm '' s = s := by
      calc
        e.symm '' s = e.symm '' (e '' s) := by rw [hs]
        _ = (e.symm ∘ e) '' s := by rw [← Set.image_comp]
        _ = id '' s := by rw [hcomp]
        _ = s := by ext y; simp
    have h2 : e.symm '' connectedComponentIn s (e x) ⊆ connectedComponentIn s x := by
      have h2' : e.symm '' connectedComponentIn s (e x) ⊆
          connectedComponentIn (e.symm '' s) (e.symm (e x)) :=
        ContinuousOn.image_connectedComponentIn_subset (f := e.symm) (s := s) (a := e x)
          e.symm.continuous.continuousOn hx'
      have htarget : connectedComponentIn (e.symm '' s) (e.symm (e x)) =
          connectedComponentIn s x := by
        rw [hseq]
        have hpoint : e.symm (e x) = x := e.left_inv x
        rw [hpoint]
      rwa [htarget] at h2'
    have h3 : connectedComponentIn s (e x) ⊆ e '' connectedComponentIn s x := by
      intro y hy
      have hy1 : e.symm y ∈ e.symm '' connectedComponentIn s (e x) := ⟨y, hy, rfl⟩
      have hy2 : e.symm y ∈ connectedComponentIn s x := h2 hy1
      exact ⟨e.symm y, hy2, e.right_inv y⟩
    exact h3

/-- Membership in the flat-interior is preserved by the deck map. -/
lemma mem_interior_FlatSet_period {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} (hp : p ∈ interior (FlatSet f)) : period a p ∈ interior (FlatSet f) := by
  have hset := interior_flatSet_period_image (f := f) hf
  have : period a p ∈ period a '' interior (FlatSet f) := ⟨p, hp, rfl⟩
  simpa [hset] using this

/-- The inverse deck map is the roundtrip-inverse of the deck map on image
sets (plain functions, no homeomorphism coercion): for any set `S`,
`periodInv a '' (period a '' S) = S`. -/
lemma periodInv_image_period_image {a : ℝ} (S : Set ℝ²) :
    periodInv a '' (period a '' S) = S := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hxS, hx⟩
    have hz' : periodInv a z = x := by
      rw [← hx]
      exact periodInv_period a x
    rwa [hz']
  · intro hy
    have h1 : period a y ∈ period a '' S := ⟨y, hy, rfl⟩
    exact ⟨period a y, h1, periodInv_period a y⟩

/-- Membership in the flat-interior is preserved by the inverse deck map. -/
lemma mem_interior_FlatSet_periodInv {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} (hp : p ∈ interior (FlatSet f)) : periodInv a p ∈ interior (FlatSet f) := by
  have hset := interior_flatSet_period_image (f := f) hf
  -- p ∈ s and s = period '' s give p = period x with x ∈ s; then periodInv p = x ∈ s.
  have hpin : p ∈ period a '' interior (FlatSet f) := by
    rw [← hset] at hp
    exact hp
  rcases hpin with ⟨x, hxs, hx⟩
  have hpinv : periodInv a p = x := by
    rw [← hx]
    exact periodInv_period a x
  rwa [hpinv]

/-- **The deck map sends flat components onto flat components**:
`period a '' flatComponent f p = flatComponent f (period a p)`. -/
theorem flatComponent_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    period a '' flatComponent f p = flatComponent f (period a p) := by
  unfold flatComponent
  exact homeo_connectedComponentIn_eq_self (periodHomeo a)
    (interior_flatSet_period_image (f := f) hf) p hp

/-- **The inverse deck map sends flat components onto flat components**. -/
theorem flatComponent_periodInv_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    periodInv a '' flatComponent f p = flatComponent f (periodInv a p) := by
  have hp' : periodInv a p ∈ interior (FlatSet f) := mem_interior_FlatSet_periodInv hf hp
  have hdeck' := flatComponent_deck hf hp'
  -- hdeck' : period a '' flatComponent f (periodInv a p) = flatComponent f (period a (periodInv a p))
  have hpp : period a (periodInv a p) = p := period_periodInv a p
  rw [hpp] at hdeck'
  -- hdeck' : period a '' C₂ = C₁ where C₁ := flatComponent f p, C₂ := flatComponent f (periodInv a p)
  -- roundtrip by periodInv:
  have hrt := periodInv_image_period_image (a := a) (flatComponent f (periodInv a p))
  -- hrt : periodInv a '' (period a '' flatComponent f (periodInv a p)) = flatComponent f (periodInv a p)
  have hci : periodInv a '' (period a '' flatComponent f (periodInv a p)) =
      periodInv a '' flatComponent f p := by
    exact congrArg (fun T : Set ℝ² => periodInv a '' T) hdeck'
  rw [hrt] at hci
  exact hci.symm

/-- **Centreline specialisation**: the flat component at centreline height
`y + a` is the deck image of the component at height `y` (for a
flat-interior centreline point). -/
theorem flatComponent_centre_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {y : ℝ} (hy : IsFlatInterior f (centrePoint y)) :
    period a '' flatComponent f (centrePoint y) = flatComponent f (centrePoint (y + a)) := by
  have hp : centrePoint y ∈ interior (FlatSet f) :=
    (IsFlatInterior_iff_mem_interior_FlatSet (f := f) (centrePoint_mem_stripInterior y)).1 hy
  have hdeck := flatComponent_deck hf hp
  have hcp : period a (centrePoint y) = centrePoint (y + a) := (centrePoint_period a y).symm
  simpa [hcp] using hdeck

/-! ## Pure-geometry deck images of chords and between-regions -/

/-- Bijectivity of the period map on membership in an image set:
`x ∈ period a '' S` iff `periodInv a x ∈ S`. -/
lemma mem_period_image {a : ℝ} {S : Set ℝ²} {x : ℝ²} :
    x ∈ period a '' S ↔ periodInv a x ∈ S := by
  constructor
  · intro hx
    rcases hx with ⟨z, hz, hx⟩
    have hx' : periodInv a x = z := by
      rw [← hx]
      exact periodInv_period a z
    rwa [hx']
  · intro hx
    exact ⟨periodInv a x, hx, period_periodInv a x⟩

/-- Flip-reflection identity for the side-line heights: the height of the
flipped chord `(β+a, α+a)` at `u` equals the height of `(α,β)` at `1−u`
plus `a` (the deck map turns `x0` into `1−x0`). -/
lemma sideH_deck_flip (a α β u : ℝ) :
    sideH₁ (β + a) (α + a) u = sideH₁ α β (1 - u) + a := by
  dsimp [sideH₁]
  ring

/-- Flip-reflection identity at the chord endpoints. -/
lemma sideH_deck_flip' (a α β u : ℝ) :
    sideH₁ α β (1 - u) = sideH₁ (β + a) (α + a) u - a := by
  have h := sideH_deck_flip a α β u
  linarith

/-- The same flip identity for `sideH₂` (definitionally the same affine
formula as `sideH₁`, but a separate constant). -/
lemma sideH₂_deck_flip (a α β u : ℝ) :
    sideH₂ (β + a) (α + a) u = sideH₂ α β (1 - u) + a := by
  dsimp [sideH₂]
  ring

/-- Strip-interior membership is preserved by the deck reflection
`x ↦ (1−x0, x1−a)` (periodInv), in both directions. -/
lemma periodInv_stripInterior_iff {a : ℝ} {x : ℝ²} :
    periodInv a x ∈ stripInterior ↔ x ∈ stripInterior := by
  rw [stripInterior]
  dsimp [periodInv]
  constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]

/-- **The deck image of a strip chord**: `period a` sends the chord
`(0,α)→(1,β)` to the chord `(0,β+a)→(1,α+a)`. -/
theorem period_image_stripChord {a α β : ℝ} :
    period a '' stripChord α β = stripChord (β + a) (α + a) := by
  ext x
  rw [mem_period_image]
  rw [mem_stripChord, mem_stripChord]
  -- goal: periodInv x ∈ stripInt ∧ (periodInv x)1 = sideH₁ αβ ((periodInv x)0)
  --       ⟷ x ∈ stripInt ∧ x 1 = sideH₁ (β+a)(α+a) (x 0)
  constructor
  · intro hx
    have hxS : periodInv a x ∈ stripInterior := hx.1
    have hx1 : (periodInv a x) 1 = sideH₁ α β ((periodInv a x) 0) := hx.2
    constructor
    · exact (periodInv_stripInterior_iff.mp hxS)
    · have hside := sideH_deck_flip a α β (x 0)
      -- hside : sideH₁ (β+a)(α+a) (x0) = sideH₁ α β (1-x0) + a
      dsimp [periodInv] at hx1
      -- hx1 : x 1 - a = sideH₁ α β (1 - x 0)
      rw [hside]
      linarith
  · intro hx
    have hxS : x ∈ stripInterior := hx.1
    have hx1 : x 1 = sideH₁ (β + a) (α + a) (x 0) := hx.2
    constructor
    · exact (periodInv_stripInterior_iff.mpr hxS)
    · dsimp [periodInv]
      rw [sideH_deck_flip] at hx1
      linarith

/-- **The deck image of an open between-region**: `period a` sends
`betweenChord α₁β₁ α₂β₂` to `betweenChord (β₁+a,α₁+a) (β₂+a,α₂+a)`. -/
theorem period_image_betweenChord {a α₁ β₁ α₂ β₂ : ℝ} :
    period a '' betweenChord α₁ β₁ α₂ β₂ = betweenChord (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) := by
  ext x
  rw [mem_period_image]
  rw [mem_betweenChord, mem_betweenChord]
  constructor
  · intro hx
    have hxS : periodInv a x ∈ stripInterior := hx.1
    have hx1 : sideH₁ α₁ β₁ ((periodInv a x) 0) < (periodInv a x) 1 := hx.2.1
    have hx2 : (periodInv a x) 1 < sideH₁ α₂ β₂ ((periodInv a x) 0) := hx.2.2
    dsimp [periodInv] at hx1 hx2
    constructor
    · exact (periodInv_stripInterior_iff.mp hxS)
    · constructor
      · have hside := sideH_deck_flip a α₁ β₁ (x 0)
        rw [hside]
        linarith
      · have hside := sideH_deck_flip a α₂ β₂ (x 0)
        rw [hside]
        linarith
  · intro hx
    have hxS : x ∈ stripInterior := hx.1
    have hx1 : sideH₁ (β₁ + a) (α₁ + a) (x 0) < x 1 := hx.2.1
    have hx2 : x 1 < sideH₁ (β₂ + a) (α₂ + a) (x 0) := hx.2.2
    constructor
    · exact (periodInv_stripInterior_iff.mpr hxS)
    · have hx1' : sideH₁ α₁ β₁ (1 - x 0) < x 1 - a := by
        rw [sideH_deck_flip] at hx1
        linarith
      have hx2' : x 1 - a < sideH₁ α₂ β₂ (1 - x 0) := by
        rw [sideH_deck_flip] at hx2
        linarith
      constructor <;> dsimp [periodInv] <;> linarith

/-! ## Blend (leaf) deck: the flipped-data blend at height `y+a` -/

/-- The inverse side parameter is deck-covariant: the parameter of the
height `y+a` in the flipped data equals the parameter of `y` in the
original data. -/
lemma blendT_deck {a α₁ β₁ α₂ β₂ y : ℝ} :
    blendT (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) (y + a) = blendT α₁ β₁ α₂ β₂ y := by
  rw [blendT_eq_mulinv]
  rw [blendT_eq_mulinv]
  have h1 := sideH_deck_flip a α₁ β₁ (1 / 2)
  have h2 := sideH₂_deck_flip a α₂ β₂ (1 / 2)
  have hnum : (y + a) - sideH₁ (β₁ + a) (α₁ + a) (1 / 2) = y - sideH₁ α₁ β₁ (1 / 2) := by
    rw [h1]
    ring
  have hden : sideH₂ (β₂ + a) (α₂ + a) (1 / 2) - sideH₁ (β₁ + a) (α₁ + a) (1 / 2) =
      sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2) := by
    rw [h2, h1]
    ring
  rw [hnum, hden]

/-- **The deck map sends the blended leaf to the blended leaf of the
flipped data**: `period a (genP t u) = genP (flipped) t (1−u)` — the leaf
through the centreline height `y+a` is the period image of the leaf
through `y` (segment parameter reflected by the seam swap). -/
lemma period_deck_genP {a α₁ β₁ α₂ β₂ t u : ℝ} :
    period a (genP α₁ β₁ α₂ β₂ t u) =
      genP (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) t (1 - u) := by
  ext i <;> fin_cases i
  · simp [period, genP]
  · dsimp [period, genP]
    have h1 := sideH_deck_flip a α₁ β₁ u
    have h2 := sideH_deck_flip a α₂ β₂ u
    have h1' : sideH₁ (β₁ + a) (α₁ + a) (1 - u) = sideH₁ α₁ β₁ u + a := by
      have hh := sideH_deck_flip a α₁ β₁ (1 - u)
      rw [hh]
      congr 1
      ring
    have h2' : sideH₂ (β₂ + a) (α₂ + a) (1 - u) = sideH₂ α₂ β₂ u + a := by
      have hh := sideH₂_deck_flip a α₂ β₂ (1 - u)
      rw [hh]
      congr 1
      ring
    -- LHS second coordinate: (1-t) sideH₁ αβ u + t sideH₂ αβ u + a
    -- RHS: (1-t) sideH₁ flip (1-u) + t sideH₂ flip (1-u)
    rw [h1', h2']
    ring

/-- **Left-endpoint deck**: the left endpoint height of the flipped blend
at `y+a` equals the right endpoint height of the original blend at `y`
plus `a`. -/
lemma blendA1_deck {a α₁ β₁ α₂ β₂ y : ℝ} :
    (genA (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a)
        (blendT (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) (y + a))) 1 =
      (genB α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 1 + a := by
  rw [blendA1_formula, blendB1_formula, blendT_deck]
  dsimp [blendT] at *
  ring

/-- **Right-endpoint deck**: the right endpoint height of the flipped
blend at `y+a` equals the left endpoint height of the original blend at
`y` plus `a`. -/
lemma blendB1_deck {a α₁ β₁ α₂ β₂ y : ℝ} :
    (genB (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a)
        (blendT (β₁ + a) (α₁ + a) (β₂ + a) (α₂ + a) (y + a))) 1 =
      (genA α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 1 + a := by
  rw [blendB1_formula, blendA1_formula, blendT_deck]
  dsimp [blendT] at *
  ring

end Submission.PaperBand

