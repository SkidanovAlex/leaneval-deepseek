import Submission.Work.CentrelineUBends
import Submission.Work.FlatComponents

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Flat-centreline heights: sets, deck invariance, chord pre-bend facts (GREEN)

The centreline `(1/2, y)` splits into the `U`-heights
(`UHeight`, `dN ≠ 0`, leaves = canonical U-bends of `CentrelineUBends`) and
the **flat heights** (`FlatHeight`, `dN = 0`, leaves = chords of the flat
components).  This file records the flat-side facts provable WITHOUT the
still-open trapezoid-frontier analysis:

* `FlatHeight` and its deck invariance under `y ↦ y+a` (from
  `dN_zero_period_iff` + `centrePoint_period`);
* the centreline trichotomy `UHeight = FlatHeightᶜ`;
* flat-interior centreline points lie in their flat component;
* **`flatChord_image_isometric`**: any straight chord of a flat component
  is an image-isometric pre-bend — `‖f (x₀+Bv) − f (x₀+Av)‖ = ‖Bv−Av‖`
  (from `flatComponent_chord_is_prebend`'s affine line formula), so the
  `BendArcFacts` free relations (1),(2),(3) of Lemma G apply verbatim to
  the eventual flat leaves.

OPEN (the genuine research bottleneck of the middle, documented in
`session_status39`): the canonical flat-leaf through a flat centreline
point — a chord of its flat component running from boundary line to
boundary line in the component's ruling direction — needs the flat-component
TRAPEZOID structure (frontier toward `U` consists of two parallel U-bend
chords), whose frontier-straightness analysis is still open.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- The set of centreline heights whose centreline point is FLAT
(`dN = 0`): the centreline portion of the flat set. -/
def FlatHeight (a : ℝ) (f : ℝ² → ℝ³) : Set ℝ := {y : ℝ | dN f (centrePoint y) = 0}

/-- Membership in `FlatHeight` means the centreline point is flat. -/
lemma mem_FlatHeight {a : ℝ} {f : ℝ² → ℝ³} {y : ℝ} :
    y ∈ FlatHeight a f ↔ dN f (centrePoint y) = 0 := by
  rfl

/-- A flat height iff the centreline point lies in the flat set
(`FlatSet`; the strip-interior membership that `FlatSet` requires is
automatic for centreline points). -/
lemma mem_FlatHeight_iff_FlatSet {a : ℝ} {f : ℝ² → ℝ³} {y : ℝ} :
    y ∈ FlatHeight a f ↔ centrePoint y ∈ Submission.PaperBand.FlatSet f := by
  rw [mem_FlatHeight]
  rw [Submission.PaperBand.mem_FlatSet]
  constructor
  · intro hy
    exact ⟨centrePoint_mem_stripInterior y, hy⟩
  · intro hy
    exact hy.2

/-- **Centreline trichotomy**: a height is a `U`-height iff it is NOT a
flat height. -/
lemma mem_UHeight_iff_not_FlatHeight {a : ℝ} {f : ℝ² → ℝ³} {y : ℝ} :
    y ∈ UHeight a f ↔ y ∉ FlatHeight a f := by
  rfl

/-- **Flat heights are deck-invariant**: `y+a` is flat iff `y` is (the
shape operator vanishes at `period x` iff at `x`). -/
lemma mem_FlatHeight_add_period {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (y : ℝ) : y + a ∈ FlatHeight a f ↔ y ∈ FlatHeight a f := by
  rw [mem_FlatHeight, mem_FlatHeight]
  rw [centrePoint_period a y]
  exact dN_zero_period_iff hf (centrePoint_mem_stripInterior y)

/-- A FLAT-INTERIOR centreline point lies in its own flat component. -/
lemma mem_flatComponent_of_flatInterior_centre {a : ℝ} {f : ℝ² → ℝ³}
    {y : ℝ} (hfi : IsFlatInterior f (centrePoint y)) :
    centrePoint y ∈ flatComponent f (centrePoint y) := by
  exact mem_flatComponent (f := f) (p := centrePoint y)
    ((IsFlatInterior_iff_mem_interior_FlatSet (f := f) (centrePoint_mem_stripInterior y)).1 hfi)

/-- **Straight chords of a flat component are image-isometric**: for a
segment `{x₀ + t•v | t ∈ Icc A B}` (`A ≤ B`) inside a flat component, the
image chord has the preimage length
`‖f (x₀+Bv) − f (x₀+Av)‖ = ‖(x₀+Bv) − (x₀+Av)‖` (`= |B−A|·‖v‖`).  This is
the `BendArcFacts` isometric-image hypothesis for flat chords, so the free
relations (1),(2),(3) of Lemma G hold for the eventual flat leaves too. -/
lemma flatChord_image_isometric {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p x₀ : ℝ²} (hx₀ : x₀ ∈ flatComponent f p) {v : ℝ²} {A B : ℝ}
    (hAB : A ≤ B)
    (hseg : ∀ t ∈ Set.Icc A B, x₀ + t • v ∈ flatComponent f p) :
    ‖f (x₀ + B • v) - f (x₀ + A • v)‖ = ‖(x₀ + B • v) - (x₀ + A • v)‖ := by
  have hpre := flatComponent_chord_is_prebend hf hx₀ (A := A) (B := B) hseg
  have hxA : A ∈ Set.Icc A B := (Set.mem_Icc).2 ⟨le_rfl, hAB⟩
  have hxB : B ∈ Set.Icc A B := (Set.mem_Icc).2 ⟨hAB, le_rfl⟩
  have hAaff := hpre.2.1 A hxA
  have hBaff := hpre.2.1 B hxB
  -- hAaff : f (x₀ + A•v) = f x₀ + A•c ; hBaff likewise, c := fderiv ℝ f x₀ v
  let c : ℝ³ := fderiv ℝ f x₀ v
  have himg : f (x₀ + B • v) - f (x₀ + A • v) = (B - A) • c := by
    rw [hBaff, hAaff]
    calc
      (f x₀ + B • c) - (f x₀ + A • c) = B • c - A • c := by abel
      _ = (B - A) • c := by rw [← sub_smul]
  have hpreimg : (x₀ + B • v) - (x₀ + A • v) = (B - A) • v := by
    calc
      (x₀ + B • v) - (x₀ + A • v) = B • v - A • v := by abel
      _ = (B - A) • v := by rw [← sub_smul]
  have hx₀S : x₀ ∈ stripInterior := flatComponent_subset_stripInterior f p hx₀
  have hnc : ‖c‖ = ‖v‖ := by
    dsimp [c]
    exact fderiv_norm_eq_interior hf x₀ hx₀S v
  rw [himg, hpreimg]
  calc
    ‖(B - A) • c‖ = |B - A| * ‖c‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ = |B - A| * ‖v‖ := by rw [hnc]
    _ = ‖(B - A) • v‖ := by
      rw [norm_smul, Real.norm_eq_abs]

end Submission
