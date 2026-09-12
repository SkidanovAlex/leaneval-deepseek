import Submission.Work.UHeightAccum
import Submission.Work.ComponentLeaves
import Submission.Work.FlatBetweenFrontier
import Submission.Work.FlatComponents

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Brick (B) of the degenerate-flat-height route: the component dichotomy

GREEN — brick (B) is COMPLETE (both sides).  At a degenerate flat height
`y₀` (flat, non-flat-interior) which is NOT COVERED by any flat component's
closed centre interval (`CoveredHeight f y₀` := `∃ p ∈ interior(FlatSet f),
y₀ ∈ frHeights f p`), U-heights accumulate on BOTH sides of `y₀`:

* `section_iff_of_between` — component centreline membership ⟺ height in
  `(h₁,h₂)` for the canonical `flatComponent_between_with_data` heights;
* `flatInterior_of_no_uHeight_band` (+ `_above`) — no U-height in
  `(y₀−ε,y₀)` (resp. `(y₀,y₀+ε)`) ⟹ the inner band is flat-interior;
* `covered_of_flatInterior_band` (+ `_above`) — that ⟹ `y₀` is a frontier
  height of some component (the dichotomy, via
  `flatComponent_frontier_not_flat_interior`);
* **`uHeight_accumulate_below/above_of_uncovered_degenerate`** — the brick
  (B) conclusions: U-heights accumulate on both sides of every uncovered
  degenerate flat height.

Next (bricks (C),(D) of session_status105): with both-sides U-sequences
`yₙ → y₀`, show the leaf slopes converge (FrontierCluster +
`uBend_abs_disp_bound`) to a two-sided limit `m₀`, and define the
degenerate leaf as the chord through `(1/2,y₀)` of slope `m₀` with
centre/preBend/continuity/deck.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

def CoveredHeight {f : ℝ² → ℝ³} (y : ℝ) : Prop :=
  ∃ p : ℝ², p ∈ interior (FlatSet f) ∧ y ∈ frHeights f p


/-- section membership helper (as before). -/
lemma section_iff_of_between {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2)
    (y : ℝ) :
    (!₂[(1 / 2 : ℝ), y] : ℝ²) ∈ flatComponent f p ↔ y ∈ Set.Ioo h₁ h₂ := by
  have hord : ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 u <
      sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 u :=
    sideH₁_lt_of_heights hf ha p hp hh₁ hh₂ hlt
  have hinterval : {y : ℝ | (!₂[(1 / 2 : ℝ), y] : ℝ²) ∈ betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2} =
      Set.Ioo (sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 (1 / 2))
               (sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 (1 / 2)) :=
    centreline_of_between hord
  have hh₁' : sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 (1 / 2) = h₁ :=
    sideH₁_data_half hf ha p hp hh₁
  have hh₂' : sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 (1 / 2) = h₂ :=
    sideH₁_data_half hf ha p hp hh₂
  rw [hC]
  have hset : ({y : ℝ | (!₂[(1 / 2 : ℝ), y] : ℝ²) ∈
      betweenChord (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
                   (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2} : Set ℝ) =
      Set.Ioo h₁ h₂ := by
    rw [hinterval]
    rw [hh₁', hh₂']
  rw [← hset]
  rfl

theorem covered_of_flatInterior_band {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ ε : ℝ} (hε : 0 < ε)
    (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hfi : ∀ y : ℝ, y ∈ Set.Ioo (y₀ - ε / 2) y₀ → IsFlatInterior f (centrePoint y)) :
    ∃ p : ℝ², p ∈ interior (FlatSet f) ∧ y₀ ∈ frHeights f p := by
  let y₁ : ℝ := y₀ - ε / 4
  have hy₁I : y₁ ∈ Set.Ioo (y₀ - ε / 2) y₀ := by
    dsimp [y₁]
    rw [Set.mem_Ioo]
    constructor <;> linarith
  have hy₁fi : IsFlatInterior f (centrePoint y₁) := hfi y₁ hy₁I
  let p : ℝ² := centrePoint y₁
  have hp : p ∈ interior (FlatSet f) :=
    (IsFlatInterior_iff_mem_interior_FlatSet (f := f) (centrePoint_mem_stripInterior y₁)).mp hy₁fi
  rcases flatComponent_between_with_data hf ha hp with ⟨h₁, h₂, hh₁, hh₂, hlt, hC⟩
  have hy₁C : (!₂[(1 / 2 : ℝ), y₁] : ℝ²) ∈ flatComponent f p := by
    dsimp [p]
    exact mem_flatComponent hp
  have hy₁I' : y₁ ∈ Set.Ioo h₁ h₂ :=
    (section_iff_of_between hf ha hp hh₁ hh₂ hlt hC y₁).mp hy₁C
  rw [Set.mem_Ioo] at hy₁I hy₁I'
  -- case analysis on h₂ vs y₀
  have h₂eq : h₂ = y₀ := by
    have h₂le : h₂ ≤ y₀ := by
      by_contra hybig
      have hy₀lt : y₀ < h₂ := lt_of_not_ge hybig
      -- (1/2,y₀) ∈ section (h₁,h₂) ⊆ component
      have hy₀I : y₀ ∈ Set.Ioo h₁ h₂ := by
        rw [Set.mem_Ioo]
        constructor
        · nlinarith [hy₁I'.1, hy₁I'.2]
        · exact hy₀lt
      have hy₀C : (!₂[(1 / 2 : ℝ), y₀] : ℝ²) ∈ flatComponent f p :=
        (section_iff_of_between hf ha hp hh₁ hh₂ hlt hC y₀).mpr hy₀I
      have hy₀int : (!₂[(1 / 2 : ℝ), y₀] : ℝ²) ∈ interior (FlatSet f) :=
        flatComponent_subset_flatInterior f p hy₀C
      have hy₀fi : IsFlatInterior f (centrePoint y₀) :=
        (IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior y₀)).mpr hy₀int
      exact hni hy₀fi
    have h₂ge : y₀ ≤ h₂ := by
      by_contra hybig
      have h₂lt : h₂ < y₀ := lt_of_not_ge hybig
      -- h₂ ∈ band (y₀−ε/2, y₀): flat-interior, but h₂ is a frontier height
      have h₂I : h₂ ∈ Set.Ioo (y₀ - ε / 2) y₀ := by
        rw [Set.mem_Ioo]
        constructor
        · linarith [hy₁I.1, hy₁I'.2]
        · exact h₂lt
      have h₂fi : IsFlatInterior f (centrePoint h₂) := hfi h₂ h₂I
      -- (1/2,h₂) ∈ frontier (flatComponent f p)
      let cd₁ : ℝ × ℝ := frCompData hf ha p hp h₁ hh₁
      let cd₂ : ℝ × ℝ := frCompData hf ha p hp h₂ hh₂
      have hord : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ cd₁.1 cd₁.2 u < sideH₁ cd₂.1 cd₂.2 u := by
        intro u hu
        simpa [cd₁, cd₂] using (sideH₁_lt_of_heights hf ha p hp hh₁ hh₂ hlt u hu)
      have hhalf₂ : sideH₁ cd₂.1 cd₂.2 (1 / 2) = h₂ := by
        simpa [cd₂] using (sideH₁_data_half hf ha p hp hh₂)
      have hq₂ch : (!₂[(1 / 2 : ℝ), h₂] : ℝ²) ∈ stripChord cd₂.1 cd₂.2 := by
        rw [mem_stripChord]
        constructor
        · simpa [centrePoint] using (centrePoint_mem_stripInterior h₂)
        · exact hhalf₂.symm
      have hq₂S : (!₂[(1 / 2 : ℝ), h₂] : ℝ²) ∈ stripInterior :=
        (mem_stripChord.mp hq₂ch).1
      have hq₂Fb : (!₂[(1 / 2 : ℝ), h₂] : ℝ²) ∈ frontier (betweenChord cd₁.1 cd₁.2 cd₂.1 cd₂.2) := by
        have hfr := frontier_betweenChord (α₁ := cd₁.1) (β₁ := cd₁.2) (α₂ := cd₂.1) (β₂ := cd₂.2) hord
        have hmem : (!₂[(1 / 2 : ℝ), h₂] : ℝ²) ∈
            frontier (betweenChord cd₁.1 cd₁.2 cd₂.1 cd₂.2) ∩ stripInterior := by
          rw [hfr]
          exact Or.inr hq₂ch
        exact hmem.1
      have hq₂F : (!₂[(1 / 2 : ℝ), h₂] : ℝ²) ∈ frontier (flatComponent f p) := by
        rw [hC]
        simpa [cd₁, cd₂] using hq₂Fb
      have hq₂ni : ¬ IsFlatInterior f (!₂[(1 / 2 : ℝ), h₂] : ℝ²) :=
        flatComponent_frontier_not_flat_interior (f := f) (p := p) hq₂S hq₂F
      exact hq₂ni (by simpa [centrePoint] using h₂fi)
    exact le_antisymm h₂le h₂ge
  refine ⟨p, hp, ?_⟩
  rw [← h₂eq]
  exact hh₂

/-- **Brick (B), below accumulation**: for `y₀` a flat height whose
centreline point is NOT flat-interior and which is NOT covered by any flat
component, U-heights accumulate BELOW `y₀`.  Contraposition: if no
U-height occurred in `(y₀−ε, y₀)`, then
`flatInterior_of_no_uHeight_band` makes all of `(y₀−ε/2, y₀)` flat-interior
and the dichotomy `covered_of_flatInterior_band` covers `y₀`. -/
theorem uHeight_accumulate_below_of_uncovered_degenerate {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ}
    (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    ∀ ε > 0, ∃ u : ℝ, u ∈ UHeight a f ∧ u ∈ Set.Ioo (y₀ - ε) y₀ := by
  intro ε hε
  by_contra hnone
  have hnoU : ∀ u : ℝ, u ∈ Set.Ioo (y₀ - ε) y₀ → u ∉ UHeight a f := by
    intro u hu huU
    exact hnone ⟨u, huU, hu⟩
  have hfi := flatInterior_of_no_uHeight_band hf ha (y₀ := y₀) (ε := ε) hε hnoU
  rcases covered_of_flatInterior_band hf ha (y₀ := y₀) (ε := ε) hε hni hfi with ⟨p, hp, hh⟩
  exact hunc ⟨p, hp, hh⟩

theorem flatInterior_of_no_uHeight_band_above {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ ε : ℝ} (hε : 0 < ε)
    (hnoU : ∀ u : ℝ, u ∈ Set.Ioo y₀ (y₀ + ε) → u ∉ UHeight a f) :
    ∀ y : ℝ, y ∈ Set.Ioo y₀ (y₀ + ε / 2) → IsFlatInterior f (centrePoint y) := by
  intro y hy
  have hyU : y ∉ UHeight a f := by
    apply hnoU
    rw [Set.mem_Ioo] at hy ⊢
    constructor <;> nlinarith [hy.1, hy.2, hε]
  have hyF : y ∈ FlatHeight a f := by
    by_contra h
    exact hyU ((mem_UHeight_iff_not_FlatHeight (a := a) (f := f)).mpr h)
  by_contra hni
  let ρ : ℝ := min (y - y₀) ((y₀ + ε - y) / 2)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    apply lt_min
    · nlinarith [hy.1]
    · nlinarith [hε, hy.2]
  rcases exists_uHeight_near_degenerate_flat hf ha hyF hni ρ hρ with ⟨u, huU, huρ⟩
  have huI : u ∈ Set.Ioo y₀ (y₀ + ε) := by
    rw [Set.mem_Ioo]
    have huρ' := abs_lt.mp huρ
    constructor
    · have h1 : ρ ≤ y - y₀ := by dsimp [ρ]; exact min_le_left _ _
      nlinarith
    · have h2 : ρ ≤ (y₀ + ε - y) / 2 := by dsimp [ρ]; exact min_le_right _ _
      nlinarith
  exact (hnoU u huI) huU

/-- Mirror dichotomy (above): if all centre points of the inner band
`(y₀, y₀+ε/2)` are flat-interior while `y₀` is flat non-interior, then
`y₀` is a frontier height of some component (its LOWER frontier). -/

theorem covered_of_flatInterior_band_above {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ ε : ℝ} (hε : 0 < ε)
    (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hfi : ∀ y : ℝ, y ∈ Set.Ioo y₀ (y₀ + ε / 2) → IsFlatInterior f (centrePoint y)) :
    ∃ p : ℝ², p ∈ interior (FlatSet f) ∧ y₀ ∈ frHeights f p := by
  let y₁ : ℝ := y₀ + ε / 4
  have hy₁I : y₁ ∈ Set.Ioo y₀ (y₀ + ε / 2) := by
    dsimp [y₁]
    rw [Set.mem_Ioo]
    constructor <;> linarith
  have hy₁fi : IsFlatInterior f (centrePoint y₁) := hfi y₁ hy₁I
  let p : ℝ² := centrePoint y₁
  have hp : p ∈ interior (FlatSet f) :=
    (IsFlatInterior_iff_mem_interior_FlatSet (f := f) (centrePoint_mem_stripInterior y₁)).mp hy₁fi
  rcases flatComponent_between_with_data hf ha hp with ⟨h₁, h₂, hh₁, hh₂, hlt, hC⟩
  have hy₁C : (!₂[(1 / 2 : ℝ), y₁] : ℝ²) ∈ flatComponent f p := by
    dsimp [p]
    exact mem_flatComponent hp
  have hy₁I' : y₁ ∈ Set.Ioo h₁ h₂ :=
    (section_iff_of_between hf ha hp hh₁ hh₂ hlt hC y₁).mp hy₁C
  rw [Set.mem_Ioo] at hy₁I hy₁I'
  have h₁eq : h₁ = y₀ := by
    have h₁le : h₁ ≤ y₀ := by
      by_contra hybig
      have h₁gt : y₀ < h₁ := lt_of_not_ge hybig
      -- h₁ ∈ band (y₀, y₀+ε/2): flat-interior, but (1/2,h₁) is on the lower
      -- frontier chord of the component, hence NOT flat-interior
      have h₁I : h₁ ∈ Set.Ioo y₀ (y₀ + ε / 2) := by
        rw [Set.mem_Ioo]
        constructor
        · exact h₁gt
        · linarith [hy₁I'.1, hy₁I.2]
      have h₁fi : IsFlatInterior f (centrePoint h₁) := hfi h₁ h₁I
      let cd₁ : ℝ × ℝ := frCompData hf ha p hp h₁ hh₁
      let cd₂ : ℝ × ℝ := frCompData hf ha p hp h₂ hh₂
      have hord : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ cd₁.1 cd₁.2 u < sideH₁ cd₂.1 cd₂.2 u := by
        intro u hu
        simpa [cd₁, cd₂] using (sideH₁_lt_of_heights hf ha p hp hh₁ hh₂ hlt u hu)
      have hhalf₁ : sideH₁ cd₁.1 cd₁.2 (1 / 2) = h₁ := by
        simpa [cd₁] using (sideH₁_data_half hf ha p hp hh₁)
      have hq₁ch : (!₂[(1 / 2 : ℝ), h₁] : ℝ²) ∈ stripChord cd₁.1 cd₁.2 := by
        rw [mem_stripChord]
        constructor
        · simpa [centrePoint] using (centrePoint_mem_stripInterior h₁)
        · exact hhalf₁.symm
      have hq₁S : (!₂[(1 / 2 : ℝ), h₁] : ℝ²) ∈ stripInterior :=
        (mem_stripChord.mp hq₁ch).1
      have hq₁Fb : (!₂[(1 / 2 : ℝ), h₁] : ℝ²) ∈ frontier (betweenChord cd₁.1 cd₁.2 cd₂.1 cd₂.2) := by
        have hfr := frontier_betweenChord (α₁ := cd₁.1) (β₁ := cd₁.2) (α₂ := cd₂.1) (β₂ := cd₂.2) hord
        have hmem : (!₂[(1 / 2 : ℝ), h₁] : ℝ²) ∈
            frontier (betweenChord cd₁.1 cd₁.2 cd₂.1 cd₂.2) ∩ stripInterior := by
          rw [hfr]
          exact Or.inl hq₁ch
        exact hmem.1
      have hq₁F : (!₂[(1 / 2 : ℝ), h₁] : ℝ²) ∈ frontier (flatComponent f p) := by
        rw [hC]
        simpa [cd₁, cd₂] using hq₁Fb
      have hq₁ni : ¬ IsFlatInterior f (!₂[(1 / 2 : ℝ), h₁] : ℝ²) :=
        flatComponent_frontier_not_flat_interior (f := f) (p := p) hq₁S hq₁F
      exact hq₁ni (by simpa [centrePoint] using h₁fi)
    have h₁ge : y₀ ≤ h₁ := by
      by_contra hybig
      have h₁lt : h₁ < y₀ := lt_of_not_ge hybig
      -- y₀ lies strictly inside the section (h₁,h₂)
      have hy₀I : y₀ ∈ Set.Ioo h₁ h₂ := by
        rw [Set.mem_Ioo]
        constructor
        · exact h₁lt
        · nlinarith [hy₁I.1, hy₁I'.2]
      have hy₀C : (!₂[(1 / 2 : ℝ), y₀] : ℝ²) ∈ flatComponent f p :=
        (section_iff_of_between hf ha hp hh₁ hh₂ hlt hC y₀).mpr hy₀I
      have hy₀int : (!₂[(1 / 2 : ℝ), y₀] : ℝ²) ∈ interior (FlatSet f) :=
        flatComponent_subset_flatInterior f p hy₀C
      have hy₀fi : IsFlatInterior f (centrePoint y₀) :=
        (IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior y₀)).mpr hy₀int
      exact hni hy₀fi
    exact le_antisymm h₁le h₁ge
  refine ⟨p, hp, ?_⟩
  rw [← h₁eq]
  exact hh₁

theorem uHeight_accumulate_above_of_uncovered_degenerate {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ}
    (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    ∀ ε > 0, ∃ u : ℝ, u ∈ UHeight a f ∧ u ∈ Set.Ioo y₀ (y₀ + ε) := by
  intro ε hε
  by_contra hnone
  have hnoU : ∀ u : ℝ, u ∈ Set.Ioo y₀ (y₀ + ε) → u ∉ UHeight a f := by
    intro u hu huU
    exact hnone ⟨u, huU, hu⟩
  have hfi := flatInterior_of_no_uHeight_band_above hf ha (y₀ := y₀) (ε := ε) hε hnoU
  rcases covered_of_flatInterior_band_above hf ha (y₀ := y₀) (ε := ε) hε hni hfi with ⟨p, hp, hh⟩
  exact hunc ⟨p, hp, hh⟩
end Submission
