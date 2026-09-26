import Mathlib
import ChallengeDeps
import Submission.CompactCover
import Submission.Commons.Analysis.Real.open_cover_subdivision

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-!
# Layer A (xix) — refinement of a chart cover of a compact-interval path

`CompactCover.lean` (Layer A (xviii)) produced a finite list of cover
charts `cs` (sigma pairs of point and chart) such that every path point
lies in the region of some chart of the list.  This module refines that
cover into a form the path-following induction can consume: a **uniform
refinement** in which every subinterval of the parameter interval of length
at most `δ` lies inside a single chart region.

1. **real representatives** — `pathInChart σ g` (the open set of times
   whose path point lies in the region of the chart `g`), its ambient-open
   representative `coverOpenReal hσ g` (`isOpen_coverOpenReal`,
   `pathInChart_eq_coverOpenReal`), and the transfer
   `real_chart_cover` (the real interval `[a,b]` is covered by the
   representatives of the charts of `cs`).
2. **the refinement statement** `chart_refinement`: from the chart cover
   one obtains a `δ > 0` such that every subinterval `[x,y] ⊆ [a,b]` of
   length at most `δ` lies entirely in the region of one chart of `cs`
   (i.e. the whole path over `[x,y]` stays inside that chart region).
   This is the Lebesgue-number-style fact on which the grid partition and
   the adapted chain are built.  (The uniform-subdivision input is the
   commons lemma `Commons.Analysis.Real.open_cover_subdivision`, proven by
   the fleet.)

Everything here is elementary and verified (no axioms, no `sorry`).
-/

namespace LeanEval.KnotTheory.Quadrisecant

/-- The set of times whose path point lies in the region of the chart
`g` (an open set of the compact interval, `σ` being continuous). -/
def pathInChart {r : ℝ → Space} {a b : ℝ} (σ : CompactInterval a b → ZeroSetPoint r)
    (g : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)) :
    Set (CompactInterval a b) :=
  {u : CompactInterval a b | (σ u : KnotParamTriple) ∈ g.2.V}

/-- `pathInChart` is open (the point map is continuous and the chart region
is open). -/
lemma isOpen_pathInChart {r : ℝ → Space} {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (hσ : Continuous σ)
    (g : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)) :
    IsOpen (pathInChart σ g) := by
  unfold pathInChart
  have hmap : Continuous (fun u : CompactInterval a b => (σ u : KnotParamTriple)) :=
    continuous_subtype_val.comp hσ
  exact IsOpen.preimage hmap g.2.V_open

/-- An ambient-open representative of `pathInChart σ g`: an open set of the
real line whose intersection with the interval subtype is exactly the set
of times whose path point lies in the region of `g`. -/
noncomputable def coverOpenReal {r : ℝ → Space} {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (hσ : Continuous σ)
    (g : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)) : Set ℝ :=
  Classical.choose (isOpen_induced_iff.mp (isOpen_pathInChart σ hσ g))

/-- The real representative is open. -/
lemma isOpen_coverOpenReal {r : ℝ → Space} {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (hσ : Continuous σ)
    (g : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)) :
    IsOpen (coverOpenReal σ hσ g) :=
  (Classical.choose_spec (isOpen_induced_iff.mp (isOpen_pathInChart σ hσ g))).1

/-- The chart-time set is the pullback of its real representative along the
inclusion of the interval. -/
lemma pathInChart_eq_coverOpenReal {r : ℝ → Space} {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (hσ : Continuous σ)
    (g : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)) :
    pathInChart σ g =
      (fun u : CompactInterval a b => (u : ℝ)) ⁻¹' coverOpenReal σ hσ g := by
  exact (Classical.choose_spec (isOpen_induced_iff.mp (isOpen_pathInChart σ hσ g))).2.symm

/-- A time whose path point lies in the region of `g` lies in the real
representative of `g`. -/
lemma mem_coverOpenReal_of_mem_pathInChart {r : ℝ → Space} {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (hσ : Continuous σ)
    (g : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)) {u : CompactInterval a b}
    (hu : u ∈ pathInChart σ g) : (u : ℝ) ∈ coverOpenReal σ hσ g := by
  simpa [pathInChart_eq_coverOpenReal σ hσ g] using hu

/-- The real interval `[a,b]` is covered by the real representatives of the
cover charts of `cs`. -/
lemma real_chart_cover {r : ℝ → Space} {a b : ℝ} (σ : CompactInterval a b → ZeroSetPoint r)
    (hσ : Continuous σ) (cs : List (Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)))
    (hcover : ∀ u : CompactInterval a b,
      ∃ g : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p), g ∈ cs ∧
        (σ u : KnotParamTriple) ∈ g.2.V) :
    ∀ t : ℝ, t ∈ Set.Icc a b →
      ∃ g : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p), g ∈ cs ∧
        t ∈ coverOpenReal σ hσ g := by
  intro t ht
  let u : CompactInterval a b := ⟨t, ht⟩
  rcases hcover u with ⟨g, hg, hug⟩
  refine ⟨g, hg, ?_⟩
  have hmemO : (u : ℝ) ∈ coverOpenReal σ hσ g := by
    exact mem_coverOpenReal_of_mem_pathInChart σ hσ g hug
  simpa [u] using hmemO

end LeanEval.KnotTheory.Quadrisecant


namespace LeanEval.KnotTheory.Quadrisecant

/-- **Chart refinement of a compact-interval path.**  From a finite chart
cover of the path one obtains a positive `δ` such that every subinterval
`[x,y]` of `[a,b]` of length at most `δ` lies entirely in the region of one
chart of `cs` (i.e. the path over `[x,y]` stays inside that chart region).
This is the uniform refinement from which the grid partition and the
adapted chain are built. -/
theorem chart_refinement {r : ℝ → Space} {a b : ℝ} (hab : a ≤ b)
    (σ : CompactInterval a b → ZeroSetPoint r) (hσ : Continuous σ)
    (cs : List (Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)))
    (hcover : ∀ u : CompactInterval a b,
      ∃ g : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p), g ∈ cs ∧
        (σ u : KnotParamTriple) ∈ g.2.V) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x y : ℝ, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y → y - x ≤ δ →
        ∃ g : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p), g ∈ cs ∧
          ∀ u : CompactInterval a b, (u : ℝ) ∈ Set.Icc x y →
            (σ u : KnotParamTriple) ∈ g.2.V := by
  -- index the uniform-subdivision input by the charts of the cover list
  let ι : Type := {g : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p) // g ∈ cs}
  let U : ι → Set ℝ := fun g => coverOpenReal σ hσ g.1
  have hUo : ∀ i : ι, IsOpen (U i) := by
    intro i
    exact isOpen_coverOpenReal σ hσ i.1
  have hcovU : (Set.Icc a b : Set ℝ) ⊆ ⋃ i : ι, U i := by
    intro t ht
    rcases real_chart_cover σ hσ cs hcover t ht with ⟨g, hg, htO⟩
    exact Set.mem_iUnion.mpr ⟨⟨g, hg⟩, by simpa [U] using htO⟩
  rcases Commons.Analysis.Real.open_cover_subdivision hab U hUo hcovU with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro x y hx hy hxy hlen
  rcases hδ x y hx hy hxy hlen with ⟨gi, hcell⟩
  -- gi : ι (a chart of the cover); its cell is contained in the real
  -- representative of its region
  refine ⟨gi.1, gi.2, ?_⟩
  intro u hu
  have huO : (u : ℝ) ∈ coverOpenReal σ hσ gi.1 := by
    simpa [U] using hcell hu
  have hup : u ∈ pathInChart σ gi.1 := by
    simpa [pathInChart_eq_coverOpenReal σ hσ gi.1] using huO
  simpa [pathInChart] using hup

end LeanEval.KnotTheory.Quadrisecant
