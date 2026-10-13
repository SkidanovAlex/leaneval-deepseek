/-
  WilE7 (`Work.WilE7.BandAux.bandCompTwo_defs`): the sheet partition of the two-strata band.

  This is the two-strata analogue of the partition `bandSheetPart` of
  `Work.WilE7.BandAux.bandComponent`.  Given two strata `S₁ S₂`, two families of sheets
  `s₁ : Fin k₁ → C → ℝ^{m+1}` and `s₂ : Fin k₂ → C → ℝ^{m+1}` and a set `G` of ambient points of
  the two-strata band `bandS3two Z S₁ S₂`, the part indexed by `(i, j) : Fin k₁ × Fin k₂` is the
  set of points of `G` whose second block lies on the sheet `s₁ i` and whose fourth block lies on
  the sheet `s₂ j`.
-/
import Mathlib
import Submission.Work.WilE7.BandAux.BandDefsTwo
import Submission.Work.WilE7.BandAux.bandComponent

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.BandAux
open Work.WilE7 WilkiesDesign WilkiesDesign.E

/-- The part of `G` whose second block lies on the sheet `s₁ i` and whose fourth block lies on
the sheet `s₂ j`. -/
def bandSheetPartTwo {p m k₁ k₂ : ℕ}
    (s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (G : Set (Fin (bandDim p m) → ℝ)) (ij : Fin k₁ × Fin k₂) : Set G :=
  {w : G | bandZ2 w.1 = Fin.append (bandBase w.1) (s₁ ij.1 (bandBase w.1)) ∧
    bandZ2' w.1 = Fin.append (bandBase w.1) (s₂ ij.2 (bandBase w.1))}

theorem mem_bandSheetPartTwo {p m k₁ k₂ : ℕ}
    {s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    {s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    {G : Set (Fin (bandDim p m) → ℝ)} {ij : Fin k₁ × Fin k₂} {w : G} :
    w ∈ bandSheetPartTwo s₁ s₂ G ij ↔
      (bandZ2 w.1 = Fin.append (bandBase w.1) (s₁ ij.1 (bandBase w.1)) ∧
        bandZ2' w.1 = Fin.append (bandBase w.1) (s₂ ij.2 (bandBase w.1))) := Iff.rfl

end Work.WilE7.BandAux
