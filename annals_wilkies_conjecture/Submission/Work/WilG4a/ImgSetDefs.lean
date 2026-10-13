/-
  WilG4a — definition of the *image set* of a family member along a cell.

  For a cell `κ ⊆ ℝ^{p+1}` (coordinates `(l, y)`) and a family member
  `f : ℝ^p × ℝ → ℝ`, `imgSet κ f ⊆ ℝ^{p+1}` is the set of pairs `(l, s)` such that `s` is a value
  of `f(l, ·)` at a point `y` of the fibre of `κ` over `l`:

    `(l,s) ∈ imgSet κ f  ↔  ∃ y, (l,y) ∈ κ ∧ f l y = s`.

  Its fibre over `l` is therefore exactly the image `imgFibre κ f l`, and the lower/upper
  endpoints `Aend κ f`, `Bend κ f` are the infimum/supremum of that fibre:

    `Aend κ f l = sInf {x | Fin.snoc l x ∈ imgSet κ f}`.

  The set is built from `κ` and the graph of `f` by a coordinate projection
  (`imgSet κ f = coordImage (iota1 p) ({w | Fin.init w ∈ κ} ∩ graphFam f)`), so its
  `Ω`-membership is controlled by `coordImage_mem`; that is the content of `imgSet_mem`.
-/
import Mathlib
import Submission.Work.WilG4a.LipChartsDefs
import Submission.Work.WilG5.Reindex3

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesDesign WilkiesConjecture

/-- The image of the fibre of `κ` over `l` under `f`, as a set of pairs `(l, s)` in `ℝ^{p+1}`. -/
def imgSet (p : ℕ) (κ : Set (Fin (p + 1) → ℝ)) (f : (Fin p → ℝ) → ℝ → ℝ) :
    Set (Fin (p + 1) → ℝ) :=
  {z | ∃ y : ℝ, Fin.snoc (Fin.init z) y ∈ κ ∧ f (Fin.init z) y = z (Fin.last p)}

/-- Reading `imgSet` on a `Fin.snoc`: the fibre of `imgSet κ f` over `l` is the image of the
fibre of `κ` over `l` under `f`. -/
@[simp] theorem mem_imgSet_snoc (p : ℕ) (κ : Set (Fin (p + 1) → ℝ))
    (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) (s : ℝ) :
    Fin.snoc l s ∈ imgSet p κ f ↔ ∃ y : ℝ, Fin.snoc l y ∈ κ ∧ f l y = s := by
  simp only [imgSet, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]

/-- The fibre of `imgSet κ f` over `l` is `imgFibre κ f l`. -/
theorem imgFibre_eq (p : ℕ) (κ : Set (Fin (p + 1) → ℝ)) (f : (Fin p → ℝ) → ℝ → ℝ)
    (l : Fin p → ℝ) :
    {x : ℝ | Fin.snoc l x ∈ imgSet p κ f} = imgFibre κ f l := by
  ext s
  simp only [imgFibre, Set.mem_ofPred_eq, mem_imgSet_snoc]

end Work.WilG4a
