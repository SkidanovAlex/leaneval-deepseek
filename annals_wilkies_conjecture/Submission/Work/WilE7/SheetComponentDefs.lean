/-
  WilE7 (`Work.WilE7.SheetComponentDefs`): the vocabulary of the sheet-component lemma
  (`Work.WilE7.sheetComponent`).

  Over a base set `C ⊆ ℝ^p`, let `Z ⊆ ℝ^{p+q}` be a semi-Pfaffian set and `S` a stratum of
  `ℝ^{p+q}` over `ℝ^p`, and suppose the part of `S` over `C` is covered by the graphs of
  continuous maps `s i : ℝ^p → ℝ^q`, `i : Fin k` (pointwise distinct on `C`).  The sheet-component
  lemma studies the connected component of the point

  `w₀ = (u₀, (π u₀, s j (π u₀)))`

  in the *fibre product*

  `sheetProduct Z S = {(z₁, z₂) ∈ Z.set × S.X.set : π z₁ = π z₂}`

  (with `π = projFirst p q` the base projection), and shows that this component is contained in
  the graph of `s j` and projects onto `C`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.stratGraph

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-- The fibre product of the semi-Pfaffian set `Z ⊆ ℝ^{p+q}` with the stratum `S ⊆ ℝ^{p+q}` over
their common base `ℝ^p`, sitting in `ℝ^{(p+q)+(p+q)}`. -/
def sheetProduct (p q : ℕ) (Z : SemiPf (p + q)) (S : Stratum p q) :
    Set (Fin ((p + q) + (p + q)) → ℝ) :=
  {z | projFirst (p + q) (p + q) z ∈ Z.set ∧ projSnd (p + q) (p + q) z ∈ S.X.set ∧
    projFirst p q (projFirst (p + q) (p + q) z) = projFirst p q (projSnd (p + q) (p + q) z)}

/-- Membership in the fibre product, unfolded. -/
theorem mem_sheetProduct {p q : ℕ} {Z : SemiPf (p + q)} {S : Stratum p q}
    {z : Fin ((p + q) + (p + q)) → ℝ} :
    z ∈ sheetProduct p q Z S ↔
      projFirst (p + q) (p + q) z ∈ Z.set ∧ projSnd (p + q) (p + q) z ∈ S.X.set ∧
        projFirst p q (projFirst (p + q) (p + q) z) =
          projFirst p q (projSnd (p + q) (p + q) z) := Iff.rfl

/-- The point of the fibre product which joins the point `u₀` of `Z` to the graph of the sheet
`s j` above the base of `u₀`. -/
def sheetProductPt {p q : ℕ} (u₀ : Fin (p + q) → ℝ) {k : ℕ}
    (s : Fin k → (Fin p → ℝ) → (Fin q → ℝ)) (j : Fin k) : Fin ((p + q) + (p + q)) → ℝ :=
  Fin.append u₀ (Fin.append (projFirst p q u₀) (s j (projFirst p q u₀)))

/-- The part of the fibre product whose base projection lies in `C`. -/
def sheetBase {p q : ℕ} (Z : SemiPf (p + q)) (S : Stratum p q) (C : Set (Fin p → ℝ)) :
    Set (Fin ((p + q) + (p + q)) → ℝ) :=
  {z | z ∈ sheetProduct p q Z S ∧ projFirst p q (projSnd (p + q) (p + q) z) ∈ C}

/-- Membership in `sheetBase`, unfolded. -/
theorem mem_sheetBase {p q : ℕ} {Z : SemiPf (p + q)} {S : Stratum p q} {C : Set (Fin p → ℝ)}
    {z : Fin ((p + q) + (p + q)) → ℝ} :
    z ∈ sheetBase Z S C ↔
      z ∈ sheetProduct p q Z S ∧ projFirst p q (projSnd (p + q) (p + q) z) ∈ C := Iff.rfl

/-- The partition of `G` according to the sheet `s i` that the second factor lies on. -/
def sheetPart {p q k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin q → ℝ))
    (G : Set (Fin ((p + q) + (p + q)) → ℝ)) : Fin k → Set G :=
  fun i => {x : G | projSnd p q (projSnd (p + q) (p + q) x.1) =
    s i (projFirst p q (projSnd (p + q) (p + q) x.1))}

/-- Membership in a piece of the sheet partition, unfolded. -/
theorem mem_sheetPart {p q k : ℕ} {s : Fin k → (Fin p → ℝ) → (Fin q → ℝ)}
    {G : Set (Fin ((p + q) + (p + q)) → ℝ)} {i : Fin k} {x : G} :
    x ∈ sheetPart s G i ↔
      projSnd p q (projSnd (p + q) (p + q) x.1) =
        s i (projFirst p q (projSnd (p + q) (p + q) x.1)) := Iff.rfl

end Work.WilE7
