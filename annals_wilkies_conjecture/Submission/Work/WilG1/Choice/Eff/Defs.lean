/-
  WilG1/Choice/Eff — the "leftmost selection" construction for one-dimensional definable
  choice (BNZ §2.3).

  Given a set `X ⊆ ℝ^{p+1}` in `Ω` and a cylindrical decomposition `C` of `ℝ^{p+1}` adapted
  to `X`, every cell of `C` is either contained in `X` or disjoint from it.  `selOf K` is the
  selection set of `selSet` on the region of parameters whose fibre in `K` is nonempty; by
  `selSet_fibre` it picks exactly one point of each fibre of a *cell* `K`.

  Over a parameter `l` with nonempty fibre in `X`, the cells of `C` contained in `X` give
  finitely many selected values, and `minGraph` takes their minimum.  `sigmaOf C X` is the
  set of all the selected points of the cells of `C` contained in `X`; `minGraph X (sigmaOf C X)`
  is then the graph of a genuine function, is contained in `X`, and is `Ω`-definable.
-/
import Submission.Work.WilG1.ChoiceDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG1.Choice.Eff

open WilkiesDesign

/-- The selection set of a set `K`: `selSet` on the region of parameters whose fibre in `K`
is nonempty. -/
def selOf {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  Work.WilG1.selSet K (Work.WilG1.projPar K)

/-- The union of the selections of the cells of `C` that are contained in `X`, intersected
with `X`. -/
def sigmaOf {p : ℕ} (C : Finset (Set (Fin (p + 1) → ℝ))) (X : Set (Fin (p + 1) → ℝ)) :
    Set (Fin (p + 1) → ℝ) :=
  ⋃ κ ∈ C.filter (fun κ => κ ⊆ X), (selOf κ ∩ X)

/-- The graph of the minimal selection: over the parameters whose fibre in `X` is empty the
value is `0`, and otherwise the value is the minimum of the fibre of `Sg`. -/
def minGraph {p : ℕ} (X Sg : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  {z | (z (Fin.last p) = 0 ∧ ¬ ∃ t : ℝ, Fin.snoc (Fin.init z) t ∈ X) ∨
    (z ∈ Sg ∧ ∀ t : ℝ, Fin.snoc (Fin.init z) t ∈ Sg → z (Fin.last p) ≤ t)}

theorem mem_minGraph {p : ℕ} {X Sg : Set (Fin (p + 1) → ℝ)} {z : Fin (p + 1) → ℝ} :
    z ∈ minGraph X Sg ↔
      ((z (Fin.last p) = 0 ∧ ¬ ∃ t : ℝ, Fin.snoc (Fin.init z) t ∈ X) ∨
        (z ∈ Sg ∧ ∀ t : ℝ, Fin.snoc (Fin.init z) t ∈ Sg → z (Fin.last p) ≤ t)) := Iff.rfl

theorem mem_sigmaOf {p : ℕ} {C : Finset (Set (Fin (p + 1) → ℝ))}
    {X : Set (Fin (p + 1) → ℝ)} {z : Fin (p + 1) → ℝ} :
    z ∈ sigmaOf C X ↔ ∃ κ ∈ C, κ ⊆ X ∧ z ∈ selOf κ ∧ z ∈ X := by
  simp only [sigmaOf, Finset.mem_filter, Set.mem_iUnion, Set.mem_inter_iff, exists_prop,
    and_assoc]

theorem sigmaOf_subset {p : ℕ} {C : Finset (Set (Fin (p + 1) → ℝ))}
    {X : Set (Fin (p + 1) → ℝ)} : sigmaOf C X ⊆ X := by
  intro z hz
  obtain ⟨κ, -, -, -, hzX⟩ := mem_sigmaOf.mp hz
  exact hzX

end Work.WilG1.Choice.Eff
