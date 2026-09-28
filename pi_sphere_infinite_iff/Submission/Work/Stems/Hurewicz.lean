import Mathlib
import Submission.Work.Stems.HurewiczSphere
import Submission.Work.Stems.exists_collapsingMap

/-!
# The Hurewicz map `πₙ(X,x₀) → Hₙ(X;ℤ)`

Mathlib's `HomotopyGroup (Fin n) X x₀` is built from *cubes* `Iⁿ → X` which send `∂Iⁿ` to `x₀`.
To push the fundamental class of `Sⁿ` forward along such a cube we use the collapse
`φ : Iⁿ → Sⁿ` of `Work.Stems.exists_collapsingMap`: a cube representative `p` of a class in
`πₙ(X,x₀)` is constant on the fibres of `φ`, so it descends to a continuous map
`Sⁿ → X` (`Topology.IsQuotientMap.lift`), whose Hurewicz class
(`Work.Stems.hurewiczClass`, `HurewiczSphere.lean`) is the value of the Hurewicz map on the class.

The construction is well defined on homotopy classes (`hurewiczChain_eq_of_homotopic`), which is
delegated; `hurewiczMap` is then the induced map on `HomotopyGroup`.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

/-- The chosen collapse `Iⁿ → Sⁿ` (onto, sends `∂Iⁿ` to `φ 0`, injective off `∂Iⁿ`). -/
def collapseMap (n : ℕ) (hn : 1 ≤ n) : C(CubeI n, sphere n) :=
  Classical.choose (exists_collapsingMap n hn)

theorem collapseMap_isQuotientMap (n : ℕ) (hn : 1 ≤ n) :
    Topology.IsQuotientMap (collapseMap n hn) :=
  (Classical.choose_spec (exists_collapsingMap n hn)).1

theorem collapseMap_boundary (n : ℕ) (hn : 1 ≤ n) {q : CubeI n}
    (hq : q ∈ _root_.Cube.boundary (Fin n)) :
    collapseMap n hn q = collapseMap n hn 0 :=
  (Classical.choose_spec (exists_collapsingMap n hn)).2.1 q hq

theorem collapseMap_fiber (n : ℕ) (hn : 1 ≤ n) {q q' : CubeI n}
    (h : collapseMap n hn q = collapseMap n hn q') :
    q = q' ∨ (q ∈ _root_.Cube.boundary (Fin n) ∧ q' ∈ _root_.Cube.boundary (Fin n)) :=
  (Classical.choose_spec (exists_collapsingMap n hn)).2.2 q q' h

/-- A cube representative of a class in `πₙ(X,x₀)` descends to the sphere along the collapse. -/
def cubeLift (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] {x₀ : X}
    (p : Ω^ (Fin n) X x₀) : C(sphere n, X) :=
  (collapseMap_isQuotientMap n hn).lift p.1
    (fun _ _ h => by
      rcases collapseMap_fiber n hn h with h' | ⟨hq, hq'⟩
      · rw [h']
      · rw [p.2 _ hq, p.2 _ hq'])

/-- The lift restricted to the cube is the original cube map. -/
theorem cubeLift_comp (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] {x₀ : X}
    (p : Ω^ (Fin n) X x₀) : (cubeLift n hn p).comp (collapseMap n hn) = p.1 :=
  (collapseMap_isQuotientMap n hn).lift_comp p.1 _

/-- The **Hurewicz class** of a cube: the Hurewicz class of its descent to `Sⁿ`. -/
def hurewiczChain (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] (x₀ : X)
    (p : Ω^ (Fin n) X x₀) : (chains (TopCat.of X)).homology n :=
  hurewiczClass n hn (cubeLift n hn p)

end

end Work.Stems
