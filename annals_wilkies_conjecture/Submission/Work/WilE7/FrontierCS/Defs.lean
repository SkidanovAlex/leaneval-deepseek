/-
  WilE7 / CS-slice: shared definitions of the `FrontierCS` nodes (design
  `sources/wilkiesE7/wilkies_e7_frontier.md`).  Kept in their own module so that the delegated
  node files can state their lemmas in the same vocabulary as `FrontierCS/Main.lean`.
-/
import Mathlib

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.FrontierCS

/-- The Jacobian determinant of a square map, written with partial derivatives. -/
def jacDet {j : ℕ} (g : (Fin j → ℝ) → (Fin j → ℝ)) (e : Fin j → ℝ) : ℝ :=
  (Matrix.of fun (a l : Fin j) => fderiv ℝ g e (Pi.single l 1) a).det

/-- The `0/1` slope matrix attached to a Boolean matrix. -/
def gridMat {d j : ℕ} (b : Fin d → Fin j → Bool) : Matrix (Fin d) (Fin j) ℝ :=
  Matrix.of fun k c => if b k c then 1 else 0

/-- The slice set: points of the slice chart over `W` where the slice Jacobian is invertible. -/
def sliceSet {N d j : ℕ} (G : (Fin N → ℝ) → (Fin j → ℝ)) (W : Set (Fin N → ℝ))
    (ψ : (Fin d → ℝ) × (Fin j → ℝ) → (Fin N → ℝ)) : Set ((Fin d → ℝ) × (Fin j → ℝ)) :=
  {p | ψ p ∈ W ∧ (fderiv ℝ (fun e => G (ψ (p.1, e))) p.2).range = ⊤}

/-- The slice chart attached to `γ`, `B` and the slope matrix `Λ`. -/
def sliceChart {N d j : ℕ} (γ : (Fin d → ℝ) → (Fin N → ℝ)) (B : (Fin j → ℝ) →L[ℝ] (Fin N → ℝ))
    (Λ : Matrix (Fin d) (Fin j) ℝ) : (Fin d → ℝ) × (Fin j → ℝ) → (Fin N → ℝ) :=
  fun p => γ (p.1 + Λ.mulVec p.2) + B p.2

end Work.WilE7.FrontierCS
