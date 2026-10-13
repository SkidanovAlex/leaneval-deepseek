/-
  WilCrux — vocabulary shared by the lemmas feeding `Work.WilCrux.OmegaModulus`
  (H1, the Ω-bookkeeping of the "uniform modulus of continuity" set of a definable family).

  Given `f : ℝ^a → ℝ^b → ℝ` we view it as a single function `famFun f` on `ℝ^{a+b}`; its graph
  is `famGraph f` (`WilG4a`/`CG.Spec`).  The Ω-set of H1 lives in `ℝ^{(a+1)+(a+b)}`: the first
  `a+1` coordinates are the pair `(w, η)`, the last `a+b` are the point `(w', z)`.  The index
  maps below name the individual coordinates of that ambient space.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG0.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilCrux

open WilkiesDesign WilkiesDesign.CG

/-- The family member `f : ℝ^a → ℝ^b → ℝ` read as a single function on `ℝ^{a+b}`
(parameters first, then the fibre coordinates). -/
def famLift {a b : ℕ} (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) : (Fin (a + b) → ℝ) → ℝ :=
  fun l => f (fun i => l (Fin.castAdd b i)) (fun j => l (Fin.natAdd a j))

/-- The graph of `famLift f` is exactly `famGraph f`. -/
theorem graphOf_famLift {a b : ℕ} (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) :
    graphOf (famLift f) = famGraph f := rfl

/-- The coordinate carrying `η` (the last parameter coordinate) inside `ℝ^{(a+1)+(a+b)}`. -/
def etaIdx (a b : ℕ) : Fin ((a + 1) + (a + b)) := Fin.castAdd (a + b) (Fin.last a)

/-- The coordinate carrying the `i`-th centre coordinate `w i` of the ball. -/
def centreIdx (a b : ℕ) (i : Fin a) : Fin ((a + 1) + (a + b)) :=
  Fin.castAdd (a + b) (Fin.castSucc i)

/-- The coordinate carrying the `i`-th coordinate `w' i` of the punctured ball. -/
def upperIdx (a b : ℕ) (i : Fin a) : Fin ((a + 1) + (a + b)) :=
  Fin.natAdd (a + 1) (Fin.castAdd b i)

/-- The coordinate carrying the `j`-th fibre coordinate `z j`. -/
def fibreIdx (a b : ℕ) (j : Fin b) : Fin ((a + 1) + (a + b)) :=
  Fin.natAdd (a + 1) (Fin.natAdd a j)

/-- The `Ω`-set of H1: the last `a+b` coordinates `(w', z)` of `u` satisfy
`|w_i - w'_i| < η`, `z ≠ 0`, `|z_j| < η`, and `¬ (|f w' z| < ε)`, where `η` is the last of
the first `a+1` coordinates.  The coordinatewise forms of `dist` and `‖·‖` are used so that
the set is visibly a finite boolean combination of polynomial (in)equalities; under `η > 0`
they agree with `dist` and `‖·‖`. -/
def Tset {a b : ℕ} (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (ε : ℝ) :
    Set (Fin ((a + 1) + (a + b)) → ℝ) :=
  {u | (∀ i : Fin a, |u (centreIdx a b i) - u (upperIdx a b i)| < u (etaIdx a b))
    ∧ (fun j : Fin b => u (fibreIdx a b j)) ≠ 0
    ∧ (∀ j : Fin b, |u (fibreIdx a b j)| < u (etaIdx a b))
    ∧ ¬ (|famLift f (fun k : Fin (a + b) => u (Fin.natAdd (a + 1) k))| < ε)}

end Work.WilCrux
