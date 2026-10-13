/-
  WilE9 / `Gen` — vocabulary for `Submission/Work/WilE9/Gen/gen_contSet.lean`.

  The continuity locus of a `Gen`-graph is built out of `Gen`-operations only, so all the
  intermediate sets are defined here as plain set-builders over `ℝ^N`, together with the
  coordinate index maps that make the point equations (`Fin.snoc`, `snocIt`) readable.

  ## The layout

  The primary space is `ℝ^{(n+3)+(n+1)}` with coordinates

      z = (v₀ … vₙ, ε, δ, w₀ … wₙ),   v j := z (iV n j), ε := z (iE n), δ := z (iD n),
                                      w j := z (iW n j).

  The block `w` is the last `n+1` coordinates, so `blkLift (n+1) (n+3) G` says `w ∈ G`, and
  the block `(v, ε, δ)` is the first `n+3` coordinates, so `Work.WilG0.projLastIter (n+3) (n+1)`
  quantifies `w` away.

  The continuity property of `G` at `v` is, with `close(v,δ,w) := ∀ j < n, (w j - v j)² < δ²`,

      Cont v  ↔  ∀ ε > 0, ∃ δ > 0, ∀ w ∈ G, close(v,δ,w) → |wₙ - vₙ| < ε,

  and the "bad" body `Psi = {w ∈ G ∧ close ∧ ε² ≤ (wₙ - vₙ)²}` has `Psi ∈ Gen` because every
  atom is semialgebraic.  `Theta`, `T3set`, `T5set` are the successive projections and
  complements of the negation chain `¬Cont`, and `Sfin n G = G ∩ T5setᶜ` is the continuity
  locus.
-/
import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.snocIt_natAdd

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Classical Topology
namespace Work.WilE9.Gen
open WilkiesDesign WilkiesDesign.E

/-! ## Lifts -/

/-- `X ⊆ ℝ^m` placed in the *last* `m` coordinates of `ℝ^{k+m}` (the first `k` coordinates are
free).  This is the `k`-fold iterate of `Gen.prod_left`. -/
def blkLift (m k : ℕ) (X : Set (Fin m → ℝ)) : Set (Fin (k + m) → ℝ) :=
  {z | (fun i : Fin m => z (Fin.natAdd k i)) ∈ X}

/-! ## Coordinates of the big space `ℝ^{(n+3)+(n+1)}` -/

/-- The `v_j`-coordinate, `j < n` (first block, position `j`). -/
def iV (n : ℕ) (j : Fin n) : Fin ((n + 3) + (n + 1)) :=
  Fin.castAdd (n + 1) (⟨j.val, by omega⟩ : Fin (n + 3))

/-- The `vₙ`-coordinate (first block, position `n`). -/
def iVlast (n : ℕ) : Fin ((n + 3) + (n + 1)) :=
  Fin.castAdd (n + 1) (⟨n, by omega⟩ : Fin (n + 3))

/-- The `ε`-coordinate (first block, position `n+1`). -/
def iE (n : ℕ) : Fin ((n + 3) + (n + 1)) :=
  Fin.castAdd (n + 1) (⟨n + 1, by omega⟩ : Fin (n + 3))

/-- The `δ`-coordinate (first block, position `n+2`). -/
def iD (n : ℕ) : Fin ((n + 3) + (n + 1)) :=
  Fin.castAdd (n + 1) (⟨n + 2, by omega⟩ : Fin (n + 3))

/-- The `w_j`-coordinate, `j < n` (second block, position `n+3+j`). -/
def iW (n : ℕ) (j : Fin n) : Fin ((n + 3) + (n + 1)) :=
  Fin.natAdd (n + 3) (⟨j.val, by omega⟩ : Fin (n + 1))

/-- The `wₙ`-coordinate (second block, last position). -/
def iWlast (n : ℕ) : Fin ((n + 3) + (n + 1)) :=
  Fin.natAdd (n + 3) (Fin.last n)

/-! ## Coordinates of the projected spaces -/

/-- Coordinates of a point `(v, ε, δ) ∈ ℝ^{n+3}`. -/
def xV (n : ℕ) (j : Fin n) : Fin (n + 3) := ⟨j.val, by omega⟩
def xVlast (n : ℕ) : Fin (n + 3) := ⟨n, by omega⟩
def xE (n : ℕ) : Fin (n + 3) := ⟨n + 1, by omega⟩
def xD (n : ℕ) : Fin (n + 3) := Fin.last (n + 2)

/-- Coordinates of a point `(v, ε) ∈ ℝ^{n+2}`. -/
def qV (n : ℕ) (j : Fin n) : Fin (n + 2) := ⟨j.val, by omega⟩
def qVlast (n : ℕ) : Fin (n + 2) := ⟨n, by omega⟩
def qE (n : ℕ) : Fin (n + 2) := ⟨n + 1, by omega⟩

/-- Coordinates of a point `v ∈ ℝ^{n+1}`. -/
def vV (n : ℕ) (j : Fin n) : Fin (n + 1) := Fin.castSucc j

/-! ## The semialgebraic atoms -/

/-- `δ² - (w_j - v_j)²`: the atom of the sup-metric closeness `|w_j - v_j| < δ` for `j < n`. -/
def Pclose (n : ℕ) (j : Fin n) : MvPolynomial (Fin ((n + 3) + (n + 1))) ℝ :=
  MvPolynomial.X (iD n) ^ 2 - (MvPolynomial.X (iW n j) - MvPolynomial.X (iV n j)) ^ 2

/-- `ε² - (wₙ - vₙ)²`: the atom of the "bad" condition `|wₙ - vₙ| ≥ ε`. -/
def Ptail (n : ℕ) : MvPolynomial (Fin ((n + 3) + (n + 1))) ℝ :=
  MvPolynomial.X (iE n) ^ 2 - (MvPolynomial.X (iWlast n) - MvPolynomial.X (iVlast n)) ^ 2

/-- The set `δ² - (w_j - v_j)² > 0`, i.e. `|w_j - v_j| < δ`. -/
def closeAtom (n : ℕ) (j : Fin n) : Set (Fin ((n + 3) + (n + 1)) → ℝ) :=
  {z | 0 < MvPolynomial.eval z (Pclose n j)}

/-- The set `ε² - (wₙ - vₙ)² ≤ 0`, i.e. `|wₙ - vₙ| ≥ ε`. -/
def tailAtom (n : ℕ) : Set (Fin ((n + 3) + (n + 1)) → ℝ) :=
  {z | MvPolynomial.eval z (Ptail n) ≤ 0}

/-! ## The chain of sets -/

/-- The "bad" body of the continuity condition: `w ∈ G`, the first `n` coordinates of `w` are
within `δ` of those of `v`, and the last coordinate of `w` is at distance `≥ ε` from `vₙ`. -/
def Psi (n : ℕ) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin ((n + 3) + (n + 1)) → ℝ) :=
  blkLift (n + 1) (n + 3) G ∩ (⋂ j : Fin n, closeAtom n j) ∩ tailAtom n

/-- `∃ w, (v,ε,δ,w) ∈ Psi`: the body of the "bad" set in the coordinates `(v, ε, δ)`. -/
def Theta (n : ℕ) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (n + 3) → ℝ) :=
  Work.WilG0.projLastIter (n + 3) (n + 1) (Psi n G)

/-- `∃ δ > 0, (v,ε,δ) ∉ Theta`. -/
def T3set (n : ℕ) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (n + 2) → ℝ) :=
  projLast ({z : Fin (n + 3) → ℝ | 0 < z (xD n)} ∩ (Theta n G)ᶜ)

/-- `∃ ε > 0, (v,ε) ∉ T3set`. -/
def T5set (n : ℕ) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  projLast ({z : Fin (n + 2) → ℝ | 0 < z (qE n)} ∩ (T3set n G)ᶜ)

/-- The continuity locus of the `Gen`-graph `G`. -/
def Sfin (n : ℕ) (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  G ∩ (T5set n G)ᶜ

end Work.WilE9.Gen
