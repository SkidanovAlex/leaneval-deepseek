/-
  WilE9 — shared definitions for `Submission/Work/WilE9/Gen/gen_interior.lean`.

  Everything here is vocabulary for the proof that the frozen inductive
  `WilkiesDesign.E.Gen` is closed under topological interior: `Gen` has no
  "interior" constructor, so `interior X` has to be *built* from `X` using
  `compl`, `proj`, `prod_left`, `inter` and `hyp` only.

  The ambient space is `ℝ^{(n+1)+n}` and the layout of its coordinates is

      z = (x, ε, y),   x i := z (xIdx i),  ε := z (eIdx n),  y i := z (yIdx i),

  (`x` in positions `0..n-1`, `ε` in position `n`, `y` in positions `n+1..2n`).
  `mkPt x ε y` is the corresponding point, built with `Fin.append`/`Fin.snoc`
  so that `liftZ`/`projY` below (whose block structure is `Fin.tail`/`Fin.append`)
  act on it in the obvious way:

  * `liftZ (n+1) n {w | Fin.tail w ∈ X}` consists of the points whose `y`-block
    lies in `X` (the `x`- and `ε`-coordinates are free);
  * `projY (n+1) n` quantifies the `y`-block away, leaving `(x, ε) ∈ ℝ^{n+1}`;
  * `ballSet n` is `{z | 0 < ε ∧ ∀ i, (y i - x i)^2 < ε^2}` and `posSet n` is
    `{u | 0 < u (last n)}`.
-/
import Mathlib
import Submission.Work.WilE9.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Topology
namespace Work.WilE9.Gen
open WilkiesDesign WilkiesDesign.E

/-- The `i`-th `x`-coordinate of the `(x, ε, y)`-layout of `ℝ^{(n+1)+n}`. -/
def xIdx {n : ℕ} (i : Fin n) : Fin ((n + 1) + n) := ⟨i.val, by omega⟩

/-- The `ε`-coordinate of the `(x, ε, y)`-layout of `ℝ^{(n+1)+n}`. -/
def eIdx (n : ℕ) : Fin ((n + 1) + n) := ⟨n, by omega⟩

/-- The `i`-th `y`-coordinate of the `(x, ε, y)`-layout of `ℝ^{(n+1)+n}`. -/
def yIdx {n : ℕ} (i : Fin n) : Fin ((n + 1) + n) := ⟨n + 1 + i.val, by omega⟩

/-- The point of `ℝ^{(n+1)+n}` with coordinates `(x, ε, y)`. -/
def mkPt {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) (y : Fin n → ℝ) : Fin ((n + 1) + n) → ℝ :=
  Fin.append (Fin.snoc x ε) y

/-- Prepending `k` free coordinates to a set: the `k`-fold iterate of
`WilkiesDesign.E.Gen.prod_left`. The original coordinates end up in the *last*
`n` positions. -/
def liftZ (n : ℕ) : (k : ℕ) → Set (Fin n → ℝ) → Set (Fin (n + k) → ℝ)
  | 0, X => X
  | k + 1, X => {z | Fin.tail z ∈ liftZ n k X}

/-- Projecting away the last `k` coordinates: the `k`-fold iterate of `projLast`
(hence of the `Gen.proj` constructor). -/
def projY (n : ℕ) : (k : ℕ) → Set (Fin (n + k) → ℝ) → Set (Fin n → ℝ)
  | 0, X => X
  | k + 1, X => projY n k (projLast X)

/-- The `n+1` positivity conditions whose intersection is `ballSet n`: index `0` is
`ε > 0` (the polynomial `X (eIdx n)`) and index `i+1` is `ε^2 - (y i - x i)^2 > 0`. -/
def ballPoly (n : ℕ) : Fin (n + 1) → MvPolynomial (Fin ((n + 1) + n)) ℝ :=
  Fin.cases (MvPolynomial.X (eIdx n))
    (fun i => MvPolynomial.X (eIdx n) ^ 2 -
      (MvPolynomial.X (yIdx i) - MvPolynomial.X (xIdx i)) ^ 2)

/-- The set of `z = (x, ε, y)` with `ε > 0` and `|y i - x i| < ε` for all `i`. -/
def ballSet (n : ℕ) : Set (Fin ((n + 1) + n) → ℝ) :=
  ⋂ j : Fin (n + 1), {z | 0 < MvPolynomial.eval z (ballPoly n j)}

/-- The set of `u : Fin (n+1) → ℝ` with `0 < u (last n)`, i.e. the `ε > 0` condition
after the `y`-block has been projected away. -/
def posSet (n : ℕ) : Set (Fin (n + 1) → ℝ) := {u | 0 < u (Fin.last n)}

end Work.WilE9.Gen
