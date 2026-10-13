/-
  WilG4c / `CritAux` — the `Ω`-definability of the ball-condensation operator `HypoRaw`.

  `HypoRaw p n X` is the set of points `u = (l,z)` such that some *fibre* ball around `u` (i.e.
  a ball around `z` inside the fibre `l = const`) is contained in `X`.  The file
  `CritAux/hypoRaw_mem.lean` proves that it is `Ω`-definable with format/degree bounds uniform
  in the data.

  This module holds the vocabulary of the construction.  The auxiliary ambient space is
  `ℝ^{hypoM p n}` with coordinates `(x, r, y)`: `x ∈ ℝ^{hypoN p n}` is the base point, `r` a
  radius and `y ∈ ℝ^{n+1}` the varying cube point.  Concretely, in the `snocIt` coordinates of
  `hypoM p n = (hypoN p n + 1) + (n + 1)`, the first `hypoN p n` coordinates are `x`, the next one
  is `r` and the last `n+1` are `y`.

  * `iotaA p n : Fin (hypoN p n) → Fin (hypoM p n)` is the index map of the substitution
    `(x,r,y) ↦ (parPt x, y)` (drop the `z`-block of `x`, keep the parameter block, append `y`).
  * `ballP p n` is the polynomial `r^2 - Σ_j (y_j - z_j)^2`; its positivity locus is the
    Euclidean ball of radius `r` around `z` in the fibre.
  * `HypoBall p n` is that positivity locus.
  * `HypoA p n X` is the pullback of `Xᶜ` along the substitution `w ↦ w ∘ iotaA p n`.
  * `HypoBuild p n X` is the final `Ω`-construction: project `y` away, complement, record `r > 0`,
    project `r` away.
  * `HypoRawE p n X` is the Euclidean-ball description of `HypoRaw p n X`.

  Everything in this file is a definition; it is `sorry`-free.
-/
import Mathlib
import Submission.Work.WilG4c.CritAux
import Submission.Work.WilG0.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign

/-- The dimension of the base space `ℝ^{p + (n+1)}`. -/
abbrev hypoN (p n : ℕ) : ℕ := p + (n + 1)

/-- The dimension of the auxiliary space `(x, r, y)`. -/
abbrev hypoM (p n : ℕ) : ℕ := (hypoN p n + 1) + (n + 1)

/-- The index map of the substitution `(x,r,y) ↦ (parPt x, y)`: the parameter coordinates
`Fin p` sit at positions `0,…,p-1` (inside the `x`-block) and the `y`-coordinates at the end. -/
def iotaA (p n : ℕ) : Fin (hypoN p n) → Fin (hypoM p n) :=
  Fin.append
    (fun i : Fin p => Fin.castAdd (n + 1) (Fin.castSucc (Fin.castAdd (n + 1) i)))
    (fun j : Fin (n + 1) => Fin.natAdd (hypoN p n + 1) j)

/-- The polynomial `r^2 - Σ_j (y_j - z_j)^2` in the coordinates `(x, r, y)`. -/
def ballP (p n : ℕ) : MvPolynomial (Fin (hypoM p n)) ℝ :=
  MvPolynomial.X (Fin.castAdd (n + 1) (Fin.last (hypoN p n))) ^ 2 -
    ∑ j : Fin (n + 1),
      (MvPolynomial.X (Fin.natAdd (hypoN p n + 1) j)
        - MvPolynomial.X (Fin.castAdd (n + 1) (Fin.castSucc (Fin.natAdd p j)))) ^ 2

/-- The pullback of `Xᶜ` along the substitution `w ↦ w ∘ iotaA p n`. -/
def HypoA (p n : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)) : Set (Fin (hypoM p n) → ℝ) :=
  {w | w ∘ iotaA p n ∈ Xᶜ}

/-- The positivity locus of `ballP p n`: `y` lies in the Euclidean ball of radius `r` around `z`. -/
def HypoBall (p n : ℕ) : Set (Fin (hypoM p n) → ℝ) :=
  {w | 0 < MvPolynomial.eval w (ballP p n)}

/-- The `Ω`-construction: the set of `x` such that some `r > 0` has every `y` in the ball
already satisfying `(parPt x, y) ∈ X`. -/
def HypoBuild (p n : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)) : Set (Fin (p + (n + 1)) → ℝ) :=
  projLast ((Work.WilG0.projLastIter (hypoN p n + 1) (n + 1) (HypoA p n X ∩ HypoBall p n))ᶜ
    ∩ {u : Fin (hypoN p n + 1) → ℝ | 0 < u (Fin.last (hypoN p n))})

/-- The Euclidean-ball description of `HypoRaw p n X`. -/
def HypoRawE (p n : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)) : Set (Fin (p + (n + 1)) → ℝ) :=
  {u | ∃ r : ℝ, 0 < r ∧ ∀ y : Fin (n + 1) → ℝ,
      (∑ j : Fin (n + 1), (y j - cubePt u j) ^ 2 < r ^ 2) → Fin.append (parPt u) y ∈ X}

end Work.WilkG4c
