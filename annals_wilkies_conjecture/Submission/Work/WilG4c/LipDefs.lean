/-
  WilG4c — vocabulary for the §5.3 reduction (BNZ, *Wilkie's conjecture for Pfaffian
  structures*, §5.3 "Reduction to 1-Lipschitz").

  The reduction deduces `FLemP S p (n+1) (PY p n)` from `FLemP S p (n+1) (PYLip p n)`.  Since
  `PY` only constrains the `y`-derivatives, its content is the classical Yomdin–Gromov
  preparation (BNZ §5.3): the `x`-derivative of a `PY` family is `O_n(1)` off a finite
  (`Ω`-definable) exceptional set of `x`-values, so the family is `O_n(1)`-Lipschitz off those
  hyperplanes; a cell decomposition of `Λ × I_x` compatible with the exceptional set splits the
  family into pieces that a linear rescaling of `x` turns into `1`-Lipschitz families, to which
  the `1`-Lipschitz F-lemma applies.

  Coordinates.  A family member is
  `f : (Fin p → ℝ) → (Fin (n+1) → ℝ) → ℝ`, parameter `l : Fin p → ℝ`, cube point
  `z : Fin (n+1) → ℝ` with `z 0 = x` (the distinguished coordinate) and `z (i+1) = y i`.
  `famFunHat f` is the same as a single function on `ℝ^{p + (n+1)}`, with the *last*
  `n+1` coordinates the cube point (matching `WilkiesDesign.CG.famGraph`), and `xPt l x y` is
  the corresponding point.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.Hyps

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The family member as one function -/

/-- A family member read as a single function on `ℝ^{p + (n+1)}`: the first `p` coordinates
are the parameter, the last `n+1` are the cube point.  This is exactly the function whose
graph is `famGraph f`. -/
def famFunHat {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    (Fin (p + (n + 1)) → ℝ) → ℝ :=
  fun z => f (fun i => z (Fin.castAdd (n + 1) i)) (fun j => z (Fin.natAdd p j))

theorem famGraph_eq_graphOf_famFunHat {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    famGraph f = graphOf (famFunHat f) := rfl

/-- The point `(l, x, y)` of `ℝ^{p + (n+1)}`. -/
def xPt {p n : ℕ} (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) : Fin (p + (n + 1)) → ℝ :=
  Fin.append l (Fin.cons x y)

@[simp] theorem famFunHat_xPt {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    famFunHat f (xPt l x y) = f l (Fin.cons x y) := by
  simp [famFunHat, xPt, Fin.append_left, Fin.append_right]

/-- The coordinate of `ℝ^{p + (n+1)}` holding the distinguished `x`. -/
def xDirHat (p n : ℕ) : Fin (p + (n + 1)) := Fin.natAdd p 0

@[simp] theorem xPt_xDirHat {p n : ℕ} (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    xPt l x y (xDirHat p n) = x := by
  simp [xPt, xDirHat]

/-! ## 2. The improper point `(l,x)` of `ℝ^{p+1}` -/

/-- The pair `(l,x)` as a point of `ℝ^{p+1}` (parameter first, then `x`). -/
def lxPt {p : ℕ} (l : Fin p → ℝ) (x : ℝ) : Fin (p + 1) → ℝ := Fin.snoc l x

@[simp] theorem lxPt_castSucc {p : ℕ} (l : Fin p → ℝ) (x : ℝ) (i : Fin p) :
    lxPt l x (Fin.castSucc i) = l i := by simp [lxPt]

@[simp] theorem lxPt_last {p : ℕ} (l : Fin p → ℝ) (x : ℝ) : lxPt l x (Fin.last p) = x := by
  simp [lxPt]

/-! ## 3. The exceptional set of `x`-values and the `x`-derivative bound -/

/-- The `x`-derivative of a family member at `(l,x,y)`. -/
def xDeriv {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) : ℝ :=
  fderiv ℝ (famFunHat f) (xPt l x y) (Pi.single (xDirHat p n) 1)

/-- `BadX f`: the set of `(l,x) ∈ ℝ^{p+1}` with `x ∈ I` at which `|∂₀ f|` is unbounded in `y`
over the `C¹` locus of the fibre.  This is the exceptional set produced by BNZ Lemma 5.6
(`Work.WilG4c.BddDxHyp`) inside the §5.3 reduction. -/
def BadX {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (p + 1) → ℝ) :=
  {w | w (Fin.last p) ∈ I ∧
    ∀ M : ℝ, ∃ y : Fin n → ℝ, y ∈ openCube n ∧
      xPt (fun i => w (Fin.castSucc i)) (w (Fin.last p)) y ∈
        interior {z | ContDiffAt ℝ 1 (famFunHat f) z} ∧
      M < |xDeriv f (fun i => w (Fin.castSucc i)) (w (Fin.last p)) y|}

/-- `XDerivBdd f B C`: off the exceptional set `B`, the `x`-derivative of `f` is bounded by
`C` (on the `C¹` locus of each fibre). -/
def XDerivBdd {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (B : Set (Fin (p + 1) → ℝ)) (C : ℝ) : Prop :=
  ∀ w ∉ B, w (Fin.last p) ∈ I → ∀ y ∈ openCube n,
    xPt (fun i => w (Fin.castSucc i)) (w (Fin.last p)) y ∈
      interior {z | ContDiffAt ℝ 1 (famFunHat f) z} →
    |xDeriv f (fun i => w (Fin.castSucc i)) (w (Fin.last p)) y| ≤ C

/-- The fibre of the exceptional set over a parameter `l`. -/
def badFibre {p : ℕ} (B : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) : Set ℝ :=
  {x | lxPt l x ∈ B}

@[simp] theorem mem_badFibre {p : ℕ} (B : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (x : ℝ) :
    x ∈ badFibre B l ↔ lxPt l x ∈ B := Iff.rfl

/-! ## 4. `YBound` for a one-member family, in `famFunHat` form -/

theorem ybound_iff {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (r : ℕ) :
    YBound (fun _ : Fin 1 => f) r ↔
      ∀ l : Fin p → ℝ, ∀ x ∈ I, ∀ m, m ≤ r → ∀ y ∈ openCube n,
        ‖iteratedFDeriv ℝ m (slice (f l) x) y‖ ≤ 1 := by
  constructor
  · intro h l x hx m hm y hy
    simpa using h (0 : Fin 1) l x hx m hm y hy
  · intro h i l x hx m hm y hy
    simpa using h l x hx m hm y hy

end Work.WilkG4c
