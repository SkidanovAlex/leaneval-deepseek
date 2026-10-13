/-
  WilG4c — vocabulary for the `CurveFam` lemma (BNZ §5.3/§5.4: a definable family of
  near-maximising curves of the `x`-derivative).

  A family member is `f : (Fin p → ℝ) → (Fin (n+1) → ℝ) → ℝ`; a *point* of `ℝ^{p+(n+1)}`
  is written in the `(l, x, y)` splitting used by `Work.WilkG4c.xPt` (the first `p`
  coordinates are the parameter `l`, the next one is `x`, the remaining `n` are `y`).

  The lemma `CurveFam` has to produce, definably in `(l,x)`, a point `γ l x` of the cube at
  which the `x`-derivative is within a factor `2` of the sup over the cube.  The selection
  set is built here:

  * `DgSet`      the graph of `x ↦ ∂₀ f` over the interior of the `C¹` locus (from `SharpDeriv`);
  * `LocSet`     the interior of the `C¹` locus itself (`= projLast DgSet`);
  * `cmpSet`     the relation `4 a² < b²`, i.e. `2|a| < |b|`, in `ℝ²`;
  * `badSet1`    `(w,y',s,s')` with `(w,s),(z',s') ∈ DgSet`, `4 s² < s'²` and `y' ∈ openCube n`,
                 where `z'` is `w` with its `y`-block replaced by `y'`;
  * `badSet`     the projection of `badSet1` onto `(w,y')` — `w` is *not* within a factor `2`
                 of the sup over the cube of the fibre;
  * `Xset`       the selection set: the `y ∈ openCube n` for which `(l,x,y) ∈ LocSet` and
                 `(l,x,y) ∉ badSet`.

  All index maps are of the shape consumed by `Work.WilG5.coordPre`; the ambient is
  `ℝ^{m+n+2}` (`m = p+(n+1)`) laid out as `(w | y' | s | s')`, so that `Work.WilG5.projN (n+2)`
  quantifies exactly the `y',s,s'`.
-/
import Mathlib
import Submission.Work.WilG4c.LipDefs
import Submission.Work.WilG5.Reindex3

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG5

variable (p n : ℕ)

/-! ## 1. The `x`-derivative graph and the `C¹` locus -/

/-- `DgSet p n f`: the graph of the `x`-derivative of the family member `f` over the interior
of its `C¹` locus, in `ℝ^{p+(n+1)+1}`.  This is the set produced by `SharpDeriv` at order `1`
in the direction `xDirHat p n`. -/
def DgSet (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    Set (Fin (p + (n + 1) + 1) → ℝ) :=
  {z | Fin.init z ∈ interior {x : Fin (p + (n + 1)) → ℝ | ContDiffAt ℝ 1 (famFunHat f) x} ∧
    z (Fin.last (p + (n + 1))) = iteratedFDeriv ℝ 1 (famFunHat f) (Fin.init z)
      (fun _ : Fin 1 => Pi.single (xDirHat p n) 1)}

/-- `LocSet p n f`: the interior of the `C¹` locus of the family member `f`, in `ℝ^{p+(n+1)}`. -/
def LocSet (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    Set (Fin (p + (n + 1)) → ℝ) :=
  interior {x : Fin (p + (n + 1)) → ℝ | ContDiffAt ℝ 1 (famFunHat f) x}

/-- The `x`-derivative of the family member `f` at a point `u` of `ℝ^{p+(n+1)}`. -/
def xDer (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (u : Fin (p + (n + 1)) → ℝ) : ℝ :=
  fderiv ℝ (famFunHat f) u (Pi.single (xDirHat p n) 1)

/-- The relation `2 |a| < |b|` on `ℝ²`, written `4 a² < b²`. -/
def cmpSet : Set (Fin 2 → ℝ) := {u | 4 * u 0 ^ 2 < u 1 ^ 2}

/-! ## 2. The index maps of the ambient `ℝ^{m+n+2}` (`m = p + (n+1)`) -/

/-- The index of `s` inside the block `Fin (n+2)` (which carries `y',s,s'`). -/
def blkS (n : ℕ) : Fin (n + 2) := ⟨n, by omega⟩

/-- The ambient coordinate holding `s`. -/
def sPos (p n : ℕ) : Fin (p + (n + 1) + n + 2) := Fin.natAdd (p + (n + 1)) (blkS n)

/-- The ambient coordinate holding `s'`. -/
def sPos' (p n : ℕ) : Fin (p + (n + 1) + n + 2) :=
  Fin.natAdd (p + (n + 1)) (Fin.last (n + 1))

/-- The coordinates of the first block `w` together with the derivative value `s`. -/
def iwIdx : Fin (p + (n + 1) + 1) → Fin (p + (n + 1) + n + 2) :=
  Fin.snoc (Fin.castAdd (n + 2)) (sPos p n)

/-- The coordinates of `z' = (l,x,y')` inside the ambient: the `(l,x)` part of `w`, then `y'`. -/
def zIdx : Fin (p + (n + 1)) → Fin (p + (n + 1) + n + 2) :=
  Fin.append (fun i : Fin p => Fin.castAdd (n + 2) (Fin.castAdd (n + 1) i))
    (Fin.cons (Fin.castAdd (n + 2) (Fin.natAdd p 0))
      (fun j : Fin n => Fin.natAdd (p + (n + 1)) (Fin.castAdd 2 j)))

/-- The coordinates of `z'` together with the derivative value `s'`. -/
def izIdx : Fin (p + (n + 1) + 1) → Fin (p + (n + 1) + n + 2) :=
  Fin.snoc (zIdx p n) (sPos' p n)

/-- The two coordinates holding `s` and `s'`. -/
def icIdx : Fin 2 → Fin (p + (n + 1) + n + 2) :=
  Fin.cons (sPos p n) (fun _ : Fin 1 => sPos' p n)

/-- The coordinates of the `y'`-block. -/
def cubeIdx : Fin n → Fin (p + (n + 1) + n + 2) :=
  fun j => Fin.natAdd (p + (n + 1)) (Fin.castAdd 2 j)

/-- `zPt p n w y'`: the point obtained from `w` by replacing its `y`-block by `y'`. -/
def zPt (w : Fin (p + (n + 1)) → ℝ) (y' : Fin n → ℝ) : Fin (p + (n + 1)) → ℝ :=
  Fin.append (w ∘ Fin.castAdd (n + 1)) (Fin.cons (w (Fin.natAdd p 0)) y')

/-- The position of `y j` inside the family point `ℝ^{p+(n+1)}`. -/
def yIdx : Fin n → Fin (p + (n + 1)) := fun j => Fin.natAdd p j.succ

/-! ## 3. The selection set -/

/-- `(w,y',s,s')` with `(w,s) ∈ DgSet`, `(z',s') ∈ DgSet`, `y' ∈ openCube n` and `4 s² < s'²`,
where `z'` is `w` with `y`-block replaced by `y'`. -/
def badSet1 (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    Set (Fin (p + (n + 1) + n + 2) → ℝ) :=
  coordPre (iwIdx p n) (DgSet p n f) ∩ coordPre (izIdx p n) (DgSet p n f) ∩
    coordPre (icIdx p n) cmpSet ∩ coordPre (cubeIdx p n) (openCube n)

/-- The points `w` of `ℝ^{p+(n+1)}` which fail the near-maximality condition. -/
def badSet (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (p + (n + 1)) → ℝ) :=
  projN (n + 2) (badSet1 p n f)

/-- The selection set of the `CurveFam` lemma: the `y ∈ openCube n` for which `(l,x,y)` lies in
the interior of the `C¹` locus and is *not* beaten by a factor `2` by any other cube point of
the fibre. -/
def Xset (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (p + (n + 1)) → ℝ) :=
  coordPre (yIdx p n) (openCube n) ∩ LocSet p n f ∩ (badSet p n f)ᶜ

/-! ## 4. Explicit (deliberately loose) format/degree bounds -/

/-- A format bound for `badSet` (linear in `p,n,a1`). -/
def Fbad (p n a1 : ℕ) : ℕ := a1 + 600 * (p + n + 2) + 5000

/-- A degree bound for `badSet`. -/
def Dbad (p n L : ℕ) : ℕ := 2 * L + 600 * (p + n + 2) + 5000

/-- A format bound for `Xset`. -/
def Fx (p n a1 : ℕ) : ℕ := a1 + 1000 * (p + n + 2) + 20000

/-- The constant part of the degree bound of `Xset`. -/
def Cx (p n : ℕ) : ℕ := 1000 * (p + n + 2) + 10000

/-- A degree bound for `Xset`, written as `3 * L` plus a constant. -/
def Dx (p n L : ℕ) : ℕ := 3 * L + Cx p n

end Work.WilkG4c
