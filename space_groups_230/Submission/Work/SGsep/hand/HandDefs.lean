import Mathlib
import Submission.Work.SG.SGsepDefs

/-!
# Handedness certificates: the vocabulary

This module fixes the definitions used by the `hand_separates` development.  Everything is
phrased with the flat integer types `Data.M3` / `Data.V3` of
`Submission.Work.SG.Data.Core` (the level at which the generated certificates are checked) and
with the integer matrices `IMat` / vectors `IVec` of `Submission.Work.SG.Defs` (the level at
which the group-theoretic statements live).

The central objects are

* `V3.cross` – the cross product of two integer vectors;
* `V3.gcdV` – the (positive) gcd of the three entries of a vector;
* `V3.Prim` – primitivity, in Bézout form `∃ β, β·v = 1`;
* `M3.row` – a row of a flat matrix;
* `M3.skew z` – the matrix of `x ↦ z × x`;
* `M3.form A z = Aᵀ S - S A` (`S = skew z`) – twice the symmetric matrix of the quadratic form
  `y ↦ det(y, A y, z)`;
* `M3.psd` – "positive semidefinite" tested by the seven principal minors;
* `AxisW` / `axisTab` – the generated, kernel-checked axis data of the `652` rotations of the
  `230` representatives.
-/

namespace Work.SGsep.Hand

open Work.SG

namespace Data

open Work.SG.Data

/-- Cross product of two integer vectors. -/
def V3.cross (u v : V3) : V3 :=
  ⟨u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x⟩

/-- Coordinatewise negation. -/
def V3.negate (v : V3) : V3 := ⟨-v.x, -v.y, -v.z⟩

/-- The positive gcd of the three entries. -/
def V3.gcdV (v : V3) : Nat := Nat.gcd (Nat.gcd v.x.natAbs v.y.natAbs) v.z.natAbs

/-- `v` is primitive: some integer linear functional takes the value `1` on it. -/
def V3.Prim (v : V3) : Prop := ∃ β : V3, V3.dot β v = 1

/-- A row of a flat matrix (index `0, 1, 2`). -/
def M3.row (A : M3) (j : Nat) : V3 :=
  if j = 0 then ⟨A.a, A.b, A.c⟩ else if j = 1 then ⟨A.d, A.e, A.f⟩ else ⟨A.g, A.h, A.i⟩

/-- Transpose. -/
def M3.trans (A : M3) : M3 := ⟨A.a, A.d, A.g, A.b, A.e, A.h, A.c, A.f, A.i⟩

/-- Coordinatewise scalar multiple. -/
def M3.smulM (c : Int) (A : M3) : M3 :=
  ⟨c * A.a, c * A.b, c * A.c, c * A.d, c * A.e, c * A.f, c * A.g, c * A.h, c * A.i⟩

/-- The skew matrix of `x ↦ z × x`. -/
def M3.skew (z : V3) : M3 := ⟨0, -z.z, z.y, z.z, 0, -z.x, -z.y, z.x, 0⟩

/-- `Aᵀ S - S A` with `S = skew z`; twice the symmetric matrix of `y ↦ det(y, A y, z)`. -/
def M3.form (A : M3) (z : V3) : M3 :=
  M3.sub (M3.mul (M3.trans A) (M3.skew z)) (M3.mul (M3.skew z) A)

/-- Positive semidefiniteness, tested by the seven principal minors. -/
def M3.psd (N : M3) : Bool :=
  0 ≤ N.a && 0 ≤ N.e && 0 ≤ N.i &&
  0 ≤ N.a * N.e - N.b * N.d && 0 ≤ N.a * N.i - N.c * N.g && 0 ≤ N.e * N.i - N.f * N.h &&
  0 ≤ M3.det N

/-- Symmetry of a flat matrix. -/
def M3.Symm (N : M3) : Bool := (N.b == N.d) && (N.c == N.g) && (N.f == N.h)

/-- The element of representative `k` with table index `i` (flat). -/
def A3 (k : Fin 230) (i : Nat) : M3 := (repArith k.val).elems.getD i M3.one

/-- The same element, as an integer matrix. -/
def Ah (k : Fin 230) (i : Nat) : IMat := (A3 k i).toIMat

/-- The row `j` of `A - 1`, as an integer vector. -/
def rowOf (A : M3) (j : Nat) : IVec := (M3.row (M3.sub A M3.one) j).toFun

/-- A checked axis datum: primitive axis vector `z`, cross-product witness `p`, `q`, `m`, and
the sign `eps` making `eps • form A z` positive semidefinite. -/
structure AxisW where
  z : V3
  p : Nat
  q : Nat
  m : Int
  eps : Int
deriving DecidableEq, Repr, Inhabited

/-- The part of the check that does not involve `det A`/`ord A`. -/
def AxisW.chkCore (A : M3) (w : AxisW) : Bool :=
  (!(w.m == 0)) && (M3.mulV (M3.sub A M3.one) w.z == V3.zero) && (V3.gcdV w.z == 1) &&
  (V3.cross (M3.row (M3.sub A M3.one) w.p) (M3.row (M3.sub A M3.one) w.q) ==
    V3.smul w.m w.z) &&
  (w.eps == 1 || w.eps == -1) && M3.Symm (M3.form A w.z) &&
  M3.psd (M3.smulM w.eps (M3.form A w.z))

/-- The full check of one axis entry: `det A = 1`, `3 ≤ ord A`, and the core conditions. -/
def AxisW.chk (A : M3) (w : AxisW) : Bool :=
  (M3.det A == 1) && decide (3 ≤ M3.ord A) && w.chkCore A

end Data
end Work.SGsep.Hand
