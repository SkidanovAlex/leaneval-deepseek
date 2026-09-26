import Submission.Work.SG.Defs

/-! Flat integer types and certificate checkers for the generated space-group data.
Everything here is computable and designed for kernel evaluation (`decide +kernel`):
`Int` fields, `Nat` bitmasks, `List` lookups. GENERATED data lives in the sibling modules;
this file is hand-written. -/

namespace Work.SG.Data

/-- A `3 × 3` integer matrix, row-major fields. -/
structure M3 where
  (a b c d e f g h i : Int)
deriving DecidableEq, Repr, Inhabited

/-- An integer 3-vector. -/
structure V3 where
  (x y z : Int)
deriving DecidableEq, Repr, Inhabited

namespace V3
def zero : V3 := ⟨0, 0, 0⟩
def add (u v : V3) : V3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
def sub (u v : V3) : V3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩
def smul (k : Int) (v : V3) : V3 := ⟨k * v.x, k * v.y, k * v.z⟩
def dot (u v : V3) : Int := u.x * v.x + u.y * v.y + u.z * v.z
/-- All coordinates divisible by `m`. -/
def dvd (m : Int) (v : V3) : Bool := v.x % m == 0 && v.y % m == 0 && v.z % m == 0
def ediv (v : V3) (m : Int) : V3 := ⟨v.x / m, v.y / m, v.z / m⟩
def emod (v : V3) (m : Int) : V3 := ⟨v.x % m, v.y % m, v.z % m⟩
def toList (v : V3) : List Int := [v.x, v.y, v.z]
/-- The integer vector as a function `Fin 3 → ℤ`. -/
def toFun (v : V3) : Fin 3 → ℤ := ![v.x, v.y, v.z]
end V3

namespace M3
def one : M3 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩
def mul (A B : M3) : M3 :=
  ⟨A.a * B.a + A.b * B.d + A.c * B.g, A.a * B.b + A.b * B.e + A.c * B.h,
    A.a * B.c + A.b * B.f + A.c * B.i,
   A.d * B.a + A.e * B.d + A.f * B.g, A.d * B.b + A.e * B.e + A.f * B.h,
    A.d * B.c + A.e * B.f + A.f * B.i,
   A.g * B.a + A.h * B.d + A.i * B.g, A.g * B.b + A.h * B.e + A.i * B.h,
    A.g * B.c + A.h * B.f + A.i * B.i⟩
def mulV (A : M3) (v : V3) : V3 :=
  ⟨A.a * v.x + A.b * v.y + A.c * v.z, A.d * v.x + A.e * v.y + A.f * v.z,
   A.g * v.x + A.h * v.y + A.i * v.z⟩
def add (A B : M3) : M3 :=
  ⟨A.a + B.a, A.b + B.b, A.c + B.c, A.d + B.d, A.e + B.e, A.f + B.f, A.g + B.g, A.h + B.h, A.i + B.i⟩
def sub (A B : M3) : M3 :=
  ⟨A.a - B.a, A.b - B.b, A.c - B.c, A.d - B.d, A.e - B.e, A.f - B.f, A.g - B.g, A.h - B.h, A.i - B.i⟩
def neg (A : M3) : M3 := ⟨-A.a, -A.b, -A.c, -A.d, -A.e, -A.f, -A.g, -A.h, -A.i⟩
def det (A : M3) : Int :=
  A.a * (A.e * A.i - A.f * A.h) - A.b * (A.d * A.i - A.f * A.g) + A.c * (A.d * A.h - A.e * A.g)
def trace (A : M3) : Int := A.a + A.e + A.i
/-- Columns `A e₀, A e₁, A e₂`. -/
def cols (A : M3) : List V3 := [⟨A.a, A.d, A.g⟩, ⟨A.b, A.e, A.h⟩, ⟨A.c, A.f, A.i⟩]
/-- `A` from its three columns. -/
def ofCols (u v w : V3) : M3 := ⟨u.x, v.x, w.x, u.y, v.y, w.y, u.z, v.z, w.z⟩
def pow (A : M3) : Nat → M3
  | 0 => one
  | k + 1 => mul A (pow A k)
/-- `∑_{e < k} Aᵉ`. -/
def normSum (A : M3) : Nat → M3
  | 0 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | k + 1 => add (pow A k) (normSum A k)
/-- Order of `A` if it is at most 12, else `0`. -/
def ord (A : M3) : Nat :=
  ((List.range 12).find? fun k => pow A (k + 1) == one).map (· + 1) |>.getD 0
/-- The flat row-major entries (the `Defs.lean` convention). -/
def toList (A : M3) : List Int := [A.a, A.b, A.c, A.d, A.e, A.f, A.g, A.h, A.i]
/-- The integer matrix (bridge to `IMat`). -/
def toIMat (A : M3) : IMat := !![A.a, A.b, A.c; A.d, A.e, A.f; A.g, A.h, A.i]
end M3

/-- `∑ cᵢ gᵢ` (extra coefficients / generators are ignored). -/
def lin : List V3 → List Int → V3
  | g :: gs, c :: cs => V3.add (V3.smul c g) (lin gs cs)
  | _, _ => V3.zero

/-- Certificate for membership / non-membership of a vector in the `ℤ`-span of a list:
`yes cs` : `v = ∑ cᵢ gᵢ`; `no φ m` : `m ≥ 2`, `φ·gᵢ ≡ 0 (mod m)` for all `i`, `φ·v ≢ 0 (mod m)`. -/
inductive SpanCert
  | yes (cs : List Int)
  | no (φ : V3) (m : Nat)
deriving Repr, Inhabited

/-- The membership bit the certificate claims. -/
def SpanCert.bit : SpanCert → Bool
  | .yes _ => true
  | .no _ _ => false

/-- Check a span certificate for `v` against generators `gs`. -/
def SpanCert.chk (gs : List V3) (v : V3) : SpanCert → Bool
  | .yes cs => cs.length == gs.length && lin gs cs == v
  | .no φ m => 2 ≤ m && gs.all (fun g => V3.dot φ g % (m : Int) == 0) && V3.dot φ v % (m : Int) != 0

/-- Primes that can divide an element order or `H¹` order here (all orders are `≤ 48`). -/
def smallPrimes : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

/-- Prime divisors of `o` (for `o ≤ 48`). -/
def primesOf (o : Nat) : List Nat := smallPrimes.filter fun p => o % p == 0

/-- Integer vector of length `3k` as `k` blocks of `V3`. -/
def blocks : List Int → List V3
  | x :: y :: z :: r => ⟨x, y, z⟩ :: blocks r
  | _ => []

/-- Concatenate blocks. -/
def unblocks (vs : List V3) : List Int := vs.flatMap V3.toList

/-- Dot product of integer lists. -/
def ldot (u v : List Int) : Int := (List.zipWith (· * ·) u v).sum

end Work.SG.Data

namespace Work.SG.Data

/-- Element table of one arithmetic class, in BFS order from the identity:
`elems[0] = 1`, `elems[i+1] = gens[par[i].1] * elems[par[i].2]` with `par[i].2 ≤ i`;
`mulGen[g][i]` = index of `gens[g] * elems[i]`; `genIdx[g]` = index of `gens[g]`. -/
structure ArithData where
  n : Nat
  gens : List M3
  elems : List M3
  par : List (Nat × Nat)
  mulGen : List (List Nat)
  genIdx : List Nat
deriving Repr, Inhabited

end Work.SG.Data

namespace Work.SG.Data

/-- Normaliser element taking an `H¹` representative (or a representative `k₁`) to the
representative `k`: `U` (with inverse `Uinv`), `σ` (the translation is `s = σ / n²`), and
`img[i]` = index of `U · elems[i] · U⁻¹`. -/
structure ConjCert where
  k : Nat
  U : M3
  Uinv : M3
  sig : V3
  img : List Nat
deriving Repr, Inhabited

/-- Cohomology certificate of one arithmetic class (`k` generators, coordinates `y ∈ ℤ^{3k}` =
`n · τ(generators)`):
* `H` — upper-echelon basis (`H[c][c] > 0`, zeros before `c`) of the solution lattice
  `S = {y : R y ≡ 0 (mod n)}` of the relation rows `R = relRows`;
* `wc[c]` — sparse integer combination of relation rows whose sum `w` has `w[q] ≡ 0 (mod n)`
  for `q > c` and `w[c] ≡ n / H[c][c]` (so `y ∈ S`, `y_{<c} = 0` ⇒ `H[c][c] ∣ y_c`);
* `Bl` — upper-echelon basis of the coboundary lattice, each row with `σ ∈ ℤ³` such that
  `(1 - g)σ ≡ 0 (mod n)` and `row ≡ ((1 - g)σ / n)_g (mod n)`;
* `reps` — the `H¹` representatives (reduced modulo `Bl`), `reps[0] = 0`;
* `add[h][c]` — index of `reduce (reps[h] + H[c])`;
* `targets[h]` — a `det 1` normaliser certificate from `reps[h]` to a space-group representative. -/
structure CohomData where
  n : Nat
  H : List (List Int)
  wc : List (List (Nat × Int))
  Bl : List (List Int × V3)
  reps : List (List Int)
  add : List (List Nat)
  targets : List ConjCert
deriving Repr, Inhabited

end Work.SG.Data

namespace Work.SG.Data

/-- Order certificate for the intrinsic translation `v_A = N_A τ(A)` of element `i` of rep `k`:
`o · v_A ∈ N_A ℤ³` (`yes` coefficients over the columns of `N_A`), and for each prime `p ∣ o`
(in `primesOf o` order) a non-membership certificate `(φ, m)` for `(o / p) · v_A`. -/
structure ElemCert where
  o : Nat
  yes : List Int
  nos : List (V3 × Nat)
deriving Repr, Inhabited

/-- "All columns of `X` lie in the span of `Y`": `yes` = coefficients for each column;
`no col φ m` = column `col` is not in the span. -/
inductive TfCert
  | yes (cs : List (List Int))
  | no (col : Nat) (φ : V3) (m : Nat)
deriving Repr, Inhabited

def TfCert.bit : TfCert → Bool
  | .yes _ => true
  | .no _ _ _ => false

/-- Pair-feature certificate for elements `(i, j) = (A, B)`:
`fix` : `(B - 1) v_A ∈ span((B - 1) N_A)` (⇔ `v_A ∈ Λ^B + N_A ℤ³`);
`afix` : the same with `B + 1`;
`tf` : the four τ-free bits `cols(A∓1) ⊆ span cols(B∓1)` in the order
`(A-1,B-1), (A+1,B+1), (A-1,B+1), (A+1,B-1)`. -/
structure PairCert where
  i : Nat
  j : Nat
  fix : SpanCert
  afix : SpanCert
  tf : List TfCert
deriving Repr, Inhabited

/-- Screw-handedness certificate for a rotation `A` (`det 1`, order `ord ≥ 3`): primitive
oriented axis `c` (`(A-1)c = 0`, `β·c = 1`, `det(e_q, A e_q, c) > 0`), `N_A = c wᵀ`,
`h = gcd w` (`h ∣ wᵢ`, `β₂·(w/h) = 1`), and `v_A = j c`. Value `(ord, h, j mod h)`. -/
structure HandCert where
  ord : Nat
  c : V3
  beta : V3
  q : Nat
  w : V3
  h : Nat
  beta2 : V3
  j : Int
deriving Repr, Inhabited

/-- Order of `[τ]` in `H¹`: `σ` with `(1 - g)σ ≡ o n z_g (mod n²)` for all generators, and for
each prime `p ∣ o` an integer left-kernel vector `u` (`∑_g u_gᵀ (1 - g) = 0`) with
`∑_g u_g · (o/p) z_g ≢ 0 (mod n)`. -/
structure SymCert where
  o : Nat
  sig : V3
  nos : List (List Int)
deriving Repr, Inhabited

/-- One separation certificate for representatives `k < l` of the same arithmetic class. -/
inductive Sep
  | elem (k l : Nat) (det tr : Int) (o : Nat)
  | sym (k l : Nat) (a b : SymCert)
  | hand (k l : Nat) (ord h : Nat) (jm : Int) (ta tb : List (Option HandCert))
  | pair (k l : Nat) (dA trA : Int) (oA : Nat) (dB trB : Int) (oB : Nat) (bits : List Bool)
      (la lb : List PairCert)
deriving Repr, Inhabited

end Work.SG.Data

namespace Work.SG.Data

/-- Join certificate for a listed subgroup `K` (bitmask) and an element `g ∉ K`:
`full t cos` — the listed subgroup `t` contains `K ∪ {g}`, and `t ⊆ ⋃ K·rᵢ` where `r₀ = 1`,
`r_{q+1} = r_{cos[q].1} · y` with `y = cos[q].2 ∈ K ∪ {g}`;
`ref g₀ k₁ k₂` — `g = k₁ g₀ k₂` with `k₁, k₂ ∈ K` and the certificate of `g₀` is `full`. -/
inductive JoinCert
  | full (t : Nat) (cos : List (Nat × Nat))
  | ref (g0 k1 k2 : Nat)
deriving Repr, Inhabited

/-- Conjugation of a listed subgroup onto an arithmetic representative:
`U · stab[x] · Uinv = arithData[j].elems[img[q]]` for the `q`-th element `x` of the subgroup. -/
structure SubConj where
  j : Nat
  U : M3
  Uinv : M3
  img : List Nat
deriving Repr, Inhabited

/-- Selling data for one support graph: coset-minimal vectors, the stabiliser (in candidate
order), its multiplication table, the identity index, all subgroups (bitmasks over `stab`),
join certificates `joins[s][g]` (`none` iff `g ∈ subs[s]`), and conjugators. -/
structure SellData where
  vecs : List V3
  stab : List M3
  mul : List (List Nat)
  one : Nat
  subs : List Nat
  joins : List (List (Option JoinCert))
  conj : List SubConj
deriving Repr, Inhabited

end Work.SG.Data
