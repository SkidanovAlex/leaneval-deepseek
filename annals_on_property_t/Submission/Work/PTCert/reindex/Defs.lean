import Mathlib
import Submission.Work.PTCert.GlueDefs

/-!
# Reindexing toolkit for `reindexEntryRow` (definitions)

Codes of `5`-bit sign vectors (`scOf`/`sbit`/`zOfSc`, `Submission.PTCert`), re-read as
`ZMod 2`-valued functions on `Fin 5`.  This file collects the code-level operations needed to
reindex the code sum of `fourierEntryRow` against the row table `rowTs`:

* `encV v` — the binary code `∑ i, v i · 2^i` of a `ZMod 2`-vector `v`;
* `bxor a b` — the code of the sum of the vectors coded by `a` and `b` (i.e. `Nat.xor` on codes);
* `permCode q sc` — the code whose `i`-th bit is the `(q i)`-th bit of `sc`;
* `phiC q c0` — the reindexing map `sc ↦ bxor (permCode q sc) c0` of the code sum.

The main file `Submission/Work/PTCert/reindexEntryRow.lean` uses these with `q = permOfPC (efPc k i / 32)`
and `c0 = (em (actC cmT (efTabInv k i) (rp Ta)) - 1) % 32`.
-/

namespace Work.PTCert

open Submission.PTCert

/-- The binary code of a `ZMod 2`-vector on `Fin 5`: the sum of `2^i` over the coordinates `i`
where `v i = 1`.  This is the inverse of `zOfSc` on codes `< 32`. -/
def encV (v : Fin 5 → ZMod 2) : ℕ := scOf (zBool v)

/-- The code of the sum of the sign vectors coded by `a` and `b` (bitwise xor of the codes). -/
def bxor (a b : ℕ) : ℕ := encV (zOfSc (m := 5) a + zOfSc (m := 5) b)

/-- The code whose `i`-th bit is the `(q i)`-th bit of `sc`. -/
def permCode (q : Equiv.Perm (Fin 5)) (sc : ℕ) : ℕ := encV (fun i => zOfSc (m := 5) sc (q i))

/-- The reindexing map of the code sum: `Φ sc = (permCode q sc) ⊕ c0`. -/
def phiC (q : Equiv.Perm (Fin 5)) (c0 sc : ℕ) : ℕ := bxor (permCode q sc) c0

end Work.PTCert
