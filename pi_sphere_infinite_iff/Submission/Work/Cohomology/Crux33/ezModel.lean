import Mathlib

/-!
# The `(3,3)` Eilenberg–Zilber shuffle identity, as a kernel-computable finite check

The maximal simplices of the standard triangulation of the prism `Δ³ × Δ³` are the `(3,3)`
shuffles: the lattice paths from `(0,0)` to `(3,3)`.  Encoding a path by its list of steps
(`true` = an `N`-step, `false` = an `E`-step), the vertices of the path are obtained by a left
fold (`scan`), the Eilenberg–Zilber sign is `(-1)^{#(N-step before E-step)}` (`shufSignL`), and
the `i`-th face of the prism simplex is obtained by deleting the `i`-th vertex (`List.eraseIdx`).

The main theorem `modelIdent33` says that the boundary of the sum of the twenty prism simplices
equals the sum of the pushed-forward `(2,3)`- and `(3,2)`-prism chains, coefficient by
coefficient.  This is a finite computation (the only genuinely combinatorial content of the
Eilenberg–Zilber shuffle map in bidegree `(3,3)`); we verify it by kernel reduction
(`decide`), which is possible because every ingredient is `List`-valued (no `Finset` sums or
`Finsupp` whose `DecidableEq` instances get stuck on quotient terms).
-/

namespace Work.Cohomology.Crux33

/-! ## The list model of a staircase path -/

/-- Scan a list of steps (`true` = `N`, `false` = `E`) into the list of vertices visited. -/
def scan (steps : List Bool) : List (ℕ × ℕ) :=
  steps.scanl (fun (acc : ℕ × ℕ) s => if s then (acc.1, acc.2 + 1) else (acc.1 + 1, acc.2))
    (0, 0)

/-- The Eilenberg–Zilber sign of a shuffle: `(-1)` raised to the number of pairs
(an `N`-step before an `E`-step). -/
def shufSignL (steps : List Bool) : ℤ :=
  (-1 : ℤ) ^ ((steps.foldl (fun (acc : ℕ × ℕ) s =>
    if s then (acc.1, acc.2 + 1) else (acc.1 + acc.2, acc.2)) (0, 0)).1)

/-- All shuffle step-lists of length `n` with exactly `q` `N`-steps. -/
def shufs (n q : ℕ) : List (List Bool) :=
  ((List.finRange n).sublists.filter (fun s => s.length = q)).map
    (fun s => List.ofFn (fun i : Fin n => decide (i ∈ s)))

/-- The `(3,3)` shuffles. -/
def sh33 : List (List Bool) := shufs 6 3

/-- The `(2,3)` shuffles. -/
def sh23 : List (List Bool) := shufs 5 3

/-- The `(3,2)` shuffles. -/
def sh32 : List (List Bool) := shufs 5 2

/-- Push a face of the prism `Δ² × Δ³` into `Δ³ × Δ³` along the coface `δ_j` on the first
factor. -/
def shiftA (j : ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  l.map (fun p => (if p.1 < j then p.1 else p.1 + 1, p.2))

/-- Push a face of the prism `Δ³ × Δ²` into `Δ³ × Δ³` along the coface `δ_j` on the second
factor. -/
def shiftB (j : ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  l.map (fun p => (p.1, if p.2 < j then p.2 else p.2 + 1))

/-- The coefficient, at the face `z`, of the boundary of the `(3,3)` prism chain. -/
def mdlhs (z : List (ℕ × ℕ)) : ℤ :=
  List.sum (sh33.map (fun st => List.sum ((List.finRange 7).map (fun i : ℕ =>
    if (scan st).eraseIdx i = z then shufSignL st * (-1 : ℤ) ^ i else 0))))

/-- The coefficient, at the face `z`, of the pushed-forward `(2,3)`- and `(3,2)`-prism chains. -/
def mdhrs (z : List (ℕ × ℕ)) : ℤ :=
  List.sum ((List.finRange 4).map (fun j =>
      (-1 : ℤ) ^ j * List.sum (sh23.map (fun st =>
        if shiftA j (scan st) = z then shufSignL st else 0))))
  + (-1 : ℤ) ^ 3 * List.sum ((List.finRange 4).map (fun j =>
      (-1 : ℤ) ^ j * List.sum (sh32.map (fun st =>
        if shiftB j (scan st) = z then shufSignL st else 0))))

/-- The faces occurring in the `(3,3)` prism chain. -/
def faces33 : List (List (ℕ × ℕ)) :=
  List.flatten (sh33.map (fun st => (List.finRange 7).map (fun i : ℕ => (scan st).eraseIdx i)))

/-- The pushed-forward `(2,3)` faces. -/
def faces23 : List (List (ℕ × ℕ)) :=
  List.flatten ((List.finRange 4).map (fun j => sh23.map (fun st => shiftA j (scan st))))

/-- The pushed-forward `(3,2)` faces. -/
def faces32 : List (List (ℕ × ℕ)) :=
  List.flatten ((List.finRange 4).map (fun j => sh32.map (fun st => shiftB j (scan st))))

/-- **The `(3,3)` prism identity, coefficient by coefficient (finite check).** -/
theorem modelIdent33_all :
    faces33.all (fun z => decide (mdlhs z = mdhrs z)) = true := by
  decide

/-- The pointwise form on the faces. -/
theorem mdlhs_eq_mdhrs_of_mem {z : List (ℕ × ℕ)} (hz : z ∈ faces33) : mdlhs z = mdhrs z :=
  of_decide_eq_true ((List.all_eq_true.mp modelIdent33_all) z hz)

end Work.Cohomology.Crux33
