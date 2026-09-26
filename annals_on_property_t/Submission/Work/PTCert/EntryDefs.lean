import Submission.Work.PTCert.Glue3

/-!
# PTCert — definitions for the entry formula (`EntryFormula`, glue step (G))

The kernel block entry `kEntry rowTs k ψ i j` unfolds (see `KernelCert.lean`,
`blockRows4`/`blockRow`/`mVal`/`xInfo`) to a sum over the four Klein elements `a < 4` of
a sign times `mVal` applied to the column index of the Klein column `j`.  The plain
(definable) quantities of that unfolding are collected here so that the lemmas establishing
the entry formula can be stated compactly.
-/

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D
open scoped BigOperators

noncomputable section

namespace Work.PTCert

/-- The Klein representatives of the base character `k`. -/
def efKs (k : ℕ) : List ℕ := ksL.getD k []

/-- The Klein column data of the base character `k`. -/
def efYs (k : ℕ) : List ℕ := ysL.getD k []

/-- The Klein action table of the base character `k`, entry `a`. -/
def efKl (k a : ℕ) : ℕ := (klTs.getD k (NT.leaf 0)).get a

/-- Representative number `i` of the base character `k`: `kE k i = rep_{efT k i}`. -/
def efT (k i : ℕ) : ℕ := (ksL.getD k []).getD i 0

/-- Row of the representative `kE k i`. -/
def efRow (k i : ℕ) : ℕ := rinfo (efT k i) / 128

/-- Permutation-table index of the representative `kE k i`. -/
def efIdx (k i : ℕ) : ℕ := rinfo (efT k i) % 128

/-- Permutation code of the representative `kE k i`. -/
def efPc (k i : ℕ) : ℕ := piCodes.getD (efIdx k i) 0

/-- Inverse letter table of the representative `kE k i`. -/
def efTabInv (k i : ℕ) : ℕ := piIT.get (efIdx k i)

/-- Pulled-back character of the representative `kE k i`. -/
def efSp (k i : ℕ) : ℕ := pullS (efPc k i / 32) (Sk k)

/-- Field `a` of the column data `efYs k` of the Klein column `j`. -/
def efField (k j a : ℕ) : ℕ := (ysL.getD k []).getD j 0 >>> (11 * a) &&& 2047

/-- The value of the value table `pv` in row `r` at the code `z`. -/
def efPv (pv : ℕ → ℤ) (r z : ℕ) : ℝ := (pv (keyOf r (labE r z)) : ℝ)

end Work.PTCert
