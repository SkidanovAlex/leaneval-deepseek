import Submission.CertJPsiTabT
import Submission.CertJLookup
import Submission.CertJTabs
import Submission.CertPsiAll
import Submission.CertSsum49All

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# The table evaluation of the certificate's `J`-form

The `J`-form of the certificate,

  `∑_i J_i(F) = 50·K²·(∑_{j,j'} ∑_{v,v'} c_j c_{j'} κ_jv κ_{j'v'} Ssum(β_{jv},β_{j'v'},49)
      certJPsiN(jv,j'v')) / Λ_J`,

is evaluated here as a *table* computation.  Writing `β(j,v) = eraseOne (α_j) v` and
`ã(j,v) = a_j+v+1`, the entries of the inner double sum are grouped by `(β,ã)` (the accumulated
weights `gPosL`/`gNegL`) and the two nontrivial factors are replaced by table lookups:

* `Ssum β β' 49 = mc 49 (mult β') · unpack (packedRowAt 49 (mult β')) (mult β)`, read off the
  verified row table `ssumTable49L` (zipped with `certGroupSigs`), and
* `certJPsiN = psiTab[51·N + L]` with `N = ã+ã'`, `L = |β|+|β'|`, read off the transposed
  kernel table `psiTabTN`.

All arithmetic in the inner contraction is carried out in `ℕ` (the sign split of the weights is
encoded by the four blocks `(pos,pos) + (neg,neg) - (pos,neg) - (neg,pos)`), which is essential:
the kernel's `ℤ` arithmetic is two orders of magnitude slower than its `ℕ` arithmetic.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- One inner contraction term (in `ℕ`, the lookups being `psiTabTN` reads). -/
def jt (row : List ℕ) (a b : ℕ × ℕ) : ℕ := a.2 * b.2 * (nthD row (a.1 + b.1) 0)

/-- One sign block of the inner contraction. -/
def jb (row : List ℕ) (g g' : List (ℕ × ℕ)) : ℕ :=
  List.sum (List.map (fun a => List.sum (List.map (fun b => jt row a b) g')) g)

/-- The inner contraction of a pair of signature groups, with the sign split and the two
cleared factors `mc 49 (mult β')` and the `ssumTable49L` row entry. -/
def jp (row : List ℕ) (T mc : ℕ) (gp gn gq gr : List (ℕ × ℕ)) : ℤ :=
  (mc : ℤ) * (T : ℤ) *
    (((jb row gp gq + jb row gn gr : ℕ) : ℤ) - ((jb row gp gr + jb row gn gq : ℕ) : ℤ))

/-- The outer data of the `J`-evaluation: signature, its `ssumTable49L` row, its positive and
negative weight groups and `mc 49 (mult β)`. -/
def outerJ : List (List ℕ × (List ℕ × (List (ℕ × ℕ) × (List (ℕ × ℕ) × ℕ)))) :=
  certGroupSigs.zip (ssumTable49L.zip (gPosL.zip (gNegL.zip mcL)))

/-- One outer group of the `J`-evaluation. -/
def innerJ (o : List ℕ × (List ℕ × (List (ℕ × ℕ) × (List (ℕ × ℕ) × ℕ)))) : ℤ :=
  List.sum (List.map (fun i => List.sum (List.map (fun row =>
      jp row i.2.1 o.2.2.2.2 i.2.2.1 i.2.2.2 o.2.2.1 o.2.2.2.1)
    [nthDl psiTabTN (o.1.sum + i.1.sum) []]))
    (certGroupSigs.zip (o.2.1.zip (gPosL.zip gNegL))))

/-- **The table evaluation of the `J`-form of the certificate.** -/
def certJval : ℤ := List.sum (List.map innerJ outerJ)

/-- The `c`-th chunk of the evaluation (`8` outer groups). -/
def chunkJ (c : ℕ) : ℤ := List.sum (List.map innerJ (List.take 8 (List.drop (8 * c) outerJ)))

end Commons.NumberTheory.MaynardSieve
