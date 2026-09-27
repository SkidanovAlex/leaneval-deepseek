import Mathlib
import Submission.Work.Drive.cone_chain
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.SeamMeetDefs


/-!
# The vocabulary of L6: a jointly smooth family of (loop, 3-chain) pairs

Definitions only (see the comment at the end of this file for the statement and the proof plan of the parity
invariance `Work.Drive.odd_ncard_famMeet_iff`).
-/


/-!
## The statement of L6, for the record (it lives as a declaration in
`Submission/Work/Drive/odd_ncard_famMeet_iff.lean`; the definitions above are the vocabulary it uses)

```
theorem Work.Drive.odd_ncard_famMeet_iff (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ⊤ M]
    (L : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 4) → M)
    (hL hN smooth) (hloop : ∀ t ∈ Icc 0 1, L (mk2 t 0) = L (mk2 t 1))
    (hseam : ∀ t x, onSeam x → N (famPt t (seamInv x)) = N (famPt t x))
    (havoid : ∀ p ∈ unitBox 4, famLoop L p = famChain N p → (p 4 = 0 ∨ p 4 = 1) → False)
    (htrans : ∀ p ∈ unitBox 4, famLoop L p = famChain N p →
      Surjective (fun v => d(famLoop L) p v - d(famChain N) p v))      -- NOT the sum of the ranges
    (hface : ∀ p ∈ unitBox 4, famLoop L p = famChain N p → p ∈ unitBoxBdry 4 →
      ∃ i, (p i = 0 ∨ p i = 1) ∧ (∀ j ≠ i, p j ∈ Ioo 0 1) ∧
        ∃ σ, d(famLoop L) p σ = d(famChain N) p σ ∧ σ i ≠ 0)           -- σ = τ (one common vector)
    : Odd ((famMeet L N 0).ncard) ↔ Odd ((famMeet L N 1).ncard)
```

**Review note (kept because the first draft was wrong).**  `famLoop L` and `famChain N` live on the
*same* five-box, so the transversality is the surjectivity of `d(famLoop) - d(famChain)`, not the
(sufficient only for two different domains) `range ⊔ range = ⊤`; and the face condition must ask for a
single vector `σ = τ` tangent to the meet curve — with `σ ≠ τ` allowed it is vacuous on the `p 2, p 3,
p 4` faces, because `d(famLoop)` kills those directions.

**Proof plan.**  `Submission.Work.Drive.transverse_inter_boundary_parity` is the `(2,3)` engine; L6 is
its `(5,4)` analogue with `Submission.Drive.ParityProp` (`m = 4`, proved as `Work.Drive.boxParity`,
dimension-generic) for the charted difference map of the pair `(famLoop, famChain)` on the five-box.
The boundary of the meet set is split by which of the five coordinates is on a face (`hface`: exactly
one): the `p 0`-faces are `famMeet L N 0` and `famMeet L N 1`; the `p 1`-faces are paired by `hloop`;
the `p 4`-faces are killed by `havoid`; the `p 2`/`p 3`-faces are paired by `hseam` via `seamInv`.  The
pairings are fibrewise in `p 0`, so they preserve the `p 0`-faces.  This is the joint form of
`Work.Drive.odd_ncard_loopFamMeet_iff` (the loop half, proved) and
`Work.Drive.even_ncard_tauMeet_add_tauMeet` (the chain half, proved).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- The chain parameter `(t, x) ∈ ℝ⁴` obtained by prefixing the family parameter `t` to `x ∈ ℝ³`. -/
def famPt (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (Fin.cons t x.ofLp)

@[simp] lemma famPt_apply_zero (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : famPt t x 0 = t := by
  simp [famPt]

/-- The tuple `(a, b, c) ∈ ℝ³`. -/
def famT3 (a b c : ℝ) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![a, b, c]

variable {M : Type*} [TopologicalSpace M]

/-- **The loop side of the family, on the five-box**: `p ↦ L (p 0, p 1)`. -/
def famLoop (L : EuclideanSpace ℝ (Fin 2) → M) :
    EuclideanSpace ℝ (Fin 5) → M := fun p => L (mk2 (p 0) (p 1))

/-- **The chain side of the family, on the five-box**: `p ↦ N (p 0, p 2, p 3, p 4)`. -/
def famChain (N : EuclideanSpace ℝ (Fin 4) → M) :
    EuclideanSpace ℝ (Fin 5) → M := fun p => N (famPt (p 0) (famT3 (p 2) (p 3) (p 4)))

/-- **The family meet set at the parameter `t`**: the meets of the `t`-th loop of the family with the
`t`-th chain, inside the five-box. -/
def famMeet {M : Type*} [TopologicalSpace M]
    (L : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 4) → M) (t : ℝ) :
    Set (EuclideanSpace ℝ (Fin 5)) :=
  {p | p ∈ Submission.Drive.unitBox 4 ∧ p 0 = t ∧ famLoop L p = famChain N p}


end Work.Drive
