import Mathlib
import Submission.Work.KT.Idx.PenDefs
import Submission.Work.KT.Fund.Laurent

/-!
# `Work.KT.Idx.WPen` — the W linearisation of a polynomial clutching function

The linearisation used for the Bott index (Hatcher, *Vector Bundles and K-Theory*, Prop. 2.6, in
the "W" form): for a coefficient sequence `b : Fin (d+1) → Mₙ(C(X, ℂ))` of a polynomial clutching
function `q_b(z) = Σ_j b_j z^j` on the block index `Fin (d+1) × Fin n`,

* `wPenA` is the identity in all blocks except the last (the `z`-coefficient);
* `wPenB b` is `-1` on the superdiagonal of the block index and has the coefficient matrices
  `b_j` in the last block row (the constant coefficient);

so that `M_b(z) = z • wPenA + wPenB b` is Hatcher's companion pencil.  Its two structural
properties — both stated below as the lemmas `wPen_kernel`/`wPen_det` to be proved — are

* **kernel recursion**: `M_b(z) v = 0` for `z ≠ 0` forces `v_{i+1} = z v_i`, so the kernel of
  `M_b(z)` is `{v : v_i = z^i v_0, q_b(z) v_0 = 0}`, and `M_b(z)` is invertible exactly when
  `q_b(z)` is;
* hence `det (M_b(z)) = det (q_b(z))`, so the *roots* of the pencil are the zeros of `q_b`.

`Indexing`.  The reindexed versions `wPenAf`/`wPenBf` live on `Fin ((d+1) * n)`, which is the form
`matPenProj` wants.

`Padding`.  For a Laurent matrix `P` of degree bound `m` the coefficient sequence of `z^m P` has
`2m+1` entries; going from `m` to `m+1` replaces `b` by `(0, b_0, …, b_{2m}, 0)`, i.e. one
"prepend" (`b ↦ (0,b)`, polynomial `z q_b`, adding `cls ⟨n, 1⟩` to the index) and one "append"
(`b ↦ (b,0)`, the same polynomial, not changing the index).  These are the two statements
`Work.Idx.wPen_append` and `Work.Idx.wPen_prepend`; together they give the independence of the
Bott index of the degree bound `m`.
-/

namespace Work.KT.Idx

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

set_option linter.unusedSectionVars false

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The `z`-coefficient of the W linearisation: the identity in all blocks except the last. -/
def wPenA (n d : ℕ) : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ) :=
  fun i j => if i.1 = j.1 ∧ (i.1 : ℕ) ≠ d then (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) i.2 j.2
    else 0

/-- The constant part of the W linearisation: `-1` on the superdiagonal of the block index, and the
coefficient matrices in the last block row. -/
def wPenB (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ) :=
  fun i j =>
    if (i.1 : ℕ) + 1 = (j.1 : ℕ) then
      (if (i.1 : ℕ) = d then b j.1 i.2 j.2
        else -(1 : Matrix (Fin n) (Fin n) C(X, ℂ)) i.2 j.2)
    else if (i.1 : ℕ) = d then b j.1 i.2 j.2
    else 0

/-- The W linearisation reindexed to `Fin ((d+1)*n)`. -/
def wPenAf (n d : ℕ) : Matrix (Fin ((d + 1) * n)) (Fin ((d + 1) * n)) C(X, ℂ) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (wPenA X n d)

/-- The constant part of the W linearisation, reindexed to `Fin ((d+1)*n)`. -/
def wPenBf (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin ((d + 1) * n)) (Fin ((d + 1) * n)) C(X, ℂ) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (wPenB X n d b)

/-- The pencil `z ↦ z • wPenA + wPenB b`, reindexed. -/
def wPenPencil (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (z : ℂ) :
    Matrix (Fin ((d + 1) * n)) (Fin ((d + 1) * n)) C(X, ℂ) :=
  z • wPenAf X n d + wPenBf X n d b

/-- The polynomial carried by a coefficient sequence. -/
def polyOf (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
  fun a c => ∑ j : Fin (d + 1),
    ((b j a c).comp (ContinuousMap.fst : C(X × Sph ℂ, X))) *
      ((Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) ^ (j : ℕ))

/-- Append a zero coefficient: `b ↦ (b_0, …, b_d, 0)`, i.e. the same polynomial, one more block. -/
def appSeq {n d : ℕ} (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Fin (d + 2) → Matrix (Fin n) (Fin n) C(X, ℂ) :=
  fun j => if h : (j : ℕ) < d + 1 then b ⟨j, h⟩ else 0

/-- Prepend a zero coefficient: `b ↦ (0, b_0, …, b_d)`, i.e. the polynomial `z q_b`. -/
def preSeq {n d : ℕ} (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Fin (d + 2) → Matrix (Fin n) (Fin n) C(X, ℂ) :=
  fun j => if h : 0 < (j : ℕ) then b ⟨(j : ℕ) - 1, by omega⟩ else 0

@[simp] lemma appSeq_apply {n d : ℕ} (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (j : Fin (d + 2)) :
    appSeq X b j = if h : (j : ℕ) < d + 1 then b ⟨j, h⟩ else 0 := rfl

@[simp] lemma preSeq_apply {n d : ℕ} (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (j : Fin (d + 2)) :
    preSeq X b j = if h : 0 < (j : ℕ) then b ⟨(j : ℕ) - 1, by omega⟩ else 0 := rfl

end

end Work.KT.Idx
