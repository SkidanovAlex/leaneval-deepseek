import Mathlib
import Submission.Work.KT.Idx.WPen
import Submission.Work.KT.Idx.PenDefs

/-!
# `Work.Idx.WPenBlk` — the W linearisation in block form, and its explicit resolvent

The W linearisation `Work.KT.Idx.wPenA` / `wPenB` is a matrix on the product index
`Fin (d+1) × Fin n`.  Here we

* restate it over an arbitrary commutative `ℂ`-algebra `A` (`wBA`, `wBB`), so that the purely
  algebraic statements (the explicit inverse, the annihilation of the pencil's rows by the
  coefficient sequence) can be proved and used in that generality, and record that the
  original definitions are the case `A = C(X, ℂ)` (`wBA_eq_wPenA`, `wBB_eq_wPenB`);

* introduce the polynomial matrix `wQ n D c z = ∑_j z^j • c_j` carried by a coefficient
  sequence, its "tail sums" `wd n D c z i = ∑_{j > i} z^{j-1-i} • c_j`, the last-index extension
  `wde`, and the explicit matrix `wInv n D c z E` which is the inverse of the pencil
  `z • wBA + wBB` as soon as `E` is a two-sided inverse of `wQ`;

* introduce the explicit "projection" `wProj n D c Ψ` (with `Ψ : ℤ → Mₙ(A)` the Fourier data
  `Ψ_m = (2πi)⁻¹ ∮_{|z|=1} z^m Q_c(z)⁻¹ dz`), whose entry `(k,i)` is
  `∑_{j > i} Ψ_{k+j-1-i} · c_j` (zero in the last block column), and the integral `wPsi`
  defining `Ψ` for `A = C(X, ℂ)`.

The mathematical content proved elsewhere, but stated here (so that everything below can refer
to the same vocabulary):

* `wInv` is a two-sided inverse of the pencil (`wBlk_mul_wInv`, `wInv_mul_wBlk`);
* `wProj` with `wPsi` **is** the pencil projection `matPenProj` (`matPenProj_eq_wProj`);
* the row vector of coefficients annihilates `wInv` and hence the projection
  (`wRow_wInv`, `wRow_wProj`).
-/

namespace Work.Idx

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The `z`-coefficient of the W linearisation, on the block index `Fin (D+1) × Fin n`: the
identity in all blocks except the last. -/
def wBA (n D : ℕ) : Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) A :=
  fun i j => if i.1 = j.1 ∧ (i.1 : ℕ) ≠ D then (1 : Matrix (Fin n) (Fin n) A) i.2 j.2 else 0

/-- The constant part of the W linearisation: `-1` on the superdiagonal of the block index and the
coefficient matrices in the last block row. -/
def wBB (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) :
    Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) A :=
  fun i j =>
    if (i.1 : ℕ) + 1 = (j.1 : ℕ) then
      (if (i.1 : ℕ) = D then c j.1 i.2 j.2 else -(1 : Matrix (Fin n) (Fin n) A) i.2 j.2)
    else if (i.1 : ℕ) = D then c j.1 i.2 j.2 else 0

/-- The polynomial matrix `Q_c(z) = ∑_j z^j • c_j`. -/
def wQ (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ) :
    Matrix (Fin n) (Fin n) A :=
  ∑ j : Fin (D + 1), (z ^ (j : ℕ)) • c j

/-- The tail sum `d_i(z) = ∑_{j > i} z^{j-1-i} • c_j`. -/
def wd (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ) (i : Fin (D + 1)) :
    Matrix (Fin n) (Fin n) A :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (D + 1) => i < j), (z ^ ((j : ℕ) - 1 - (i : ℕ))) • c j

/-- `d_i` extended by `1` at the last index (the column of the free term `w_D`). -/
def wde (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ) (i : Fin (D + 1)) :
    Matrix (Fin n) (Fin n) A :=
  if (i : ℕ) = D then 1 else wd n D c z i

/-- The explicit inverse of the W pencil: with `E` a two-sided inverse of `wQ n D c z`, the block
`(k,i)` is `z^k • (E * d_i(z)) - [i < k] z^{k-1-i} • 1`. -/
def wInv (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ)
    (E : Matrix (Fin n) (Fin n) A) :
    Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) A :=
  fun p q => ((z ^ (p.1 : ℕ)) • (E * wde n D c z q.1) -
      (if (q.1 : ℕ) < (p.1 : ℕ) then
        (z ^ ((p.1 : ℕ) - 1 - (q.1 : ℕ))) • (1 : Matrix (Fin n) (Fin n) A) else 0)) p.2 q.2

/-- The explicit projection of the W pencil: block `(k,i)` is `∑_{j>i} Ψ_{k+j-1-i} · c_j`, and
the last block column vanishes. -/
def wProj (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (Ψ : ℤ → Matrix (Fin n) (Fin n) A) :
    Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) A :=
  fun p q => (∑ j ∈ Finset.univ.filter (fun j : Fin (D + 1) => q.1 < j),
      Ψ ((p.1 : ℤ) + (j : ℤ) - 1 - (q.1 : ℤ)) * c j) p.2 q.2

/-- The correction term `Ψ̃ · c̃` of the prepend comparison: block `(k,i)` is `Ψ_{k-1} * c_i`. -/
def wUpdate (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A)
    (Ψ : ℤ → Matrix (Fin n) (Fin n) A) :
    Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) A :=
  fun p q => (Ψ ((p.1 : ℤ) - 1) * c q.1) p.2 q.2

/-- The block column `Ψ̃`: block `k` is `Ψ_{k-1}`. -/
def wCol (n D : ℕ) (Ψ : ℤ → Matrix (Fin n) (Fin n) A) :
    Matrix (Fin (D + 1) × Fin n) (Fin n) A :=
  fun p c => (Ψ ((p.1 : ℤ) - 1)) p.2 c

/-- The block row `c̃`: block `k` is `c_k`. -/
def wRow (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) :
    Matrix (Fin n) (Fin (D + 1) × Fin n) A :=
  fun c' q => (c q.1) c' q.2

/-! ## The original definitions are the case `A = C(X, ℂ)` -/

variable (X : Type) [TopologicalSpace X]

@[simp] lemma wBA_eq_wPenA (n d : ℕ) :
    wBA (A := C(X, ℂ)) n d = Work.KT.Idx.wPenA X n d := rfl

@[simp] lemma wBB_eq_wPenB (n d : ℕ)
    (c : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    wBB (A := C(X, ℂ)) n d c = Work.KT.Idx.wPenB X n d c := rfl

variable [CompactSpace X] [T2Space X]

/-- The pencil projection for matrices on an arbitrary finite index type `ι`, i.e. the element
`(2πi)⁻¹ ∮_{|z|=1} (zA+B)⁻¹ A dz` of `Matrix ι ι C(X, ℂ)` with the `L∞` operator norm.  This is
`Work.KT.Idx.matPenProj` for `ι = Fin N`. -/
def blkPenProj (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι C(X, ℂ)) : Matrix ι ι C(X, ℂ) :=
  letI : NormedRing (Matrix ι ι C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix ι ι C(X, ℂ)) := Matrix.instCompleteSpace ι ι C(X, ℂ)
  Work.KT.Idx.penProj A B

/-- The "block inclusion" from the `(d+1)`-block index to the `(d+2)`-block index: the identity in
the first `d+1` blocks, zero in the last one. -/
def wInc (n d : ℕ) : Matrix (Fin (d + 2) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ) :=
  fun p q => if (p.1 : ℕ) = (q.1 : ℕ) ∧ p.2 = q.2 then 1 else 0

/-- The block projection onto the first `d+1` blocks, i.e. `wInc * wIncᵀ`. -/
def wQbig (n d : ℕ) : Matrix (Fin (d + 2) × Fin n) (Fin (d + 2) × Fin n) C(X, ℂ) :=
  wInc (X := X) n d * (wInc (X := X) n d)ᵀ

/-- The Fourier data `Ψ_m = (2πi)⁻¹ ∮_{|z|=1} z^m Q_c(z)⁻¹ dz` of the pencil. -/
def wPsi (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (m : ℤ) :
    Matrix (Fin n) (Fin n) C(X, ℂ) :=
  letI : NormedRing (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  (2 * Real.pi * Complex.I)⁻¹ • ∮ z in C(0, 1), (z ^ m) • Ring.inverse (wQ (A := C(X, ℂ)) n D c z)

end

end Work.Idx
