import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.SpectralAux
import Submission.Work.KT.Fund.Laurent

/-!
# `Work.KT.FP.PencilDefs` — the pencil projection and the W linearisation

Vocabulary for the Bott index `Work.KT.FP.bott_index`.

* `pRes A B z = (z • A + B)⁻¹` — the resolvent of the matrix pencil `zA + B`;
* `pCirc A B ρ = ∮_{|z|=ρ} (zA+B)⁻¹ A dz`, `pProj A B ρ = (2πi)⁻¹ • pCirc A B ρ` — the "inside"
  spectral projection of the pencil;
* `pullFun`, `wPenA`, `wPenB`, `polyOf`, `wPenClutch` — the W linearisation of a polynomial
  clutching function with coefficient sequence `b : Fin (d+1) → Mₙ(C(X))`, on the block index
  type `Fin (d+1) × Fin n`: the kernel recursion `v_{i+1} = z v_i`, `Σ_j b_j v_j = 0` shows that
  `W(z)` is invertible for `z` on the circle exactly when `Σ_j b_j z^j` is;
* `matPProj` — the pencil projection for `Fin N`-indexed matrices over `C(X, ℂ)`;
* `coeffSeq`, `linAf`, `linBf`, `lindAt` — the linearisation of a Laurent matrix of bounded degree
  and the resulting candidate index.
-/

namespace Work.KT.FP

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

/-! ## The pencil projection (a complex Banach algebra) -/

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

/-- The resolvent of the matrix pencil `z ↦ z • A + B`. -/
def pRes (A B : R) (z : ℂ) : R := Ring.inverse (z • A + B)

/-- The integrand `(z • A + B)⁻¹ * A` of the pencil projection. -/
def pResA (A B : R) (z : ℂ) : R := pRes A B z * A

/-- The circle integral `∮_{|z|=ρ} (zA+B)⁻¹ A dz`. -/
def pCirc (A B : R) (ρ : ℝ) : R := ∮ z in C(0, ρ), pResA A B z

/-- The "inside" spectral projection of the pencil `z ↦ zA + B`. -/
def pProj (A B : R) (ρ : ℝ) : R := (2 * Real.pi * Complex.I)⁻¹ • pCirc A B ρ

/-- The same integral computed on the unit circle. -/
def pCircB (A B : R) (ρ : ℝ) : R := ∮ z in C(0, 1), pResA A B z

/-- The pencil projection computed on the unit circle. -/
def pProjB (A B : R) (ρ : ℝ) : R := (2 * Real.pi * Complex.I)⁻¹ • pCircB A B ρ

omit [CompleteSpace R] in
lemma pProj_one_neg (b : R) (ρ : ℝ) : pProj (1 : R) (-b) ρ = Work.KT.Fund.Proj b ρ := by
  simp [pProj, pCirc, pResA, pRes, Work.KT.Fund.Proj, Work.KT.Fund.CircA, Work.KT.Fund.Res,
    sub_eq_add_neg]

/-! ## Lifts to `X × S¹`, and the pencil projection over `C(X, ℂ)` -/

/-- The lift of a function on `X` to `X × S¹`. -/
def pullFun (X : Type) [TopologicalSpace X] (f : C(X, ℂ)) : C(X × Sph ℂ, ℂ) :=
  f.comp (ContinuousMap.fst : C(X × Sph ℂ, X))

@[simp] lemma pullFun_apply (X : Type) [TopologicalSpace X] (f : C(X, ℂ)) (p : X × Sph ℂ) :
    pullFun X f p = f p.1 := rfl

/-- The pencil projection for `Fin N`-indexed matrices over `C(X, ℂ)`, with the `L∞` operator norm
as the Banach algebra structure. -/
def matPProj (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (N : ℕ) (A B : Matrix (Fin N) (Fin N) C(X, ℂ)) (ρ : ℝ) :
    Matrix (Fin N) (Fin N) C(X, ℂ) :=
  letI : NormedRing (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  pProj A B ρ

/-! ## The W linearisation -/

/-- The `z`-coefficient of the W linearisation: the identity in all blocks except the last. -/
def wPenA (X : Type) [TopologicalSpace X] (n d : ℕ) :
    Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ) :=
  fun i j => if i.1 = j.1 ∧ (i.1 : ℕ) ≠ d then (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) i.2 j.2
    else 0

/-- The constant part of the W linearisation: `-1` on the superdiagonal of the block index, and the
coefficient matrices in the last block row. -/
def wPenB (X : Type) [TopologicalSpace X] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ) :=
  fun i j =>
    if (i.1 : ℕ) + 1 = (j.1 : ℕ) then
      (if (i.1 : ℕ) = d then b j.1 i.2 j.2
        else -(1 : Matrix (Fin n) (Fin n) C(X, ℂ)) i.2 j.2)
    else if (i.1 : ℕ) = d then b j.1 i.2 j.2
    else 0

/-- The polynomial (clutching function) attached to a coefficient sequence. -/
def polyOf (X : Type) [TopologicalSpace X] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
  fun a c => ∑ j : Fin (d + 1),
    (pullFun X (b j a c)) * ((Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) ^ (j : ℕ))

/-- The W clutching function `z ↦ z • wPenA + wPenB` as a matrix over `C(X × S¹, ℂ)`. -/
def wPenClutch (X : Type) [TopologicalSpace X] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X × Sph ℂ, ℂ) :=
  fun i j => (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) * (pullFun X (wPenA X n d i j))
    + (pullFun X (wPenB X n d b i j))

/-- The W linearisation reindexed to `Fin ((d+1)*n)`. -/
def wPenAf (X : Type) [TopologicalSpace X] (n d : ℕ) :
    Matrix (Fin ((d + 1) * n)) (Fin ((d + 1) * n)) C(X, ℂ) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (wPenA X n d)

/-- The constant part of the W linearisation, reindexed to `Fin ((d+1)*n)`. -/
def wPenBf (X : Type) [TopologicalSpace X] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin ((d + 1) * n)) (Fin ((d + 1) * n)) C(X, ℂ) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (wPenB X n d b)

/-! ## The Laurent linearisation of a bounded-degree Laurent matrix -/

/-- The coefficient sequence of a Laurent matrix with degree bound `m`: the `j`-th coefficient of
`z^m • P`. -/
def coeffSeq (X : Type) [TopologicalSpace X] (n m : ℕ)
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) :
    Fin (2 * m + 1) → Matrix (Fin n) (Fin n) C(X, ℂ) :=
  fun j a c => (P a c).coeff ((j : ℤ) - (m : ℤ))

/-- The reindexed `z`-coefficient of the linearisation of the degree-`m` part of a Laurent
matrix. -/
def linAf (X : Type) [TopologicalSpace X] (n m : ℕ) :
    Matrix (Fin ((2 * m + 1) * n)) (Fin ((2 * m + 1) * n)) C(X, ℂ) :=
  wPenAf X n (2 * m)

/-- The reindexed constant part of the linearisation of the degree-`m` part of a Laurent
matrix. -/
def linBf (X : Type) [TopologicalSpace X] (n m : ℕ)
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) :
    Matrix (Fin ((2 * m + 1) * n)) (Fin ((2 * m + 1) * n)) C(X, ℂ) :=
  wPenBf X n (2 * m) (coeffSeq X n m P)

/-- The candidate index of a bounded-degree Laurent clutching function, computed with the pencil
projection at radius `ρ`. -/
def lindAt (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n m : ℕ) (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) (ρ : ℝ) : K0 C(X, ℂ) :=
  cls ((⟨(2 * m + 1) * n, matPProj X ((2 * m + 1) * n) (linAf X n m) (linBf X n m P) ρ⟩ : Mat C(X, ℂ)))
    - m • cls (Mat.one C(X, ℂ) n)

end

end Work.KT.FP
