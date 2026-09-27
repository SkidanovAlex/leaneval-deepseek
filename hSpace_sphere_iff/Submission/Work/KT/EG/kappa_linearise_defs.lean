import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.Laurent

/-!
# `Work.KT.EG.kappa_linearise_defs` — the block companion matrix of a polynomial clutching function

Set-up for Hatcher's linearisation (Prop. 2.6 of *Vector Bundles and K-Theory*, §2.1).

The block index is `BIdx N m = (Fin N × Fin m) ⊕ Fin m`: `N` blocks of size `m` followed by a
final block of size `m`; the total size is `N*m + m`, identified with `Fin (N*m + m)` by
`bIdxEquiv`.

The companion matrix (`N = 2`) is

  `A = [[1, -z, 0], [0, 1, -z], [a₂, a₁, a₀]]`

i.e. `idMat - z • shMat + coeffMat` where `shMat` is the "next block" shift, `idMat` is the
identity on the first `N` blocks and `coeffMat` carries the polynomial coefficients in the last
row.  The column operations `col_{j+1} ← col_{j+1} + z col_j` produce `A * Rmat` with `Rmat` a
block-upper-triangular unipotent matrix, and `Rmat` is inverted by `1 - z • shMat`.
-/

namespace Work.KT.EG

open Matrix

noncomputable section

/-! ## 1. The block index -/

/-- The index of the block companion matrix: `N` blocks of size `m` (`Sum.inl`) followed by one
final block of size `m` (`Sum.inr`). -/
abbrev BIdx (N m : ℕ) : Type := (Fin N × Fin m) ⊕ Fin m

/-- The canonical identification `BIdx N m ≃ Fin (N*m + m)`. -/
def bIdxEquiv (N m : ℕ) : BIdx N m ≃ Fin (N * m + m) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin m))).trans finSumFinEquiv

namespace BIdx

variable {N m : ℕ}

/-- The block number of an index. -/
def st : BIdx N m → ℕ
  | Sum.inl p => p.1.val
  | Sum.inr _ => N

/-- The fibre coordinate of an index. -/
def fib : BIdx N m → Fin m
  | Sum.inl p => p.2
  | Sum.inr r => r

/-- The successor of an index in the block direction.  From the last block of the `inl` part it
moves to the `inr` block; on the `inr` block it is a (never used) fixed point. -/
def nx : BIdx N m → BIdx N m
  | Sum.inl p =>
      if h : p.1.val + 1 < N then Sum.inl ((⟨p.1.val + 1, h⟩ : Fin N), p.2) else Sum.inr p.2
  | Sum.inr r => Sum.inr r

@[simp] lemma st_inl (i : Fin N) (r : Fin m) : st (Sum.inl (i, r) : BIdx N m) = i.val := rfl

@[simp] lemma st_inr (r : Fin m) : st (Sum.inr r : BIdx N m) = N := rfl

@[simp] lemma fib_inl (i : Fin N) (r : Fin m) : fib (Sum.inl (i, r) : BIdx N m) = r := rfl

@[simp] lemma fib_inr (r : Fin m) : fib (Sum.inr r : BIdx N m) = r := rfl

@[simp] lemma nx_inl (i : Fin N) (r : Fin m) :
    nx (Sum.inl (i, r) : BIdx N m)
      = (if h : i.val + 1 < N then Sum.inl ((⟨i.val + 1, h⟩ : Fin N), r) else Sum.inr r) := rfl

@[simp] lemma nx_inr (r : Fin m) : nx (Sum.inr r : BIdx N m) = Sum.inr r := rfl

lemma st_le (x : BIdx N m) : st x ≤ N := by
  rcases x with ⟨i, r⟩ | r <;> simp

lemma st_nx {x : BIdx N m} (h : st x < N) : st (nx x) = st x + 1 := by
  rcases x with ⟨i, r⟩ | r
  · rw [nx_inl]; split <;> simp only [st_inl, st_inr] <;> omega
  · simp only [st_inr] at h; omega

lemma fib_nx (x : BIdx N m) : fib (nx x) = fib x := by
  rcases x with ⟨i, r⟩ | r
  · rw [nx_inl]; split <;> simp
  · simp

lemma eq_of_st_fib {x y : BIdx N m} (h1 : st x = st y) (h2 : fib x = fib y) : x = y := by
  rcases x with ⟨i, r⟩ | r <;> rcases y with ⟨i', r'⟩ | r'
  · simp only [st_inl, fib_inl] at h1 h2
    rw [Fin.ext h1, h2]
  · simp only [st_inl, st_inr, fib_inl, fib_inr] at h1 h2
    have hlt : i.val < N := i.2
    omega
  · simp only [st_inl, st_inr, fib_inl, fib_inr] at h1 h2
    have hlt : i'.val < N := i'.2
    omega
  · simp only [st_inr, fib_inr] at h1 h2
    rw [h2]

lemma st_nx_iterate {x : BIdx N m} (k : ℕ) (h : st x + k ≤ N) : st (nx^[k] x) = st x + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hk : st x + k ≤ N := by omega
    rw [st_nx (by omega : st (nx^[k] x) < N), ih hk]
    omega

lemma fib_nx_iterate {x : BIdx N m} (k : ℕ) : fib (nx^[k] x) = fib x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', fib_nx, ih]

/-- From the `i`-th block, `k` steps of `nx` land in the `(i+k)`-th block. -/
lemma nx_iterate_inl_eval {i : Fin N} (k : ℕ) (h : i.val + k < N) (r : Fin m) :
    nx^[k] (Sum.inl (i, r) : BIdx N m) = Sum.inl ((⟨i.val + k, h⟩ : Fin N), r) := by
  refine eq_of_st_fib ?_ ?_
  · rw [st_nx_iterate k (by simp only [st_inl]; omega)]
    simp only [st_inl, Fin.val_mk]
  · rw [fib_nx_iterate]; simp only [fib_inl]

/-- From the `j`-th block, `N - j` steps of `nx` land in the last (`inr`) block. -/
lemma nx_iterate_inr_eval {j : ℕ} (hj : j < N) (r : Fin m) :
    nx^[N - j] (Sum.inl ((⟨j, hj⟩ : Fin N), r) : BIdx N m) = Sum.inr r := by
  refine eq_of_st_fib ?_ ?_
  · rw [st_nx_iterate (N - j) (by simp only [st_inl, Fin.val_mk]; omega)]
    simp only [st_inl, st_inr, Fin.val_mk]
    omega
  · rw [fib_nx_iterate]; simp only [fib_inl, fib_inr]

end BIdx

/-! ## 2. The block matrices -/

/-- The "next block" shift matrix. -/
def shMat (R : Type) [Zero R] [One R] (N m : ℕ) : Matrix (BIdx N m) (BIdx N m) R :=
  fun x y => if BIdx.st x < N then (if y = BIdx.nx x then 1 else 0) else 0

/-- The identity on the first `N` blocks. -/
def idMat (R : Type) [Zero R] [One R] (N m : ℕ) : Matrix (BIdx N m) (BIdx N m) R :=
  fun x y => if BIdx.st x < N then (if y = x then 1 else 0) else 0

/-- The identity on the last block. -/
def lastMat (R : Type) [Zero R] [One R] (N m : ℕ) : Matrix (BIdx N m) (BIdx N m) R :=
  fun x y => if BIdx.st x = N then (if y = x then 1 else 0) else 0

/-- The matrix of `k`-th coefficients of a polynomial matrix. -/
abbrev coeffMat (X : Type) [TopologicalSpace X] {m : ℕ}
    (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) (k : ℕ) :
    Matrix (Fin m) (Fin m) C(X, ℂ) := fun i j => (q i j).coeff k

/-- The bottom row of the companion matrix: `(a_N, …, a_1)` to the left of the last block and
`a_0` in the bottom-right corner. -/
abbrev coeffMatBig (X : Type) [TopologicalSpace X] {m : ℕ} (N : ℕ)
    (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (BIdx N m) (BIdx N m) C(X, ℂ) :=
  fun x y => match x, y with
    | Sum.inr r, Sum.inl (j, s) => (q r s).coeff (N - j.val)
    | Sum.inr r, Sum.inr s => (q r s).coeff 0
    | _, _ => 0

/-- Pull back the entries of a matrix along a continuous map. -/
abbrev pullIdx {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (g : C(Y, X)) {ι : Type}
    (M : Matrix ι ι C(X, ℂ)) : Matrix ι ι C(Y, ℂ) := M.map (fun f => f.comp g)

@[simp] lemma pullIdx_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (g : C(Y, X))
    {ι : Type} (M : Matrix ι ι C(X, ℂ)) (i j : ι) (y : Y) : pullIdx g M i j y = M i j (g y) :=
  rfl

/-! ## 3. Copies of the vocabulary of `kappaRedDefs` -/

section Copies

variable (X : Type) [TopologicalSpace X]

/-- Copy of `Work.KT.EG.polyMap`: evaluation of polynomials in the coordinate `z`. -/
abbrev polyMapA : Polynomial C(X, ℂ) →+* C(X × Sph ℂ, ℂ) :=
  Polynomial.eval₂RingHom (pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))).toRingHom
    (Work.KT.zUnit X)

@[simp] lemma polyMapA_C (a : C(X, ℂ)) :
    polyMapA X (Polynomial.C a) = pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X)) a :=
  Polynomial.eval₂_C _ _

@[simp] lemma polyMapA_X : polyMapA X Polynomial.X = (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) :=
  Polynomial.eval₂_X _ _

end Copies

section CopyRed

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Copy of `Work.KT.EG.redK`. -/
abbrev redKa (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) : K0 C(X × S2, ℂ) :=
  Work.KT.Fund.kappa X n u - cls (Mat.one C(X × S2, ℂ) n)

end CopyRed

/-! ## 4. The circle `X × S¹` -/

section Circle

variable (X : Type) [TopologicalSpace X]

/-- The coordinate `z` on `X × S¹`. -/
abbrev zc : C(X × Sph ℂ, ℂ) := (Work.KT.zUnit X : C(X × Sph ℂ, ℂ))

@[simp] lemma zc_apply (p : X × Sph ℂ) : zc X p = (p.2 : ℂ) := rfl

/-- The shift matrix over `C(X × S¹, ℂ)`. -/
abbrev shC (N m : ℕ) : Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ) :=
  shMat C(X × Sph ℂ, ℂ) N m

/-- The identity on the first `N` blocks, over `C(X × S¹, ℂ)`. -/
abbrev idC (N m : ℕ) : Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ) :=
  idMat C(X × Sph ℂ, ℂ) N m

/-- The identity on the last block, over `C(X × S¹, ℂ)`. -/
abbrev lastC (N m : ℕ) : Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ) :=
  lastMat C(X × Sph ℂ, ℂ) N m

/-- The pull-back of the coefficient matrix to `X × S¹`. -/
abbrev coeffC {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ) :=
  pullIdx (ContinuousMap.fst : C(X × Sph ℂ, X)) (coeffMatBig X N q)

/-- The companion matrix `A = idMat - z • shMat + coeffMatBig` over `C(X × S¹, ℂ)`. -/
abbrev Amat {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ) :=
  idC X N m - zc X • shC X N m + coeffC X N q

/-- The column-operation matrix `R = Σ_{k ≤ N} z^k • shMat^k`. -/
abbrev Rmat {m : ℕ} (N : ℕ) : Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ) :=
  ∑ k ∈ Finset.range (N + 1), (zc X) ^ k • (shC X N m) ^ k

/-- The coefficient of `z` in the companion matrix, over `C(X, ℂ)`. -/
abbrev aMat {m : ℕ} (N : ℕ) : Matrix (BIdx N m) (BIdx N m) C(X, ℂ) := -shMat C(X, ℂ) N m

/-- The constant coefficient of the companion matrix, over `C(X, ℂ)`. -/
abbrev bMat {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (BIdx N m) (BIdx N m) C(X, ℂ) :=
  idMat C(X, ℂ) N m + coeffMatBig X N q

/-- The bottom-left block of `coeffC * Rmat`. -/
abbrev CRmat {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ) :=
  coeffC X N q * Rmat X N

/-- The bottom-left block of `coeffC * Rmat`. -/
abbrev RowM {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (Fin m) (Fin N × Fin m) C(X × Sph ℂ, ℂ) :=
  fun r p => CRmat X N q (Sum.inr r) (Sum.inl p)

/-- The bottom-right block of `coeffC * Rmat`; it is `q(z)`. -/
abbrev Qm {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ) :=
  fun r s => CRmat X N q (Sum.inr r) (Sum.inr s)

/-- The row-elimination matrix `L = fromBlocks 1 0 (-row) 1`. -/
abbrev Lmat {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ) :=
  (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m) C(X × Sph ℂ, ℂ)) 0
    (-(RowM X N q)) (1 : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) :
      Matrix ((Fin N × Fin m) ⊕ Fin m) ((Fin N × Fin m) ⊕ Fin m) C(X × Sph ℂ, ℂ))

/-- The target of the reduction: `fromBlocks 1 0 0 q(z)`. -/
abbrev Bmat {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ) :=
  (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m) C(X × Sph ℂ, ℂ)) 0 0
    (q.map (polyMapA X)) :
      Matrix ((Fin N × Fin m) ⊕ Fin m) ((Fin N × Fin m) ⊕ Fin m) C(X × Sph ℂ, ℂ))

end Circle

/-! ## 5. The cylinder `(X × I) × S¹` -/

section Cylinder

variable (X : Type) [TopologicalSpace X]

/-- The projection `(X × I) × S¹ → X`. -/
abbrev projCyl : C((X × unitInterval) × Sph ℂ, X) where
  toFun q := q.1.1
  continuous_toFun := by fun_prop

@[simp] lemma projCyl_apply (q : (X × unitInterval) × Sph ℂ) : projCyl X q = q.1.1 := rfl

/-- The projection `(X × I) × S¹ → X × S¹`. -/
def projCylS : C((X × unitInterval) × Sph ℂ, X × Sph ℂ) where
  toFun q := (q.1.1, q.2)
  continuous_toFun := by fun_prop

@[simp] lemma projCylS_apply (q : (X × unitInterval) × Sph ℂ) :
    projCylS X q = (q.1.1, q.2) := rfl

/-- Pull back a matrix over `X × S¹` to the cylinder. -/
abbrev pullCyl {ι κ : Type} (M : Matrix ι κ C(X × Sph ℂ, ℂ)) :
    Matrix ι κ C((X × unitInterval) × Sph ℂ, ℂ) := M.map (fun f => f.comp (projCylS X))

/-- The coordinate `z` on the cylinder. -/
abbrev zCyl_kld : C((X × unitInterval) × Sph ℂ, ℂ) :=
  (Work.KT.zUnit (X × unitInterval) : C((X × unitInterval) × Sph ℂ, ℂ))

/-- The coordinate `t` on the cylinder. -/
abbrev tCyl_kld : C((X × unitInterval) × Sph ℂ, ℂ) where
  toFun q := ((q.1.2 : unitInterval) : ℂ)
  continuous_toFun := by fun_prop

@[simp] lemma tCyl_kld_apply (q : (X × unitInterval) × Sph ℂ) :
    tCyl_kld X q = ((q.1.2 : unitInterval) : ℂ) := rfl

/-- The shift matrix over the cylinder. -/
abbrev shCyl (N m : ℕ) : Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ) :=
  shMat C((X × unitInterval) × Sph ℂ, ℂ) N m

/-- The identity on the first `N` blocks, over the cylinder. -/
abbrev idCyl (N m : ℕ) : Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ) :=
  idMat C((X × unitInterval) × Sph ℂ, ℂ) N m

/-- The pull-back of the coefficient matrix to the cylinder. -/
abbrev coeffCyl {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ) :=
  pullIdx (projCyl X) (coeffMatBig X N q)

/-- The companion matrix over the cylinder = the pull-back of `Amat`. -/
abbrev AmatCyl {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ) :=
  pullCyl X (Amat X N q)

/-- The interpolated column-operation matrix `R_t = Σ_{k ≤ N} (tz)^k • shMat^k`. -/
abbrev RmatCyl {m : ℕ} (N : ℕ) :
    Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ) :=
  ∑ k ∈ Finset.range (N + 1),
    ((tCyl_kld X) * (zCyl_kld X)) ^ k • (shCyl X N m) ^ k

/-- The bottom-left block of `coeffCyl * RmatCyl`. -/
abbrev CRmatCyl {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ) :=
  coeffCyl X N q * RmatCyl X N

/-- The bottom-left block of `coeffCyl * RmatCyl`. -/
abbrev RowMCyl {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (Fin m) (Fin N × Fin m) C((X × unitInterval) × Sph ℂ, ℂ) :=
  pullCyl X (RowM X N q)

/-- The interpolated row-elimination matrix `L_t = fromBlocks 1 0 (-t • row) 1`. -/
abbrev LmatCyl {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ) :=
  (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m)
      C((X × unitInterval) × Sph ℂ, ℂ)) 0
    (-(tCyl_kld X • RowMCyl X N q))
    (1 : Matrix (Fin m) (Fin m) C((X × unitInterval) × Sph ℂ, ℂ)) :
      Matrix ((Fin N × Fin m) ⊕ Fin m) ((Fin N × Fin m) ⊕ Fin m)
        C((X × unitInterval) × Sph ℂ, ℂ))

end Cylinder

end

end Work.KT.EG
