import Mathlib
import Submission.Work.KT.Fund.kbi_setup
import Submission.Work.KT.Fund.kappa_homotopic

/-!
# `Work.KT.Fund.kbi_defs` — the target idempotent and its trivialisations

Private copy (namespace `KBI`) of the setup for the proof of `Work.KT.Fund.kappa_bott`.

On each of the two discs we trivialise the module `P ⊗ H ⊕ Q`, where `H` is the Hopf line bundle:

* `TB1p`, `TB2p` are the frames (`2n × n`),
* `SA1p`, `SA2p` are their retractions (`n × 2n`),
* `W1p`, `W2p` are the two disc-images of the target idempotent.

This file is sorry-free.
-/

namespace Work.KT.Fund

open _root_.Matrix
open scoped Kronecker

noncomputable section

namespace KBI

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The disc algebra. -/
abbrev kdD : Type := C(X × Ball ℂ, ℂ)

/-- The circle algebra. -/
abbrev kdC : Type := C(X × Sph ℂ, ℂ)

/-! ## The two explicit `2 × 2` projections for the Hopf line -/

/-- The projection onto the line spanned by `(1, ζ)`: `c • [[1, ζ̄], [ζ, |ζ|²]]`. -/
def h1m : Matrix (Fin 2) (Fin 2) (kdD X) :=
  Matrix.of fun i j =>
    if i = 0 then (if j = 0 then zcn X else zcn X * zcb X)
    else (if j = 0 then zcn X * zc X else zcn X * (zc X * zcb X))

/-- The projection onto the line spanned by `(ζ̄, 1)`: `c • [[|ζ|², ζ̄], [ζ, 1]]`. -/
def h2m : Matrix (Fin 2) (Fin 2) (kdD X) :=
  Matrix.of fun i j =>
    if i = 0 then (if j = 0 then zcn X * (zc X * zcb X) else zcn X * zcb X)
    else (if j = 0 then zcn X * zc X else zcn X)

/-- The rank-one projection onto the first coordinate. -/
def E00 : Matrix (Fin 2) (Fin 2) (kdD X) :=
  Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0

@[simp] lemma h1m_apply_00 : h1m X 0 0 = zcn X := rfl
@[simp] lemma h1m_apply_01 : h1m X 0 1 = zcn X * zcb X := rfl
@[simp] lemma h1m_apply_10 : h1m X 1 0 = zcn X * zc X := rfl
@[simp] lemma h1m_apply_11 : h1m X 1 1 = zcn X * (zc X * zcb X) := rfl
@[simp] lemma h2m_apply_00 : h2m X 0 0 = zcn X * (zc X * zcb X) := rfl
@[simp] lemma h2m_apply_01 : h2m X 0 1 = zcn X * zcb X := rfl
@[simp] lemma h2m_apply_10 : h2m X 1 0 = zcn X * zc X := rfl
@[simp] lemma h2m_apply_11 : h2m X 1 1 = zcn X := rfl

/-! ## The pullbacks of `P` and `Q` to the disc -/

variable (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ))

/-- The pullback of `P` to the disc (constant in the disc variable). -/
def Pd : Matrix (Fin n) (Fin n) (kdD X) := KC.gUp X P

/-- The pullback of `Q = 1 - P` to the disc. -/
def Qd : Matrix (Fin n) (Fin n) (kdD X) := 1 - Pd X n P

lemma Pd_sq (hP : P * P = P) : Pd X n P * Pd X n P = Pd X n P := by
  rw [Pd, ← KC.gUp_mul, hP]

lemma Pd_add_Qd : Pd X n P + Qd X n P = 1 := by
  rw [Qd]; abel

/-- The scalar multiple `a • Pd`, written entrywise. -/
def sm (a : kdD X) : Matrix (Fin n) (Fin n) (kdD X) := Matrix.of fun i j => a * Pd X n P i j

lemma sm_add (a b : kdD X) : sm X n P (a + b) = sm X n P a + sm X n P b := by
  ext i j
  simp only [sm, Matrix.of_apply, Matrix.add_apply, ContinuousMap.add_apply, add_mul]

lemma sm_one (hP : P * P = P) : sm X n P 1 = Pd X n P := by
  ext i j
  simp only [sm, Matrix.of_apply, one_mul]

/-! ## The block "column" and "row" selectors -/

/-- The column selector `a ↦ (a.1) if a.2 = 0 else 0`. -/
def D0 : Matrix (Fin n × Fin 2) (Fin n) (kdD X) :=
  Matrix.of fun a j => if a.2 = 0 then (if a.1 = j then 1 else 0) else 0

/-- The column selector `a ↦ (a.1) if a.2 = 1 else 0`. -/
def D1 : Matrix (Fin n × Fin 2) (Fin n) (kdD X) :=
  Matrix.of fun a j => if a.2 = 1 then (if a.1 = j then 1 else 0) else 0

/-- The row selector `a ↦ (a.1) if a.2 = 0 else 0`. -/
def R0 : Matrix (Fin n) (Fin n × Fin 2) (kdD X) :=
  Matrix.of fun i a => if a.2 = 0 then (if i = a.1 then 1 else 0) else 0

/-- The row selector `a ↦ (a.1) if a.2 = 1 else 0`. -/
def R1 : Matrix (Fin n) (Fin n × Fin 2) (kdD X) :=
  Matrix.of fun i a => if a.2 = 1 then (if i = a.1 then 1 else 0) else 0

@[simp] lemma D0_apply (a : Fin n × Fin 2) (j : Fin n) :
    D0 X n a j = if a.2 = 0 then (if a.1 = j then 1 else 0) else 0 := rfl
@[simp] lemma D1_apply (a : Fin n × Fin 2) (j : Fin n) :
    D1 X n a j = if a.2 = 1 then (if a.1 = j then 1 else 0) else 0 := rfl
@[simp] lemma R0_apply (i : Fin n) (a : Fin n × Fin 2) :
    R0 X n i a = if a.2 = 0 then (if i = a.1 then 1 else 0) else 0 := rfl
@[simp] lemma R1_apply (i : Fin n) (a : Fin n × Fin 2) :
    R1 X n i a = if a.2 = 1 then (if i = a.1 then 1 else 0) else 0 := rfl

/-! ## The frames, the retractions and the two disc-images -/

/-- The frame of the target module over the first disc. -/
def TB1p : Matrix (Fin n × Fin 2) (Fin n) (kdD X) :=
  D0 X n + D1 X n * sm X n P (zc X)

/-- The retraction of `TB1p`. -/
def SA1p : Matrix (Fin n) (Fin n × Fin 2) (kdD X) :=
  (Qd X n P + sm X n P (zcn X)) * R0 X n + sm X n P (zcn X * zcb X) * R1 X n

/-- The frame of the target module over the second disc. -/
def TB2p : Matrix (Fin n × Fin 2) (Fin n) (kdD X) :=
  D0 X n * (Qd X n P + sm X n P (zcb X)) + D1 X n * Pd X n P

/-- The retraction of `TB2p`. -/
def SA2p : Matrix (Fin n) (Fin n × Fin 2) (kdD X) :=
  (Qd X n P + sm X n P (zcn X * zc X)) * R0 X n + sm X n P (zcn X) * R1 X n

/-- The disc-1 image of the target idempotent. -/
def W1p : Matrix (Fin n × Fin 2) (Fin n × Fin 2) (kdD X) :=
  Pd X n P ⊗ₖ h1m X + Qd X n P ⊗ₖ E00 X

/-- The disc-2 image of the target idempotent. -/
def W2p : Matrix (Fin n × Fin 2) (Fin n × Fin 2) (kdD X) :=
  Pd X n P ⊗ₖ h2m X + Qd X n P ⊗ₖ E00 X

/-! ## The reindexed (`Fin (n*2)`) versions -/

/-- The disc-1 image of the target idempotent, in the indexing `Fin (n*2)`. -/
def W1 : Matrix (Fin (n*2)) (Fin (n*2)) (kdD X) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (W1p X n P)

/-- The disc-2 image of the target idempotent, in the indexing `Fin (n*2)`. -/
def W2 : Matrix (Fin (n*2)) (Fin (n*2)) (kdD X) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (W2p X n P)

/-! ## The Hopf matrices in the `Fin 1 ⊕ Fin 1` indexing used by `pairIdem` -/

/-- `h1m` in the `Fin 1 ⊕ Fin 1` indextype. -/
def h1e : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (kdD X) :=
  Matrix.reindex (finSumFinEquiv.symm) (finSumFinEquiv.symm) (h1m X)

/-- `h2m` in the `Fin 1 ⊕ Fin 1` indextype. -/
def h2e : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (kdD X) :=
  Matrix.reindex (finSumFinEquiv.symm) (finSumFinEquiv.symm) (h2m X)

lemma h1e_map (φ : kdD X →+* kdC X) : (h1e X).map φ
    = Matrix.reindex (finSumFinEquiv.symm) (finSumFinEquiv.symm) ((h1m X).map φ) := rfl

lemma h2e_map (φ : kdD X →+* kdC X) : (h2e X).map φ
    = Matrix.reindex (finSumFinEquiv.symm) (finSumFinEquiv.symm) ((h2m X).map φ) := rfl


/-- The frame over the first disc, in the indexing `Fin (n*2)`. -/
def TB1 : Matrix (Fin (n*2)) (Fin n) (kdD X) :=
  Matrix.reindex finProdFinEquiv (Equiv.refl (Fin n)) (TB1p X n P)

/-- The retraction over the first disc, in the indexing `Fin (n*2)`. -/
def SA1 : Matrix (Fin n) (Fin (n*2)) (kdD X) :=
  Matrix.reindex (Equiv.refl (Fin n)) finProdFinEquiv (SA1p X n P)

/-- The frame over the second disc, in the indexing `Fin (n*2)`. -/
def TB2 : Matrix (Fin (n*2)) (Fin n) (kdD X) :=
  Matrix.reindex finProdFinEquiv (Equiv.refl (Fin n)) (TB2p X n P)

/-- The retraction over the second disc, in the indexing `Fin (n*2)`. -/
def SA2 : Matrix (Fin n) (Fin (n*2)) (kdD X) :=
  Matrix.reindex (Equiv.refl (Fin n)) finProdFinEquiv (SA2p X n P)

lemma reindex_map_sq {M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) (kdD X)} (φ : kdD X →+* kdC X) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv M).map φ
      = Matrix.reindex finProdFinEquiv finProdFinEquiv (M.map φ) := rfl

lemma reindex_map_fr {M : Matrix (Fin n × Fin 2) (Fin n) (kdD X)} (φ : kdD X →+* kdC X) :
    (Matrix.reindex finProdFinEquiv (Equiv.refl (Fin n)) M).map φ
      = Matrix.reindex finProdFinEquiv (Equiv.refl (Fin n)) (M.map φ) := rfl

lemma reindex_map_rf {M : Matrix (Fin n) (Fin n × Fin 2) (kdD X)} (φ : kdD X →+* kdC X) :
    (Matrix.reindex (Equiv.refl (Fin n)) finProdFinEquiv M).map φ
      = Matrix.reindex (Equiv.refl (Fin n)) finProdFinEquiv (M.map φ) := rfl

lemma W1_eq_kron : W1 X n P = kronMat (Pd X n P) (h1m X) + kronMat (Qd X n P) (E00 X) := by
  rw [W1, W1p]
  ext i j
  rfl

lemma W2_eq_kron : W2 X n P = kronMat (Pd X n P) (h2m X) + kronMat (Qd X n P) (E00 X) := by
  rw [W2, W2p]
  ext i j
  rfl

lemma TB1_mul_SA1 (h : TB1p X n P * SA1p X n P = W1p X n P) :
    TB1 X n P * SA1 X n P = W1 X n P := by
  simp only [TB1, SA1, W1, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [h]

lemma TB2_mul_SA2 (h : TB2p X n P * SA2p X n P = W2p X n P) :
    TB2 X n P * SA2 X n P = W2 X n P := by
  simp only [TB2, SA2, W2, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [h]

lemma SA1_mul_TB1 (h : SA1p X n P * TB1p X n P = 1) : SA1 X n P * TB1 X n P = 1 := by
  simp only [TB1, SA1, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [h]
  exact Matrix.submatrix_one_equiv (Equiv.refl (Fin n)).symm

lemma SA2_mul_TB2 (h : SA2p X n P * TB2p X n P = 1) : SA2 X n P * TB2 X n P = 1 := by
  simp only [TB2, SA2, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [h]
  exact Matrix.submatrix_one_equiv (Equiv.refl (Fin n)).symm

/-! ## The pullbacks of `P` and `Q` to `pullAlg2 X` -/

/-- The image of `C(X,ℂ)` inside `pullAlg2 X`: a function on `X` becomes the pair of its
pullbacks to the two discs (equivalently, the pullback of the corresponding function on
`X × S²`). -/
def diagPull : C(X, ℂ) →+* ↥(pullAlg2 X) :=
  ((glueEquiv X : C(X × S2, ℂ) →+* ↥(pullAlg2 X)).comp
    (pullAlg (ContinuousMap.fst : C(X × S2, X))).toRingHom)

/-- The pullback of `P` to `pullAlg2 X`. -/
def PR : Matrix (Fin n) (Fin n) ↥(pullAlg2 X) := P.map (diagPull X)

/-- The pullback of `1 - P` to `pullAlg2 X`. -/
def QR : Matrix (Fin n) (Fin n) ↥(pullAlg2 X) := (1 - P).map (diagPull X)


end KBI

end

end Work.KT.Fund
