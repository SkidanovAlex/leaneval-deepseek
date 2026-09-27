import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.cls_eq_stable_mvN
import Submission.Work.KT.k0_rep

/-!
# `Work.KT.Cone.mv_surj` — Mayer–Vietoris surjectivity for `K₀`

`K₀` of a cartesian square of rings (a *Milnor square*) with one surjective leg is the fibre
product of the `K₀`'s of the corners:

```
P --ρ₁--> P₁
|          |
ρ₂         σ₁
v          v
P₂ --σ₂--> Q
```

This file proves `Work.KT.Cone.mv_surj` from the standard algebraic inputs

* `Work.KT.k0_rep` — every element of `K₀` is a difference `[F] - [1_n]`,
* `Work.KT.cls_eq_stable_mvN` — equal `K₀`-classes are stable Murray–von Neumann equivalence,
* `Work.KT.Cone.glue_idem` — Milnor patching of idempotents, proved here from the block-matrix
  identities of Milnor's patching theorem (reproduced below).
-/

namespace Work.KT.Cone

open Matrix

noncomputable section

/-! ## Elementary lemmas about `cls`, `Mat.map` and identity blocks -/

section Elementary

variable {R S : Type} [Ring R] [Ring S]

/-- `K₀.map` on the class of an idempotent. -/
lemma map_cls (φ : R →+* S) (p : Mat R) (hp : p.IsIdem) :
    K0.map φ (cls p) = cls (p.map φ) := by
  have h : K0.map φ (cls p) = mapCls φ p := by
    rw [show K0.map φ = QuotientAddGroup.lift (K0Rel R) (FreeAbelianGroup.lift (mapCls φ)) _
        from rfl]
    rw [show cls p = QuotientAddGroup.mk (FreeAbelianGroup.of p) from rfl]
    rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]
  rw [h, mapCls, if_pos hp]

/-- The identity matrix maps to the identity matrix. -/
lemma map_one (φ : R →+* S) (k : ℕ) : (Mat.one R k).map φ = Mat.one S k := by
  unfold Mat.one Mat.map
  simp

/-- `Mat.map` commutes with block sums. -/
lemma map_sum (φ : R →+* S) (p q : Mat R) :
    (p.sum q).map φ = (p.map φ).sum (q.map φ) := by
  obtain ⟨m, M⟩ := p
  obtain ⟨n, N⟩ := q
  refine Sigma.ext rfl ?_
  simp only [Mat.map, Mat.sum, heq_eq_eq]
  ext i j
  rcases hi : finSumFinEquiv.symm i with a | a <;> rcases hj : finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.fromBlocks,
      hi, hj]

/-- The identity matrix is idempotent. -/
lemma one_idem (k : ℕ) : (Mat.one R k).IsIdem := by
  unfold Mat.IsIdem Mat.one
  simp

/-- A block sum of identity matrices is an identity matrix. -/
lemma one_sum (m n : ℕ) : (Mat.one R m).sum (Mat.one R n) = Mat.one R (m + n) := by
  have hfb : Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) R) 0 0
      (1 : Matrix (Fin n) (Fin n) R) = 1 := Matrix.fromBlocks_one
  have hri : Matrix.reindex finSumFinEquiv finSumFinEquiv
      (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R) = 1 := by
    ext i j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · have h' : finSumFinEquiv.symm i ≠ finSumFinEquiv.symm j :=
        fun hh => h (finSumFinEquiv.symm.injective hh)
      simp [h, h']
  unfold Mat.one Mat.sum
  rw [hfb, hri]

/-- Classes of identity matrices are additive. -/
lemma cls_one_add (m n : ℕ) :
    cls (Mat.one R (m + n)) = cls (Mat.one R m) + cls (Mat.one R n) := by
  rw [← one_sum m n, cls_sum (one_idem m) (one_idem n)]

/-- Shifting a normal form by identity blocks. -/
lemma shift_rep {F : Mat R} {n m : ℕ} (hF : F.IsIdem) :
    cls F - cls (Mat.one R n) = cls (F.sum (Mat.one R m)) - cls (Mat.one R (n + m)) := by
  rw [cls_sum hF (one_idem m), cls_one_add n m]
  abel

/-- The zero matrix of any size has `K₀`-class `0`. -/
lemma cls_zero (n : ℕ) : cls (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R) = 0 := by
  have hz : Mat.IsIdem (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R) := by
    show (0 : Matrix (Fin n) (Fin n) R) * 0 = 0
    simp
  have hz' : Mat.IsIdem (⟨n + n, (0 : Matrix (Fin (n + n)) (Fin (n + n)) R)⟩ : Mat R) := by
    show (0 : Matrix (Fin (n + n)) (Fin (n + n)) R) * 0 = 0
    simp
  have hsum : Mat.sum (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R)
      (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R) =
      ⟨n + n, (0 : Matrix (Fin (n + n)) (Fin (n + n)) R)⟩ := by
    refine Sigma.ext rfl ?_
    simp [Mat.sum]
  have hmvN : Mat.MvN (⟨n + n, (0 : Matrix (Fin (n + n)) (Fin (n + n)) R)⟩ : Mat R)
      (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R) :=
    ⟨0, 0, by simp, by simp⟩
  have h1 : cls (⟨n + n, (0 : Matrix (Fin (n + n)) (Fin (n + n)) R)⟩ : Mat R) =
      cls (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R) :=
    cls_eq_of_mvN hz' hz hmvN
  have h2 : cls (Mat.sum (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R)
      (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R)) =
      cls (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R) := by
    rw [hsum]; exact h1
  have h3 := cls_sum hz hz
  rw [h2] at h3
  have h4 : cls (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R) + 0 =
      cls (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R) +
        cls (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R) := by
    rw [add_zero]; exact h3
  exact (add_left_cancel h4).symm

end Elementary

/-! ## Block-matrix identities (copied from `Submission/Work/KT/patch_idem_dim.lean`)

These are the block-matrix calculations behind Milnor patching.  They are reproduced here so that
this file is independent of the (concurrently edited) source. -/

section BlockPieces

/-- The unipotent block matrix `[[1,X],[0,1]]`. -/
def blkA {R : Type} [Ring R] {a b : ℕ} (X : Matrix (Fin a) (Fin b) R) :
    Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R :=
  Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) R) X (0 : Matrix (Fin b) (Fin a) R)
    (1 : Matrix (Fin b) (Fin b) R)

/-- The unipotent block matrix `[[1,0],[Y,1]]`. -/
def blkC {R : Type} [Ring R] {a b : ℕ} (Y : Matrix (Fin b) (Fin a) R) :
    Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R :=
  Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) R) (0 : Matrix (Fin a) (Fin b) R) Y
    (1 : Matrix (Fin b) (Fin b) R)

/-- Product of the two unipotent block matrices. -/
lemma blkAC {R : Type} [Ring R] {a b : ℕ} (S : Matrix (Fin b) (Fin a) R)
    (T : Matrix (Fin a) (Fin b) R) :
    blkA T * blkC (-S) = Matrix.fromBlocks (1 - T * S) T (-S) (1 : Matrix (Fin b) (Fin b) R) := by
  simp only [blkA, blkC, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      sub_eq_add_neg, Matrix.neg_mul, Matrix.mul_neg] <;> abel

/-- The product `G = [[1,T],[0,1]] * [[1,0],[-S,1]] * [[1,T],[0,1]]` in block form. -/
lemma blkG {R : Type} [Ring R] {a b : ℕ} (S : Matrix (Fin b) (Fin a) R)
    (T : Matrix (Fin a) (Fin b) R) :
    blkA T * blkC (-S) * blkA T =
      Matrix.fromBlocks (1 - T * S) ((1 - T * S) * T + T) (-S) (1 - S * T) := by
  rw [blkAC]
  simp only [blkA, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      sub_eq_add_neg, Matrix.neg_mul, Matrix.mul_neg] <;> abel

/-- The unipotent block matrix is a unit with explicit inverse. -/
lemma blkA_mul {R : Type} [Ring R] {a b : ℕ} (T : Matrix (Fin a) (Fin b) R) :
    blkA T * blkA (-T) =
      Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) R) 0 0 (1 : Matrix (Fin b) (Fin b) R) := by
  simp only [blkA, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      sub_eq_add_neg, Matrix.neg_mul, Matrix.mul_neg] <;> abel

/-- The other unipotent block matrix is a unit with explicit inverse. -/
lemma blkC_mul {R : Type} [Ring R] {a b : ℕ} (S : Matrix (Fin b) (Fin a) R) :
    blkC (-S) * blkC S =
      Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) R) 0 0 (1 : Matrix (Fin b) (Fin b) R) := by
  simp only [blkC, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      sub_eq_add_neg, Matrix.neg_mul, Matrix.mul_neg] <;> abel


/-- **The block identity behind Milnor patching.**  If `p = T*S` and `q = S*T` are idempotent then
`G = blkA T * blkC (-S) * blkA T` satisfies `G * diag(0,q) = diag(p,0) * G`. -/
theorem patch_block_key {R : Type} [Ring R] {n₁ n₂ : ℕ}
    (p : Matrix (Fin n₁) (Fin n₁) R) (q : Matrix (Fin n₂) (Fin n₂) R)
    (S : Matrix (Fin n₂) (Fin n₁) R) (T : Matrix (Fin n₁) (Fin n₂) R)
    (hp : p * p = p) (hq : q * q = q) (hST : S * T = q) (hTS : T * S = p) :
    blkA T * blkC (-S) * blkA T * Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) R) 0 0 q =
    Matrix.fromBlocks p 0 0 (0 : Matrix (Fin n₂) (Fin n₂) R) * (blkA T * blkC (-S) * blkA T) := by
  have h1 : ((1 - T*S)*T)*q = 0 := by
    have h : (1 - T*S)*T = T - T*q := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hST]
    rw [h, Matrix.sub_mul, Matrix.mul_assoc, hq, sub_self]
  have h2 : (1 - S*T)*q = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hST, hq, sub_self]
  have h3 : p*(1 - T*S) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hTS, hp, sub_self]
  have h4 : p*T = T*q := by
    rw [← hTS, Matrix.mul_assoc, hST]
  have h5 : p*((1 - T*S)*T + T) = T*q := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, h3, Matrix.zero_mul, zero_add, h4]
  calc blkA T * blkC (-S) * blkA T * Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) R) 0 0 q
      = Matrix.fromBlocks (1 - T*S) ((1 - T*S)*T + T) (-S) (1 - S*T) *
          Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) R) 0 0 q := by rw [blkG]
    _ = Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) R) (T*q) 0 (0 : Matrix (Fin n₂) (Fin n₂) R) := by
        simp only [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [Matrix.mul_zero, add_zero]
        · rw [Matrix.mul_zero, zero_add, Matrix.add_mul, h1, zero_add]
        · simp only [Matrix.mul_zero, add_zero]
        · rw [Matrix.mul_zero, zero_add, h2]
    _ = Matrix.fromBlocks p 0 0 (0 : Matrix (Fin n₂) (Fin n₂) R) *
          Matrix.fromBlocks (1 - T*S) ((1 - T*S)*T + T) (-S) (1 - S*T) := by
        simp only [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Matrix.zero_mul, add_zero, h3]
        · rw [Matrix.zero_mul, add_zero, h5]
        · simp only [Matrix.zero_mul, add_zero]
        · simp only [Matrix.zero_mul, add_zero]
    _ = Matrix.fromBlocks p 0 0 (0 : Matrix (Fin n₂) (Fin n₂) R) * (blkA T * blkC (-S) * blkA T) := by
        rw [blkG]

/-- The conjugating element `blkA T * blkC (-S) * blkA T` is a unit. -/
theorem patch_block_unit {R : Type} [Ring R] {n₁ n₂ : ℕ}
    (S : Matrix (Fin n₂) (Fin n₁) R) (T : Matrix (Fin n₁) (Fin n₂) R) :
    (blkA T * blkC (-S) * blkA T) * (blkA (-T) * blkC S * blkA (-T)) =
      (1 : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) R) ∧
    (blkA (-T) * blkC S * blkA (-T)) * (blkA T * blkC (-S) * blkA T) =
      (1 : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) R) := by
  have hAA : blkA T * blkA (-T) = 1 := by rw [blkA_mul, Matrix.fromBlocks_one]
  have hA'A : blkA (-T) * blkA T = 1 := by
    have h := blkA_mul (-T); rw [neg_neg] at h; rw [h, Matrix.fromBlocks_one]
  have hCC : blkC (-S) * blkC S = 1 := by rw [blkC_mul, Matrix.fromBlocks_one]
  have hC'C : blkC S * blkC (-S) = 1 := by
    have h := blkC_mul (-S); rw [neg_neg] at h; rw [h, Matrix.fromBlocks_one]
  constructor
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (blkA T) (blkA (-T)), hAA, Matrix.one_mul,
      ← Matrix.mul_assoc (blkC (-S)) (blkC S), hCC, Matrix.one_mul, hAA]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (blkA (-T)) (blkA T), hA'A, Matrix.one_mul,
      ← Matrix.mul_assoc (blkC S) (blkC (-S)), hC'C, Matrix.one_mul, hA'A]

/-! ## 2. Reindexing, block sums and `K₀`-classes -/


/-- `Matrix.reindex` commutes with `Matrix.map`. -/
lemma reindex_map' {R S : Type} [Ring R] [Ring S] {ι ι' : Type} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (φ : R →+* S) (M : Matrix ι ι R) :
    (Matrix.reindex e e M).map φ = Matrix.reindex e e (M.map φ) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map]

/-- `Matrix.reindex` maps the identity to the identity. -/
lemma reindex_one' {R : Type} [Ring R] {ι ι' : Type} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι'] (e : ι ≃ ι') :
    Matrix.reindex e e (1 : Matrix ι ι R) = 1 := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply,
    e.symm.injective.eq_iff]


/-- Conjugate idempotents (by a unit) have equal `K₀`-class. -/
lemma cls_conj {R : Type} [Ring R] {m : ℕ} (p : Matrix (Fin m) (Fin m) R) (hp : p * p = p)
    (u v : Matrix (Fin m) (Fin m) R) (hvu : v * u = 1) :
    cls (⟨m, u * p * v⟩ : Mat R) = cls (⟨m, p⟩ : Mat R) := by
  have hide : Mat.IsIdem (⟨m, u * p * v⟩ : Mat R) := by
    show (u * p * v) * (u * p * v) = u * p * v
    calc (u * p * v) * (u * p * v)
        = (u * p) * (v * (u * p * v)) := Matrix.mul_assoc (u * p) v (u * p * v)
      _ = (u * p) * ((v * (u * p)) * v) := by rw [Matrix.mul_assoc v (u * p) v]
      _ = (u * p) * (((v * u) * p) * v) := by rw [Matrix.mul_assoc v u p]
      _ = (u * p) * ((1 * p) * v) := by rw [hvu]
      _ = (u * p) * (p * v) := by rw [Matrix.one_mul]
      _ = u * (p * (p * v)) := Matrix.mul_assoc u p (p * v)
      _ = u * ((p * p) * v) := by rw [Matrix.mul_assoc p p v]
      _ = u * (p * v) := by rw [hp]
      _ = u * p * v := (Matrix.mul_assoc u p v).symm
  exact (cls_eq_of_mvN (p := ⟨m, p⟩) (q := ⟨m, u * p * v⟩) hp hide
    ⟨u, p * v, by rw [Matrix.mul_assoc, hvu, Matrix.mul_one],
      by rw [← Matrix.mul_assoc]⟩).symm

end BlockPieces

/-! ## Milnor patching of idempotents -/

section GlueTools

variable {P Q : Type} [Ring P] [Ring Q]

/-- `Matrix.map` commutes with `Matrix.fromBlocks`. -/
lemma fromBlocks_map' (φ : P →+* Q) {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) P) (B : Matrix (Fin m) (Fin n) P)
    (C : Matrix (Fin n) (Fin m) P) (D : Matrix (Fin n) (Fin n) P) :
    (Matrix.fromBlocks A B C D).map φ =
      Matrix.fromBlocks (A.map φ) (B.map φ) (C.map φ) (D.map φ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.map_apply, Matrix.fromBlocks]

/-- Naturality of the unipotent block matrix `[[1,X],[0,1]]`. -/
lemma blkA_map (φ : P →+* Q) {a b : ℕ} (X : Matrix (Fin a) (Fin b) P) :
    (blkA X).map φ = blkA (X.map φ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blkA, Matrix.map_apply, Matrix.fromBlocks, Matrix.one_apply, map_zero]

/-- Naturality of the unipotent block matrix `[[1,0],[Y,1]]`. -/
lemma blkC_map (φ : P →+* Q) {a b : ℕ} (Y : Matrix (Fin b) (Fin a) P) :
    (blkC Y).map φ = blkC (Y.map φ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blkC, Matrix.map_apply, Matrix.fromBlocks, Matrix.one_apply, map_zero]

end GlueTools

/-- Matrices over `P` are determined by their two images. -/
lemma matrix_ext_of_maps {ι : Type*} {P P₁ P₂ Q : Type}
    [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {A B : Matrix ι ι P} (h1 : A.map ρ₁ = B.map ρ₁) (h2 : A.map ρ₂ = B.map ρ₂) : A = B := by
  ext i j
  have h1' : ρ₁ (B i j) = ρ₁ (A i j) := by
    have h := congrFun (congrFun h1 i) j
    simp only [Matrix.map_apply] at h
    exact h.symm
  have h2' : ρ₂ (B i j) = ρ₂ (A i j) := by
    have h := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply] at h
    exact h.symm
  have hx : σ₁ (ρ₁ (A i j)) = σ₂ (ρ₂ (A i j)) := by
    have h := congrArg (fun f : P →+* Q => f (A i j)) hcomm
    simpa [RingHom.comp_apply] using h
  exact (hpb (ρ₁ (A i j)) (ρ₂ (A i j)) hx).unique ⟨rfl, rfl⟩ ⟨h1', h2'⟩

/-- A pair of matrices over `P₁`, `P₂` whose entries match in `Q` is the pair of images of a
matrix over `P`. -/
lemma matrix_lift_pair {ι : Type*} {P P₁ P₂ Q : Type}
    [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    (N₁ : Matrix ι ι P₁) (N₂ : Matrix ι ι P₂)
    (h : ∀ i j, σ₁ (N₁ i j) = σ₂ (N₂ i j)) :
    ∃ E : Matrix ι ι P, E.map ρ₁ = N₁ ∧ E.map ρ₂ = N₂ := by
  let E : Matrix ι ι P := fun i j => (hpb (N₁ i j) (N₂ i j) (h i j)).choose
  have hE₁ : E.map ρ₁ = N₁ := by
    ext i j
    rw [Matrix.map_apply]
    dsimp only [E]
    exact (hpb (N₁ i j) (N₂ i j) (h i j)).choose_spec.1.1
  have hE₂ : E.map ρ₂ = N₂ := by
    ext i j
    rw [Matrix.map_apply]
    dsimp only [E]
    exact (hpb (N₁ i j) (N₂ i j) (h i j)).choose_spec.1.2
  exact ⟨E, hE₁, hE₂⟩

/-- The `Mat.snd` of a stabilised base change: `(F ⊕ 1).map φ` and `(F.map φ) ⊕ 1` have the
same underlying matrix. -/
lemma mat_snd_sum_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (F : Mat R) (s : ℕ) :
    ((F.map φ).sum (Mat.one S s)).2 = ((F.sum (Mat.one R s)).map φ).2 := by
  have hmat : ((F.sum (Mat.one R s)).map φ : Mat S) = ((F.map φ).sum (Mat.one S s) : Mat S) := by
    rw [map_sum, map_one]
  have hmat' : (⟨(F.1 + s), ((F.sum (Mat.one R s)).map φ).2⟩ : Mat S)
      = ⟨(F.1 + s), ((F.map φ).sum (Mat.one S s)).2⟩ := hmat
  exact (eq_of_heq (Sigma.mk.inj hmat').2).symm

/-- A matrix over a quotient lifts entrywise. -/
lemma matrix_lift_of_surjective {R S : Type} [Ring R] [Ring S] (φ : R →+* S)
    (hφ : Function.Surjective φ) {m n : ℕ} (M : Matrix (Fin m) (Fin n) S) :
    ∃ N : Matrix (Fin m) (Fin n) R, N.map φ = M := by
  refine ⟨M.map (fun s => Classical.choose (hφ s)), ?_⟩
  ext i j
  simp only [Matrix.map_apply]
  exact Classical.choose_spec (hφ (M i j))

/-- The conjugate of an idempotent by a unit is idempotent. -/
lemma conj_idem {R : Type} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u v p : Matrix ι ι R}
    (hp : p * p = p) (hvu : v * u = 1) : (u * p * v) * (u * p * v) = u * p * v := by
  have e1 : (u * p * v) * (u * p * v) = u * p * (v * u) * p * v := by noncomm_ring
  rw [e1, hvu]
  have e2 : u * p * 1 * p * v = u * (p * p) * v := by noncomm_ring
  rw [e2, hp]

/-- Reindexing a triple product of matrices along `finSumFinEquiv`. -/
lemma reindex_mul3 {R : Type} [Ring R] {a b : ℕ}
    (X Y Z : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (X * Y * Z) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv X *
        Matrix.reindex finSumFinEquiv finSumFinEquiv Y *
        Matrix.reindex finSumFinEquiv finSumFinEquiv Z := by
  rw [reindexMul, reindexMul]

/-- Reindexed conjugation preserves the `K₀`-class. -/
lemma cls_conj_reindex {R : Type} [Ring R] {a b : ℕ}
    (u v p : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R) (hp : p * p = p) (hvu : v * u = 1) :
    cls (⟨a + b, Matrix.reindex finSumFinEquiv finSumFinEquiv u *
        Matrix.reindex finSumFinEquiv finSumFinEquiv p *
        Matrix.reindex finSumFinEquiv finSumFinEquiv v⟩ : Mat R) =
      cls (⟨a + b, Matrix.reindex finSumFinEquiv finSumFinEquiv p⟩ : Mat R) :=
  cls_conj (Matrix.reindex finSumFinEquiv finSumFinEquiv p)
    (by rw [reindexMul, hp])
    (Matrix.reindex finSumFinEquiv finSumFinEquiv u)
    (Matrix.reindex finSumFinEquiv finSumFinEquiv v)
    (by rw [reindexMul, hvu, reindex_one'])

/-- **Milnor patching of idempotents (rectangular form)**: in a cartesian square of rings with the
leg `σ₂ : P₂ → Q` surjective, idempotents `e₁` (size `n₁`) over `P₁` and `e₂` (size `n₂`) over `P₂`
whose base changes to `Q` are Murray–von Neumann equivalent (rectangular witnesses `S : n₂ × n₁`,
`T : n₁ × n₂`) glue to an idempotent over `P` whose classes in `K₀ P₁`, `K₀ P₂` are those of the
two idempotents.

The construction (Milnor, *Introduction to algebraic K-theory*, §2; M. Land, *Algebraic K-theory*,
§4.3, Thm. 4.51 and Cor. 4.53): over `Q` the unipotent block matrix
`G = [[1,T],[0,1]] * [[1,0],[-S,1]] * [[1,T],[0,1]]` satisfies `G * diag(0,e₂) = diag(e₁,0) * G`.
As `G` is a product of unipotent factors it lifts *as a unit* to `P₂`; conjugating `diag(0,e₂)` by
that unit gives an idempotent over `P₂` with `Q`-image `diag(e₁,0)` and the class of `e₂`, while
`diag(e₁,0)` is an idempotent over `P₁` with that `Q`-image and the class of `e₁`. The pull-back
property `hpb` glues the two. -/
theorem glue_idem {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hs : Function.Surjective σ₂) (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {n₁ n₂ : ℕ} (e₁ : Matrix (Fin n₁) (Fin n₁) P₁) (e₂ : Matrix (Fin n₂) (Fin n₂) P₂)
    (he₁ : e₁ * e₁ = e₁) (he₂ : e₂ * e₂ = e₂)
    (S : Matrix (Fin n₂) (Fin n₁) Q) (T : Matrix (Fin n₁) (Fin n₂) Q)
    (hST : S * T = e₂.map σ₂) (hTS : T * S = e₁.map σ₁) :
    ∃ E : Mat P, E.IsIdem ∧ cls (E.map ρ₁) = cls (⟨n₁, e₁⟩ : Mat P₁) ∧
      cls (E.map ρ₂) = cls (⟨n₂, e₂⟩ : Mat P₂) := by
  -- lifts of the Murray–von Neumann witnesses to `P₂`
  obtain ⟨T₂, hT₂⟩ := matrix_lift_of_surjective σ₂ hs T
  obtain ⟨S₂, hS₂⟩ := matrix_lift_of_surjective σ₂ hs S
  -- `Matrix.map` commutes with negation, entrywise over `P₂`
  have map_neg₂ : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) P₂), (-M).map σ₂ = -(M.map σ₂) := by
    intro a b M
    ext i j
    simp [Matrix.map_apply]
  -- the unipotent conjugating unit over `P₂` and its inverse
  have hunit₁ : (blkA T₂ * blkC (-S₂) * blkA T₂) *
      (blkA (-T₂) * blkC S₂ * blkA (-T₂)) = 1 := (patch_block_unit S₂ T₂).1
  have hunit₂ : (blkA (-T₂) * blkC S₂ * blkA (-T₂)) *
      (blkA T₂ * blkC (-S₂) * blkA T₂) = 1 := (patch_block_unit S₂ T₂).2
  -- the same unit over `Q`
  have hunit₁Q : (blkA T * blkC (-S) * blkA T) * (blkA (-T) * blkC S * blkA (-T)) = 1 :=
    (patch_block_unit S T).1
  -- the unit maps to `G` over `Q`
  have hG : (blkA T₂ * blkC (-S₂) * blkA T₂).map σ₂ = blkA T * blkC (-S) * blkA T := by
    rw [Matrix.map_mul, Matrix.map_mul, blkA_map, blkC_map, hT₂, map_neg₂, hS₂]
  have hGinv : (blkA (-T₂) * blkC S₂ * blkA (-T₂)).map σ₂ = blkA (-T) * blkC S * blkA (-T) := by
    rw [Matrix.map_mul, Matrix.map_mul, blkA_map, blkC_map, map_neg₂, hT₂, hS₂]
  -- the corner idempotents over `P₂` and `P₁`
  have hM₂idem : (Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂) *
        (Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂) =
      Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂ := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, he₂]
  have hN₁idem : (Matrix.fromBlocks e₁ 0 0 (0 : Matrix (Fin n₂) (Fin n₂) P₁)) *
        (Matrix.fromBlocks e₁ 0 0 (0 : Matrix (Fin n₂) (Fin n₂) P₁)) =
      Matrix.fromBlocks e₁ 0 0 (0 : Matrix (Fin n₂) (Fin n₂) P₁) := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, he₁]
  -- the glued idempotent over `P₂`
  have hN₂idem : ((blkA T₂ * blkC (-S₂) * blkA T₂) *
          Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂ *
          (blkA (-T₂) * blkC S₂ * blkA (-T₂))) *
        ((blkA T₂ * blkC (-S₂) * blkA T₂) *
          Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂ *
          (blkA (-T₂) * blkC S₂ * blkA (-T₂))) =
      (blkA T₂ * blkC (-S₂) * blkA T₂) *
        Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂ *
        (blkA (-T₂) * blkC S₂ * blkA (-T₂)) :=
    conj_idem (u := blkA T₂ * blkC (-S₂) * blkA T₂)
      (v := blkA (-T₂) * blkC S₂ * blkA (-T₂))
      (p := Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂) hM₂idem hunit₂
  -- the images of the two corner idempotents over `Q`
  have hM₂map : (Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂).map σ₂ =
      Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) Q) 0 0 (e₂.map σ₂) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.map_apply, Matrix.fromBlocks]
  have hN₁map : (Matrix.fromBlocks e₁ 0 0 (0 : Matrix (Fin n₂) (Fin n₂) P₁)).map σ₁ =
      Matrix.fromBlocks (e₁.map σ₁) 0 0 (0 : Matrix (Fin n₂) (Fin n₂) Q) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.map_apply, Matrix.fromBlocks]
  have hkey := patch_block_key (e₁.map σ₁) (e₂.map σ₂) S T
    (by rw [← Matrix.map_mul, he₁]) (by rw [← Matrix.map_mul, he₂]) hST hTS
  have hN₂map : ((blkA T₂ * blkC (-S₂) * blkA T₂) *
        Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂ *
        (blkA (-T₂) * blkC S₂ * blkA (-T₂))).map σ₂ =
      Matrix.fromBlocks (e₁.map σ₁) 0 0 (0 : Matrix (Fin n₂) (Fin n₂) Q) := by
    rw [Matrix.map_mul, Matrix.map_mul, hG, hGinv, hM₂map, hkey]
    have e : Matrix.fromBlocks (e₁.map σ₁) 0 0 (0 : Matrix (Fin n₂) (Fin n₂) Q) *
        (blkA T * blkC (-S) * blkA T) * (blkA (-T) * blkC S * blkA (-T)) =
        Matrix.fromBlocks (e₁.map σ₁) 0 0 (0 : Matrix (Fin n₂) (Fin n₂) Q) *
          ((blkA T * blkC (-S) * blkA T) * (blkA (-T) * blkC S * blkA (-T))) :=
      Matrix.mul_assoc _ _ _
    rw [e, hunit₁Q, Matrix.mul_one]
  -- the two images agree, so `hpb` glues them
  have hpair : ∀ i j,
      σ₁ ((Matrix.fromBlocks e₁ 0 0 (0 : Matrix (Fin n₂) (Fin n₂) P₁)) i j) =
      σ₂ (((blkA T₂ * blkC (-S₂) * blkA T₂) *
        Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂ *
        (blkA (-T₂) * blkC S₂ * blkA (-T₂))) i j) := by
    intro i j
    have h : (Matrix.fromBlocks e₁ 0 0 (0 : Matrix (Fin n₂) (Fin n₂) P₁)).map σ₁ =
        ((blkA T₂ * blkC (-S₂) * blkA T₂) *
          Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂ *
          (blkA (-T₂) * blkC S₂ * blkA (-T₂))).map σ₂ := by rw [hN₁map, hN₂map]
    exact congrFun (congrFun h i) j
  obtain ⟨E, hE₁, hE₂⟩ :=
    matrix_lift_pair ρ₁ ρ₂ σ₁ σ₂ hpb
      (Matrix.fromBlocks e₁ 0 0 (0 : Matrix (Fin n₂) (Fin n₂) P₁))
      ((blkA T₂ * blkC (-S₂) * blkA T₂) *
        Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂ *
        (blkA (-T₂) * blkC S₂ * blkA (-T₂))) hpair
  -- the glued matrix over `P`, its idempotency and its classes
  refine ⟨⟨n₁ + n₂, Matrix.reindex finSumFinEquiv finSumFinEquiv E⟩, ?_, ?_, ?_⟩
  · show (Matrix.reindex finSumFinEquiv finSumFinEquiv E) *
        (Matrix.reindex finSumFinEquiv finSumFinEquiv E) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv E
    rw [reindexMul]
    congr 1
    refine matrix_ext_of_maps ρ₁ ρ₂ σ₁ σ₂ hcomm hpb ?_ ?_
    · rw [Matrix.map_mul, hE₁, hN₁idem]
    · rw [Matrix.map_mul, hE₂, hN₂idem]
  · show cls (⟨n₁ + n₂, (Matrix.reindex finSumFinEquiv finSumFinEquiv E).map ρ₁⟩ : Mat P₁) =
      cls (⟨n₁, e₁⟩ : Mat P₁)
    have hmat : (⟨n₁ + n₂, (Matrix.reindex finSumFinEquiv finSumFinEquiv E).map ρ₁⟩ : Mat P₁) =
        Mat.sum (⟨n₁, e₁⟩ : Mat P₁) (⟨n₂, (0 : Matrix (Fin n₂) (Fin n₂) P₁)⟩ : Mat P₁) := by
      show (⟨n₁ + n₂, (Matrix.reindex finSumFinEquiv finSumFinEquiv E).map ρ₁⟩ : Mat P₁) = _
      rw [reindex_map', hE₁]
      rfl
    have hid₁ : Mat.IsIdem (⟨n₁, e₁⟩ : Mat P₁) := he₁
    have hid₂ : Mat.IsIdem (⟨n₂, (0 : Matrix (Fin n₂) (Fin n₂) P₁)⟩ : Mat P₁) := by
      show (0 : Matrix (Fin n₂) (Fin n₂) P₁) * 0 = 0
      simp
    rw [hmat, cls_sum hid₁ hid₂, cls_zero n₂, add_zero]
  · show cls (⟨n₁ + n₂, (Matrix.reindex finSumFinEquiv finSumFinEquiv E).map ρ₂⟩ : Mat P₂) =
      cls (⟨n₂, e₂⟩ : Mat P₂)
    have hconj : (Matrix.reindex finSumFinEquiv finSumFinEquiv E).map ρ₂ =
        Matrix.reindex finSumFinEquiv finSumFinEquiv (blkA T₂ * blkC (-S₂) * blkA T₂) *
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂) *
        Matrix.reindex finSumFinEquiv finSumFinEquiv (blkA (-T₂) * blkC S₂ * blkA (-T₂)) := by
      rw [reindex_map', hE₂]
      exact reindex_mul3 _ _ _
    rw [hconj, cls_conj_reindex (blkA T₂ * blkC (-S₂) * blkA T₂)
      (blkA (-T₂) * blkC S₂ * blkA (-T₂))
      (Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂) hM₂idem hunit₂]
    have hsum : (⟨n₁ + n₂, Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂)⟩ : Mat P₂) =
        Mat.sum (⟨n₁, (0 : Matrix (Fin n₁) (Fin n₁) P₂)⟩ : Mat P₂) (⟨n₂, e₂⟩ : Mat P₂) :=
      rfl
    have hid₁ : Mat.IsIdem (⟨n₁, (0 : Matrix (Fin n₁) (Fin n₁) P₂)⟩ : Mat P₂) := by
      show (0 : Matrix (Fin n₁) (Fin n₁) P₂) * 0 = 0
      simp
    have hid₂ : Mat.IsIdem (⟨n₂, e₂⟩ : Mat P₂) := he₂
    rw [hsum, cls_sum hid₁ hid₂, cls_zero n₁, zero_add]

/-! ## Mayer–Vietoris surjectivity -/

/-- **Mayer–Vietoris surjectivity (Milnor patching) for `K₀`.**  In a cartesian square of rings
`ρ₁ : P → P₁`, `ρ₂ : P → P₂`, `σ₁ : P₁ → Q`, `σ₂ : P₂ → Q` with `σ₂` surjective, `K₀ P` surjects
onto the pairs of `K₀ P₁ × K₀ P₂` that agree in `K₀ Q`.-/
theorem mv_surj {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hs : Function.Surjective σ₂) (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂) :
    ∀ z₁ z₂, K0.map σ₁ z₁ = K0.map σ₂ z₂ → ∃ z, K0.map ρ₁ z = z₁ ∧ K0.map ρ₂ z = z₂ := by
  intro z₁ z₂ hz
  obtain ⟨F₁, n₁, hid₁, hz₁⟩ := k0_rep z₁
  obtain ⟨F₂, n₂, hid₂, hz₂⟩ := k0_rep z₂
  -- shift so that both negative parts are the identity of size `n₁ + n₂`
  have hz₁' : z₁ = cls (F₁.sum (Mat.one P₁ n₂)) - cls (Mat.one P₁ (n₁ + n₂)) := by
    rw [hz₁, shift_rep (R := P₁) (n := n₁) hid₁ (m := n₂)]
  have hz₂' : z₂ = cls (F₂.sum (Mat.one P₂ n₁)) - cls (Mat.one P₂ (n₁ + n₂)) := by
    have h := shift_rep (R := P₂) (n := n₂) hid₂ (m := n₁)
    rw [hz₂, h, Nat.add_comm n₂ n₁]
  -- the stabilised idempotents
  set E₁ : Mat P₁ := F₁.sum (Mat.one P₁ n₂) with hE₁
  set E₂ : Mat P₂ := F₂.sum (Mat.one P₂ n₁) with hE₂
  have hidE₁ : E₁.IsIdem := Mat.sum_idem hid₁ (one_idem n₂)
  have hidE₂ : E₂.IsIdem := Mat.sum_idem hid₂ (one_idem n₁)
  -- the class condition after stabilising
  have hz' : K0.map σ₁ (cls E₁ - cls (Mat.one P₁ (n₁ + n₂))) =
      K0.map σ₂ (cls E₂ - cls (Mat.one P₂ (n₁ + n₂))) := by
    rw [← hz₁', ← hz₂']
    exact hz
  have hcls1 : K0.map σ₁ (cls E₁ - cls (Mat.one P₁ (n₁ + n₂))) =
      cls (E₁.map σ₁) - cls (Mat.one Q (n₁ + n₂)) := by
    rw [map_sub, map_cls σ₁ E₁ hidE₁, map_cls σ₁ (Mat.one P₁ (n₁ + n₂)) (one_idem _),
      map_one]
  have hcls2 : K0.map σ₂ (cls E₂ - cls (Mat.one P₂ (n₁ + n₂))) =
      cls (E₂.map σ₂) - cls (Mat.one Q (n₁ + n₂)) := by
    rw [map_sub, map_cls σ₂ E₂ hidE₂, map_cls σ₂ (Mat.one P₂ (n₁ + n₂)) (one_idem _),
      map_one]
  have hcl : cls (E₁.map σ₁) = cls (E₂.map σ₂) := by
    rw [hcls1, hcls2] at hz'
    have h := congrArg (fun x => x + cls (Mat.one Q (n₁ + n₂))) hz'
    simpa using h
  -- stable Murray–von Neumann data over `Q`
  obtain ⟨s, S, T, hTS, hST⟩ :=
    (cls_eq_stable_mvN (E₁.map σ₁) (E₂.map σ₂) (Mat.map_idem σ₁ hidE₁)
      (Mat.map_idem σ₂ hidE₂)).mp hcl
  -- the glueing
  have hmat₁ : (E₁.sum (Mat.one P₁ s)).map σ₁ = (E₁.map σ₁).sum (Mat.one Q s) := by
    rw [map_sum, map_one]
  have hmat₂ : (E₂.sum (Mat.one P₂ s)).map σ₂ = (E₂.map σ₂).sum (Mat.one Q s) := by
    rw [map_sum, map_one]
  have hTS' : T * S = ((E₁.sum (Mat.one P₁ s)).map σ₁).2 := by
    rw [← mat_snd_sum_map σ₁ E₁ s]
    exact hTS
  have hST' : S * T = ((E₂.sum (Mat.one P₂ s)).map σ₂).2 := by
    rw [← mat_snd_sum_map σ₂ E₂ s]
    exact hST
  obtain ⟨Ê, hidÊ, hÊ₁, hÊ₂⟩ :=
    glue_idem (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂) hs hcomm hpb
      (e₁ := (E₁.sum (Mat.one P₁ s)).2) (e₂ := (E₂.sum (Mat.one P₂ s)).2)
      (Mat.sum_idem hidE₁ (one_idem s)) (Mat.sum_idem hidE₂ (one_idem s)) S T hST' hTS'
  have hÊ₁' : cls (Ê.map ρ₁) = cls (E₁.sum (Mat.one P₁ s)) := hÊ₁
  have hÊ₂' : cls (Ê.map ρ₂) = cls (E₂.sum (Mat.one P₂ s)) := hÊ₂
  refine ⟨cls Ê - cls (Mat.one P (n₁ + n₂ + s)), ?_, ?_⟩
  · rw [map_sub, map_cls ρ₁ Ê hidÊ, map_cls ρ₁ (Mat.one P (n₁ + n₂ + s)) (one_idem _), map_one,
      hÊ₁', cls_sum hidE₁ (one_idem s), cls_one_add (n₁ + n₂) s]
    rw [hz₁']
    abel
  · rw [map_sub, map_cls ρ₂ Ê hidÊ, map_cls ρ₂ (Mat.one P (n₁ + n₂ + s)) (one_idem _), map_one,
      hÊ₂', cls_sum hidE₂ (one_idem s), cls_one_add (n₁ + n₂) s]
    rw [hz₂']
    abel

end

end Work.KT.Cone
