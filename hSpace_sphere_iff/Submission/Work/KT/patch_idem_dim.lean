import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic

/-!
# Milnor patching of idempotents (rectangular form)

Proof of `Work.KT.patch_idem_dim`.  The mathematical content is Milnor's patching theorem: for a
cartesian square of rings

```
P --ρ₁--> P₁
|          |
ρ₂         σ₁
v          v
P₂ --σ₂--> Q
```

with `σ₂` surjective, idempotents `e₁` over `P₁` and `e₂` over `P₂` whose base changes to `Q` are
Murray–von Neumann equivalent (rectangular witnesses `S`,`T`) glue to an idempotent `Ê` over `P`
whose classes in `K₀ P₁`, `K₀ P₂` are those of `e₁`,`e₂`.

The construction: over `Q` let `p = e₁.map σ₁`, `q = e₂.map σ₂`, and

`G = [[1,T],[0,1]] * [[1,0],[-S,1]] * [[1,T],[0,1]]  ∈ M_{n₁+n₂}(Q)`.

`G` is a product of two unipotent matrices and `G * diag(0,q) = diag(p,0) * G`.  Since `σ₂` is
surjective, `G` lifts *entrywise as a product of unipotents* to a unit `G₂` over `P₂` (no unit
lifting problem arises).  Then `N₂ = G₂ · diag(0,e₂) · G₂⁻¹` is an idempotent over `P₂` with the same
classes as `e₂` and Q-image `diag(p,0)`, while `N₁ = diag(e₁,0)` is an idempotent over `P₁` with
Q-image `diag(p,0)` and the same class as `e₁`.  The pullback property `hpb` glues `N₁` and `N₂`
to `Ê`.
-/

namespace Work.KT

open Matrix

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## 1. Block matrices and the conjugating unit -/

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
private lemma reindex_one' {R : Type} [Ring R] {ι ι' : Type} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι'] (e : ι ≃ ι') :
    Matrix.reindex e e (1 : Matrix ι ι R) = 1 := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply,
    e.symm.injective.eq_iff]

/-- `Matrix.map` along a ring hom commutes with negation. -/
lemma Matrix.map_neg' {R S : Type} [Ring R] [Ring S] {m n : Type} (φ : R →+* S)
    (M : Matrix m n R) : (-M).map φ = -(M.map φ) := by
  ext i j
  simp [Matrix.map_apply]

/-- `Mat.map` commutes with the block sum. -/
lemma Mat.map_sum {A B : Type} [Ring A] [Ring B] (φ : A →+* B) (p q : Mat A) :
    (p.sum q).map φ = (p.map φ).sum (q.map φ) := by
  obtain ⟨n, M⟩ := p
  obtain ⟨k, N⟩ := q
  refine congrArg (fun z => (⟨n + k, z⟩ : Mat B)) ?_
  show (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M 0 0 N)).map φ =
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (M.map ⇑φ) 0 0 (N.map ⇑φ))
  rw [reindex_map', Matrix.fromBlocks_map]
  simp only [Matrix.map_zero, map_zero]

/-- The zero matrix of any size has `K₀`-class `0`. -/
lemma cls_zero_mat {R : Type} [Ring R] (n : ℕ) : cls (⟨n, 0⟩ : Mat R) = 0 := by
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

/-- Conjugate idempotents (by a unit) have equal `K₀`-class. -/
private lemma cls_conj {R : Type} [Ring R] {m : ℕ} (p : Matrix (Fin m) (Fin m) R) (hp : p * p = p)
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

/-! ## 3. Gluing along the pullback square -/

/-- Matrices over `P` are determined by their two images. -/
lemma mat_ext_of_maps {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {m : ℕ} {A B : Matrix (Fin m) (Fin m) P}
    (h1 : A.map ρ₁ = B.map ρ₁) (h2 : A.map ρ₂ = B.map ρ₂) : A = B := by
  ext i j
  have h1' : ρ₁ (A i j) = ρ₁ (B i j) := by
    have h := congrFun (congrFun h1 i) j
    rwa [Matrix.map_apply, Matrix.map_apply] at h
  have h2' : ρ₂ (A i j) = ρ₂ (B i j) := by
    have h := congrFun (congrFun h2 i) j
    rwa [Matrix.map_apply, Matrix.map_apply] at h
  exact (hpb (ρ₁ (A i j)) (ρ₂ (A i j)) (by
    show σ₁ (ρ₁ (A i j)) = σ₂ (ρ₂ (A i j))
    rw [← RingHom.comp_apply, hcomm, RingHom.comp_apply])).unique
    ⟨rfl, rfl⟩ ⟨h1'.symm, h2'.symm⟩

/-- A pair of matrices with matching images in `Q` is the pair of images of a matrix over `P`. -/
lemma mat_lift {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {m : ℕ} (N₁ : Matrix (Fin m) (Fin m) P₁) (N₂ : Matrix (Fin m) (Fin m) P₂)
    (h : ∀ i j, σ₁ (N₁ i j) = σ₂ (N₂ i j)) :
    ∃ Ê : Matrix (Fin m) (Fin m) P, Ê.map ρ₁ = N₁ ∧ Ê.map ρ₂ = N₂ := by
  refine ⟨(fun i j => (hpb (N₁ i j) (N₂ i j) (h i j)).choose : Matrix (Fin m) (Fin m) P), ?_, ?_⟩
  · ext i j
    exact (Exists.choose_spec (hpb (N₁ i j) (N₂ i j) (h i j))).1.1
  · ext i j
    exact (Exists.choose_spec (hpb (N₁ i j) (N₂ i j) (h i j))).1.2

/-! ## 4. The patching theorem -/

/-- **Milnor patching of idempotents (rectangular form)**: in a cartesian square of rings with the leg `σ₂ : P₂ → Q` surjective, idempotents `e₁` (size `n₁`) over `P₁` and `e₂` (size `n₂`) over `P₂` whose base changes to `Q` are Murray–von Neumann equivalent (rectangular witnesses `S : n₂ × n₁`, `T : n₁ × n₂`) glue to an idempotent over `P` whose classes in `K₀ P₁`, `K₀ P₂` are those of the two idempotents.  Reference: M. Land, *Algebraic K-theory*, §4.3 (Milnor patching), Theorem 4.51 and Corollary 4.53 (the module `M(P,Q,α)` constructed there becomes the idempotent `Ê` here). -/
theorem patch_idem_dim {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hs : Function.Surjective σ₂) (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {n₁ n₂ : ℕ} (e₁ : Matrix (Fin n₁) (Fin n₁) P₁) (e₂ : Matrix (Fin n₂) (Fin n₂) P₂)
    (he₁ : e₁ * e₁ = e₁) (he₂ : e₂ * e₂ = e₂)
    (S : Matrix (Fin n₂) (Fin n₁) Q) (T : Matrix (Fin n₁) (Fin n₂) Q)
    (hST : S * T = e₂.map σ₂) (hTS : T * S = e₁.map σ₁) :
    ∃ Ê : Mat P, Ê.IsIdem ∧ cls (Ê.map ρ₁) = cls (⟨n₁, e₁⟩ : Mat P₁) ∧
      cls (Ê.map ρ₂) = cls (⟨n₂, e₂⟩ : Mat P₂) := by
  -- lifts of the Murray–von Neumann witnesses to `P₂`
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Matrix (Fin n₁) (Fin n₂) P₂, T₀.map σ₂ = T :=
    ⟨fun i j => (hs (T i j)).choose, by
      ext i j; exact (hs (T i j)).choose_spec⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Matrix (Fin n₂) (Fin n₁) P₂, S₀.map σ₂ = S :=
    ⟨fun i j => (hs (S i j)).choose, by
      ext i j; exact (hs (S i j)).choose_spec⟩
  -- the base changes of `e₁` and `e₂` over `Q`
  set p : Matrix (Fin n₁) (Fin n₁) Q := e₁.map σ₁ with hp
  set q : Matrix (Fin n₂) (Fin n₂) Q := e₂.map σ₂ with hq
  have hp_idem : p * p = p := by rw [hp, ← Matrix.map_mul, he₁]
  have hq_idem : q * q = q := by rw [hq, ← Matrix.map_mul, he₂]
  have hST' : S * T = q := by rw [hq]; exact hST
  have hTS' : T * S = p := by rw [hp]; exact hTS
  -- the Q-side idempotents `diag(p,0)` and `diag(0,q)`
  have hblocks : (blkA T * blkC (-S) * blkA T) *
        Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) Q) 0 0 q =
      Matrix.fromBlocks p 0 0 (0 : Matrix (Fin n₂) (Fin n₂) Q) * (blkA T * blkC (-S) * blkA T) :=
    patch_block_key p q S T hp_idem hq_idem hST' hTS'
  have hunit : (blkA T * blkC (-S) * blkA T) * (blkA (-T) * blkC S * blkA (-T)) = 1 ∧
      (blkA (-T) * blkC S * blkA (-T)) * (blkA T * blkC (-S) * blkA T) = 1 :=
    patch_block_unit S T
  -- the matrices on the two sides
  set A₂ : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) P₂ :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (blkA T₀) with hA₂
  set C₂ : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) P₂ :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (blkC (-S₀)) with hC₂
  set A₂i : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) P₂ :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (blkA (-T₀)) with hA₂i
  set C₂i : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) P₂ :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (blkC S₀) with hC₂i
  set G₂ : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) P₂ := A₂ * C₂ * A₂ with hG₂
  set G₂i : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) P₂ := A₂i * C₂i * A₂i with hG₂i
  set D₂P : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) P₂ :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) P₂) 0 0 e₂) with hD₂P
  set N₂ : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) P₂ := G₂ * D₂P * G₂i with hN₂
  set N₁ : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) P₁ :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks e₁ 0 0 (0 : Matrix (Fin n₂) (Fin n₂) P₁)) with hN₁
  -- `G₂` is a unit
  have hG₂eq : G₂ = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (blkA T₀ * blkC (-S₀) * blkA T₀) := by
    rw [hG₂, hA₂, hC₂, reindexMul finSumFinEquiv finSumFinEquiv finSumFinEquiv,
      reindexMul finSumFinEquiv finSumFinEquiv finSumFinEquiv]
  have hG₂ieq : G₂i = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (blkA (-T₀) * blkC S₀ * blkA (-T₀)) := by
    rw [hG₂i, hA₂i, hC₂i, reindexMul finSumFinEquiv finSumFinEquiv finSumFinEquiv,
      reindexMul finSumFinEquiv finSumFinEquiv finSumFinEquiv]
  have hunit₂ : G₂ * G₂i = 1 ∧ G₂i * G₂ = 1 := by
    constructor
    · rw [hG₂eq, hG₂ieq, reindexMul finSumFinEquiv finSumFinEquiv finSumFinEquiv,
        (patch_block_unit S₀ T₀).1, reindex_one']
    · rw [hG₂eq, hG₂ieq, reindexMul finSumFinEquiv finSumFinEquiv finSumFinEquiv,
        (patch_block_unit S₀ T₀).2, reindex_one']
  -- idempotency of `N₂`
  have hD₂idem : D₂P * D₂P = D₂P := by
    rw [hD₂P]
    exact Mat.sum_idem (p := (⟨n₁, (0 : Matrix (Fin n₁) (Fin n₁) P₂)⟩ : Mat P₂)) (q := ⟨n₂, e₂⟩)
      (by show (0 : Matrix (Fin n₁) (Fin n₁) P₂) * 0 = 0; simp) he₂
  have hN₁idem : N₁ * N₁ = N₁ := by
    rw [hN₁]
    exact Mat.sum_idem (p := (⟨n₁, e₁⟩ : Mat P₁))
      (q := ⟨n₂, (0 : Matrix (Fin n₂) (Fin n₂) P₁)⟩) he₁
      (by show (0 : Matrix (Fin n₂) (Fin n₂) P₁) * 0 = 0; simp)
  have hN₂idem : N₂ * N₂ = N₂ := by
    rw [hN₂]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G₂i G₂ (D₂P * G₂i), hunit₂.2, Matrix.one_mul,
      ← Matrix.mul_assoc D₂P D₂P G₂i, hD₂idem]
  -- the images in `Q` agree
  have hG₂map : G₂.map σ₂ = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (blkA T * blkC (-S) * blkA T) := by
    rw [hG₂eq, reindex_map']
    congr 1
    simp only [Matrix.map_mul, blkA, blkC, Matrix.fromBlocks_map, Matrix.map_one,
      Matrix.map_zero, Matrix.map_neg', map_zero, map_one, hT₀, hS₀]
  have hG₂imap : G₂i.map σ₂ = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (blkA (-T) * blkC S * blkA (-T)) := by
    rw [hG₂ieq, reindex_map']
    congr 1
    simp only [Matrix.map_mul, blkA, blkC, Matrix.fromBlocks_map, Matrix.map_one,
      Matrix.map_zero, Matrix.map_neg', map_zero, map_one, hT₀, hS₀, neg_neg]
  have hD₂map : D₂P.map σ₂ = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) Q) 0 0 q) := by
    rw [hD₂P, reindex_map']
    congr 1
    simp only [Matrix.fromBlocks_map, Matrix.map_zero, map_zero, ← hq]
  have hN₂map : N₂.map σ₂ = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks p 0 0 (0 : Matrix (Fin n₂) (Fin n₂) Q)) := by
    rw [hN₂, Matrix.map_mul, Matrix.map_mul, hG₂map, hD₂map, hG₂imap,
      reindexMul finSumFinEquiv finSumFinEquiv finSumFinEquiv,
      reindexMul finSumFinEquiv finSumFinEquiv finSumFinEquiv]
    congr 1
    rw [hblocks, Matrix.mul_assoc, hunit.1, Matrix.mul_one]
  have hN₁map : N₁.map σ₁ = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks p 0 0 (0 : Matrix (Fin n₂) (Fin n₂) Q)) := by
    rw [hN₁, reindex_map']
    congr 1
    simp only [Matrix.fromBlocks_map, Matrix.map_zero, map_zero, ← hp]
  -- glue
  have hcompat : ∀ i j, σ₁ (N₁ i j) = σ₂ (N₂ i j) := by
    intro i j
    have h1 : (N₁.map σ₁) i j = σ₁ (N₁ i j) := Matrix.map_apply
    have h2 : (N₂.map σ₂) i j = σ₂ (N₂ i j) := Matrix.map_apply
    rw [← h1, ← h2, hN₁map, hN₂map]
  obtain ⟨Êmat, hÊ₁, hÊ₂⟩ := mat_lift ρ₁ ρ₂ σ₁ σ₂ hpb N₁ N₂ hcompat
  refine ⟨(⟨n₁ + n₂, Êmat⟩ : Mat P), ?_, ?_, ?_⟩
  · -- idempotency, by the uniqueness in `hpb`
    show Êmat * Êmat = Êmat
    refine mat_ext_of_maps ρ₁ ρ₂ σ₁ σ₂ hcomm hpb ?_ ?_
    · rw [Matrix.map_mul, hÊ₁, hN₁idem]
    · rw [Matrix.map_mul, hÊ₂, hN₂idem]
  · -- the class over `P₁`
    have hm₁ : Mat.map ρ₁ (⟨n₁ + n₂, Êmat⟩ : Mat P) = ⟨n₁ + n₂, N₁⟩ :=
      congrArg (fun X => (⟨n₁ + n₂, X⟩ : Mat P₁)) hÊ₁
    rw [hm₁]
    have hsum₁ : (⟨n₁ + n₂, N₁⟩ : Mat P₁) = Mat.sum (⟨n₁, e₁⟩ : Mat P₁)
        ⟨n₂, (0 : Matrix (Fin n₂) (Fin n₂) P₁)⟩ :=
      Sigma.ext rfl (heq_of_eq (by rw [hN₁, Mat.sum_snd]))
    rw [hsum₁, cls_sum (p := (⟨n₁, e₁⟩ : Mat P₁))
      (q := (⟨n₂, (0 : Matrix (Fin n₂) (Fin n₂) P₁)⟩ : Mat P₁)) he₁ (by simp [Mat.IsIdem]),
      cls_zero_mat, add_zero]
  · -- the class over `P₂`
    have hm₂ : Mat.map ρ₂ (⟨n₁ + n₂, Êmat⟩ : Mat P) = ⟨n₁ + n₂, N₂⟩ :=
      congrArg (fun X => (⟨n₁ + n₂, X⟩ : Mat P₂)) hÊ₂
    rw [hm₂]
    have hconj : cls (⟨n₁ + n₂, N₂⟩ : Mat P₂) = cls (⟨n₁ + n₂, D₂P⟩ : Mat P₂) := by
      rw [hN₂]
      exact cls_conj D₂P hD₂idem G₂ G₂i hunit₂.2
    rw [hconj]
    have hsum₂ : (⟨n₁ + n₂, D₂P⟩ : Mat P₂) = Mat.sum
        (⟨n₁, (0 : Matrix (Fin n₁) (Fin n₁) P₂)⟩ : Mat P₂) ⟨n₂, e₂⟩ :=
      Sigma.ext rfl (heq_of_eq (by rw [hD₂P, Mat.sum_snd]))
    rw [hsum₂, cls_sum (p := (⟨n₁, (0 : Matrix (Fin n₁) (Fin n₁) P₂)⟩ : Mat P₂))
      (q := (⟨n₂, e₂⟩ : Mat P₂)) (by simp [Mat.IsIdem]) he₂, cls_zero_mat, zero_add]

end

end Work.KT
