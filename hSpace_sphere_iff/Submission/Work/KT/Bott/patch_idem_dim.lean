import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.FPatch

namespace Work.KT.Bott

open Matrix
open Work.KT

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Block matrices and the conjugating unit

The Mathlib-free core of Milnor's patching: over any ring, the matrix
`G = [[1,T],[0,1]] * [[1,0],[-S,1]] * [[1,T],[0,1]]` is a unit which intertwines
`diag(0, S*T)` with `diag(T*S, 0)`. -/

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

lemma blkAC {R : Type} [Ring R] {a b : ℕ} (S : Matrix (Fin b) (Fin a) R)
    (T : Matrix (Fin a) (Fin b) R) :
    blkA T * blkC (-S) = Matrix.fromBlocks (1 - T * S) T (-S) (1 : Matrix (Fin b) (Fin b) R) := by
  simp only [blkA, blkC, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      sub_eq_add_neg, Matrix.neg_mul, Matrix.mul_neg] <;> abel

lemma blkG {R : Type} [Ring R] {a b : ℕ} (S : Matrix (Fin b) (Fin a) R)
    (T : Matrix (Fin a) (Fin b) R) :
    blkA T * blkC (-S) * blkA T =
      Matrix.fromBlocks (1 - T * S) ((1 - T * S) * T + T) (-S) (1 - S * T) := by
  rw [blkAC]
  simp only [blkA, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      sub_eq_add_neg, Matrix.neg_mul, Matrix.mul_neg] <;> abel

lemma blkA_mul {R : Type} [Ring R] {a b : ℕ} (T : Matrix (Fin a) (Fin b) R) :
    blkA T * blkA (-T) =
      Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) R) 0 0 (1 : Matrix (Fin b) (Fin b) R) := by
  simp only [blkA, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      sub_eq_add_neg, Matrix.neg_mul, Matrix.mul_neg] <;> abel

lemma blkC_mul {R : Type} [Ring R] {a b : ℕ} (S : Matrix (Fin b) (Fin a) R) :
    blkC (-S) * blkC S =
      Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) R) 0 0 (1 : Matrix (Fin b) (Fin b) R) := by
  simp only [blkC, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      sub_eq_add_neg, Matrix.neg_mul, Matrix.mul_neg] <;> abel

lemma blkA_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) {a b : ℕ}
    (X : Matrix (Fin a) (Fin b) R) : (blkA X).map φ = blkA (X.map φ) := by
  unfold blkA
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_inj]
  exact ⟨Matrix.map_one _ (map_zero φ) (map_one φ), rfl,
    Matrix.map_zero _ (map_zero φ), Matrix.map_one _ (map_zero φ) (map_one φ)⟩

lemma blkC_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) {a b : ℕ}
    (Y : Matrix (Fin b) (Fin a) R) : (blkC Y).map φ = blkC (Y.map φ) := by
  unfold blkC
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_inj]
  exact ⟨Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_zero _ (map_zero φ), rfl,
    Matrix.map_one _ (map_zero φ) (map_one φ)⟩

lemma map_neg_mat {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) A) : (-M).map φ = -(M.map φ) :=
  Matrix.map_neg (⇑φ) (map_neg φ) M

/-- Conjugating an idempotent by a unit gives an idempotent. -/
lemma conj_idem {M : Type} [Monoid M] (G G' D : M) (h : G' * G = 1) (hD : D * D = D) :
    (G * D * G') * (G * D * G') = G * D * G' := by
  calc (G * D * G') * (G * D * G')
      = G * (D * (G' * (G * (D * G')))) := by simp only [mul_assoc]
    _ = G * (D * (D * G')) := by rw [← mul_assoc G' G (D * G'), h, one_mul]
    _ = G * (D * G') := by rw [← mul_assoc D D G', hD]
    _ = G * D * G' := by rw [mul_assoc]

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

/-! ## Reindexing and `K₀`-classes -/

lemma reindex_map_bott {R S : Type} [Ring R] [Ring S] {ι ι' : Type} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (φ : R →+* S) (M : Matrix ι ι R) :
    (Matrix.reindex e e M).map φ = Matrix.reindex e e (M.map φ) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map]

lemma reindex_one_bott {R : Type} [Ring R] {ι ι' : Type} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι'] (e : ι ≃ ι') :
    Matrix.reindex e e (1 : Matrix ι ι R) = 1 := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : e.symm i ≠ e.symm j := fun hh => h (e.symm.injective hh)
    rw [if_neg h', if_neg h]

/-- The zero matrix of any size has `K₀`-class `0`. -/
lemma cls_zero_mat_bott {R : Type} [Ring R] (n : ℕ) : cls (⟨n, 0⟩ : Mat R) = 0 := by
  have hzero : Mat.IsIdem (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) := by
    show (0 : Matrix (Fin 0) (Fin 0) R) * 0 = 0
    simp
  have hself : Mat.sum (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R)
      (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) =
      (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) := by
    refine Sigma.ext (by rfl) ?_
    simp only [Mat.sum] at *
    apply heq_of_eq
    ext i j
    exact Fin.elim0 i
  have hx : cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) = 0 := by
    have h := cls_sum hzero hzero
    rw [hself] at h
    have h3 : cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) + 0 =
        cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) +
          cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) := by
      rw [add_zero]; exact h
    exact (add_left_cancel h3).symm
  have hzero' : Mat.IsIdem (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R) := by
    show (0 : Matrix (Fin n) (Fin n) R) * 0 = 0
    simp
  have hmvN : Mat.MvN (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R)
      (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) :=
    ⟨0, 0, by simp, by simp⟩
  rw [cls_eq_of_mvN hzero' hzero hmvN, hx]

/-- Conjugate idempotents (by a unit) have equal `K₀`-class. -/
lemma cls_conj_bott {R : Type} [Ring R] {m : ℕ} (p : Matrix (Fin m) (Fin m) R) (hp : p * p = p)
    (u v : Matrix (Fin m) (Fin m) R) (hvu : v * u = 1) :
    cls (⟨m, u * p * v⟩ : Mat R) = cls (⟨m, p⟩ : Mat R) := by
  have hide : Mat.IsIdem (⟨m, u * p * v⟩ : Mat R) := by
    show (u * p * v) * (u * p * v) = u * p * v
    calc (u * p * v) * (u * p * v)
        = u * (p * (v * (u * (p * v)))) := by simp only [Matrix.mul_assoc]
      _ = u * (p * (p * v)) := by rw [← Matrix.mul_assoc v u (p * v), hvu, Matrix.one_mul]
      _ = u * (p * v) := by rw [← Matrix.mul_assoc p p v, hp]
      _ = u * p * v := by rw [Matrix.mul_assoc]
  have hba : (p * v) * u = p := by rw [Matrix.mul_assoc, hvu, Matrix.mul_one]
  have hab : u * (p * v) = u * p * v := (Matrix.mul_assoc u p v).symm
  exact (cls_eq_of_mvN (p := (⟨m, p⟩ : Mat R)) (q := (⟨m, u * p * v⟩ : Mat R)) hp hide
    ⟨u, p * v, hba, hab⟩).symm

/-! ## Gluing along the pullback square -/

/-- Matrices over `P` are determined by their two images. -/
lemma mat_ext_of_maps_bott {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {ι : Type} {A B : Matrix ι ι P}
    (h1 : A.map ρ₁ = B.map ρ₁) (h2 : A.map ρ₂ = B.map ρ₂) : A = B := by
  ext i j
  have h1' : ρ₁ (B i j) = ρ₁ (A i j) := by
    have h := congrFun (congrFun h1 i) j
    rw [Matrix.map_apply, Matrix.map_apply] at h
    exact h.symm
  have h2' : ρ₂ (B i j) = ρ₂ (A i j) := by
    have h := congrFun (congrFun h2 i) j
    rw [Matrix.map_apply, Matrix.map_apply] at h
    exact h.symm
  have hq : σ₁ (ρ₁ (A i j)) = σ₂ (ρ₂ (A i j)) := by
    have h := DFunLike.congr_fun hcomm (A i j)
    simpa [RingHom.comp_apply] using h
  exact (hpb (ρ₁ (A i j)) (ρ₂ (A i j)) hq).unique ⟨rfl, rfl⟩ ⟨h1', h2'⟩

/-- A pair of matrices with matching images in `Q` is the pair of images of a matrix over `P`. -/
lemma mat_lift_bott {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {ι : Type} (N₁ : Matrix ι ι P₁) (N₂ : Matrix ι ι P₂)
    (h : ∀ i j, σ₁ (N₁ i j) = σ₂ (N₂ i j)) :
    ∃ E : Matrix ι ι P, E.map ρ₁ = N₁ ∧ E.map ρ₂ = N₂ := by
  refine ⟨fun i j => (hpb (N₁ i j) (N₂ i j) (h i j)).choose, ?_, ?_⟩
  · ext i j; exact ((hpb (N₁ i j) (N₂ i j) (h i j)).choose_spec.1).1
  · ext i j; exact ((hpb (N₁ i j) (N₂ i j) (h i j)).choose_spec.1).2

/-- Matrices over `Q` lift entrywise along a surjective ring homomorphism. -/
lemma mat_lift_surj {A B : Type} [Ring A] [Ring B] (φ : A →+* B) (h : Function.Surjective φ)
    {m k : ℕ} (M : Matrix (Fin m) (Fin k) B) : ∃ M' : Matrix (Fin m) (Fin k) A, M'.map φ = M := by
  refine ⟨fun i j => (h (M i j)).choose, ?_⟩
  ext i j
  show φ ((h (M i j)).choose) = M i j
  exact (h (M i j)).choose_spec

/-- **Milnor patching of idempotents (rectangular form)**: in a cartesian square of rings (`hpb` = the pull-back property) with the leg `σ₂ : P₂ → Q` surjective (`hs`), idempotents `e₁` (size `n₁`) over `P₁` and `e₂` (size `n₂`) over `P₂` whose base changes to `Q` are Murray–von Neumann equivalent (rectangular witnesses `S : n₂ × n₁`, `T : n₁ × n₂`) glue to an idempotent over `P` whose classes in `K₀ P₁`, `K₀ P₂` are those of the two idempotents. (Cf. M. Land, *Algebraic K-theory*, §4.3, Thm 4.51 / Cor 4.53: the glued module `M = {(m₁,m₂) ∈ e₁P₁^{n₁} × e₂P₂^{n₂} : S(m₁⊗1) = m₂⊗1}` is finitely generated projective over `P`. Note `hpb` + `hs` also make `P → P₁` surjective.) -/
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
  have hp : (e₁.map σ₁) * (e₁.map σ₁) = e₁.map σ₁ := by rw [← Matrix.map_mul, he₁]
  have hq : (e₂.map σ₂) * (e₂.map σ₂) = e₂.map σ₂ := by rw [← Matrix.map_mul, he₂]
  obtain ⟨Sl, hSl⟩ := mat_lift_surj σ₂ hs S
  obtain ⟨Tl, hTl⟩ := mat_lift_surj σ₂ hs T
  have hmapG : (blkA Tl * blkC (-Sl) * blkA Tl).map σ₂ = blkA T * blkC (-S) * blkA T := by
    simp only [Matrix.map_mul, blkA_map, blkC_map, map_neg_mat, hSl, hTl]
  have hmapG' : (blkA (-Tl) * blkC Sl * blkA (-Tl)).map σ₂ = blkA (-T) * blkC S * blkA (-T) := by
    simp only [Matrix.map_mul, blkA_map, blkC_map, map_neg_mat, hSl, hTl]
  set D₁ : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) P₁ := Matrix.fromBlocks e₁ 0 0 0 with hD₁
  set D₂ : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) P₂ := Matrix.fromBlocks 0 0 0 e₂ with hD₂
  set G₂ : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) P₂ := blkA Tl * blkC (-Sl) * blkA Tl with hG₂
  set G₂' : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) P₂ := blkA (-Tl) * blkC Sl * blkA (-Tl) with hG₂'
  set N₂ : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) P₂ := G₂ * D₂ * G₂' with hN₂
  have hGQ_GQ' : (blkA T * blkC (-S) * blkA T) * (blkA (-T) * blkC S * blkA (-T)) = 1 :=
    (patch_block_unit (R := Q) S T).1
  have hG₂'G₂ : G₂' * G₂ = 1 := by rw [hG₂', hG₂]; exact (patch_block_unit (R := P₂) Sl Tl).2
  have hD₁idem : D₁ * D₁ = D₁ := by
    rw [hD₁, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, he₁]
  have hD₂idem : D₂ * D₂ = D₂ := by
    rw [hD₂, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, he₂]
  have hD₁map : D₁.map σ₁ = Matrix.fromBlocks (e₁.map σ₁) 0 0 0 := by
    rw [hD₁, Matrix.fromBlocks_map]
    simp only [Matrix.map_zero, map_zero]
  have hD₂map : D₂.map σ₂ = Matrix.fromBlocks 0 0 0 (e₂.map σ₂) := by
    rw [hD₂, Matrix.fromBlocks_map]
    simp only [Matrix.map_zero, map_zero]
  have hN₂idem : N₂ * N₂ = N₂ := by
    rw [hN₂]; exact conj_idem G₂ G₂' D₂ hG₂'G₂ hD₂idem
  have hN₂map : N₂.map σ₂ = D₁.map σ₁ := by
    rw [hN₂, Matrix.map_mul, Matrix.map_mul, hG₂, hG₂', hmapG, hmapG', hD₂map, hD₁map,
      patch_block_key (e₁.map σ₁) (e₂.map σ₂) S T hp hq hST hTS, Matrix.mul_assoc,
      hGQ_GQ', Matrix.mul_one]
  have hglue : ∀ i j, σ₁ (D₁ i j) = σ₂ (N₂ i j) := by
    intro i j
    have h := congrFun (congrFun hN₂map i) j
    rw [Matrix.map_apply, Matrix.map_apply] at h
    exact h.symm
  obtain ⟨Eblock, hEb₁, hEb₂⟩ := mat_lift_bott ρ₁ ρ₂ σ₁ σ₂ hpb D₁ N₂ hglue
  have hEbidem : Eblock * Eblock = Eblock := by
    apply mat_ext_of_maps_bott ρ₁ ρ₂ σ₁ σ₂ hcomm hpb
    · rw [Matrix.map_mul, hEb₁, hD₁idem]
    · rw [Matrix.map_mul, hEb₂, hN₂idem]
  have hD₂re : (Matrix.reindex finSumFinEquiv finSumFinEquiv D₂) *
        (Matrix.reindex finSumFinEquiv finSumFinEquiv D₂)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv D₂ := by
    rw [reindexMul finSumFinEquiv finSumFinEquiv finSumFinEquiv D₂ D₂, hD₂idem]
  have hVU : (Matrix.reindex finSumFinEquiv finSumFinEquiv G₂') *
        (Matrix.reindex finSumFinEquiv finSumFinEquiv G₂) = 1 := by
    rw [reindexMul finSumFinEquiv finSumFinEquiv finSumFinEquiv G₂' G₂, hG₂'G₂,
      reindex_one_bott finSumFinEquiv]
  have hU : (Matrix.reindex finSumFinEquiv finSumFinEquiv G₂) *
        (Matrix.reindex finSumFinEquiv finSumFinEquiv D₂) *
        (Matrix.reindex finSumFinEquiv finSumFinEquiv G₂')
      = Matrix.reindex finSumFinEquiv finSumFinEquiv N₂ := by
    rw [reindexMul finSumFinEquiv finSumFinEquiv finSumFinEquiv G₂ D₂,
      reindexMul finSumFinEquiv finSumFinEquiv finSumFinEquiv (G₂ * D₂) G₂', hN₂]
  refine ⟨⟨n₁ + n₂, Matrix.reindex finSumFinEquiv finSumFinEquiv Eblock⟩, ?_, ?_, ?_⟩
  · show (Matrix.reindex finSumFinEquiv finSumFinEquiv Eblock) *
        (Matrix.reindex finSumFinEquiv finSumFinEquiv Eblock)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv Eblock
    rw [reindexMul finSumFinEquiv finSumFinEquiv finSumFinEquiv Eblock Eblock, hEbidem]
  · have h1 : Mat.map ρ₁ (⟨n₁ + n₂, Matrix.reindex finSumFinEquiv finSumFinEquiv Eblock⟩ : Mat P)
        = Mat.sum (⟨n₁, e₁⟩ : Mat P₁) (⟨n₂, (0 : Matrix (Fin n₂) (Fin n₂) P₁)⟩ : Mat P₁) := by
      have heq : Mat.map ρ₁ (⟨n₁ + n₂, Matrix.reindex finSumFinEquiv finSumFinEquiv Eblock⟩ : Mat P)
          = (⟨n₁ + n₂, Matrix.reindex finSumFinEquiv finSumFinEquiv D₁⟩ : Mat P₁) := by
        show (⟨n₁ + n₂, (Matrix.reindex finSumFinEquiv finSumFinEquiv Eblock).map ρ₁⟩ : Mat P₁) = _
        rw [reindex_map_bott, hEb₁]
      rw [heq, hD₁]; rfl
    rw [h1, cls_sum (p := (⟨n₁, e₁⟩ : Mat P₁))
        (q := (⟨n₂, (0 : Matrix (Fin n₂) (Fin n₂) P₁)⟩ : Mat P₁)) he₁
        (by show (0 : Matrix (Fin n₂) (Fin n₂) P₁) * 0 = 0; simp),
      cls_zero_mat_bott (R := P₁) n₂, add_zero]
  · have h1 : Mat.map ρ₂ (⟨n₁ + n₂, Matrix.reindex finSumFinEquiv finSumFinEquiv Eblock⟩ : Mat P)
        = (⟨n₁ + n₂, Matrix.reindex finSumFinEquiv finSumFinEquiv N₂⟩ : Mat P₂) := by
      show (⟨n₁ + n₂, (Matrix.reindex finSumFinEquiv finSumFinEquiv Eblock).map ρ₂⟩ : Mat P₂) = _
      rw [reindex_map_bott, hEb₂]
    rw [h1, ← hU,
      cls_conj_bott (Matrix.reindex finSumFinEquiv finSumFinEquiv D₂) hD₂re
        (Matrix.reindex finSumFinEquiv finSumFinEquiv G₂)
        (Matrix.reindex finSumFinEquiv finSumFinEquiv G₂') hVU]
    rw [show (⟨n₁ + n₂, Matrix.reindex finSumFinEquiv finSumFinEquiv D₂⟩ : Mat P₂)
        = Mat.sum (⟨n₁, (0 : Matrix (Fin n₁) (Fin n₁) P₂)⟩ : Mat P₂) (⟨n₂, e₂⟩ : Mat P₂) from by
          rw [hD₂]; rfl]
    rw [cls_sum (p := (⟨n₁, (0 : Matrix (Fin n₁) (Fin n₁) P₂)⟩ : Mat P₂)) (q := (⟨n₂, e₂⟩ : Mat P₂))
        (by show (0 : Matrix (Fin n₁) (Fin n₁) P₂) * 0 = 0; simp) he₂,
      cls_zero_mat_bott (R := P₂) n₁, zero_add]

end

end Work.KT.Bott
