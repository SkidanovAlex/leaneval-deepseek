import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.sumMvN
import Submission.Work.KT.sum_mvN_congr
import Submission.Work.KT.sum_mvN_assoc
import Submission.Work.KT.rel_cancel
import Submission.Work.KT.monoid_grothendieck
import Submission.Work.KT.Cone.mv_inj
import Submission.Work.KT.cls_eq_stable_mvN
import Submission.Work.KT.k0_rep

/-!
# Injectivity of `K₀ P → K₀ P₁ ⊕ K₀ P₂` for a Milnor square

Main target (end of file): `Work.KT.k0_mv_inj`.  The proof is Milnor's Mayer–Vietoris argument for
`K₀` of a cartesian square of rings with one surjective leg, together with the stable
unit-lifting hypothesis `hlift`: an idempotent of `P` whose base changes are stably free is free.
-/

set_option maxHeartbeats 1000000

namespace Work.KT

noncomputable section

variable {R S : Type}

/-! ## 1. Bookkeeping for block sums, identity blocks and `cls` -/

section Bookkeeping

variable [Ring R] [Ring S]

/-- The complementary matrix `1 - p`. -/
def Mat.compl (p : Mat R) : Mat R := ⟨p.1, 1 - p.2⟩

/-- Entrywise image of a block sum. -/
lemma Mat.sum_map (φ : R →+* S) (p q : Mat R) :
    Mat.map φ (Mat.sum p q) = Mat.sum (Mat.map φ p) (Mat.map φ q) := by
  obtain ⟨n, X⟩ := p
  obtain ⟨m, Y⟩ := q
  unfold Mat.sum Mat.map
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  ext i j
  simp only [Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;> simp

/-- Entrywise image of an identity matrix. -/
lemma Mat.map_one (φ : R →+* S) (n : ℕ) : Mat.map φ (Mat.one R n) = Mat.one S n := by
  unfold Mat.one Mat.map
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- Entrywise image of the complementary idempotent `1 - p`. -/
lemma Mat.compl_map (φ : R →+* S) (p : Mat R) :
    Mat.map φ (Mat.compl p) = Mat.compl (Mat.map φ p) := by
  unfold Mat.compl Mat.map
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  rw [Matrix.map_sub (fun x => φ x) (fun a b => φ.map_sub a b),
    Matrix.map_one (fun x => φ x) (φ.map_zero) (φ.map_one)]

/-- `1_m ⊕ 1_k = 1_{m+k}`. -/
lemma Mat.one_sum_one (m k : ℕ) : Mat.sum (Mat.one R m) (Mat.one R k) = Mat.one R (m + k) := by
  unfold Mat.sum Mat.one
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  rw [Matrix.fromBlocks_one, Matrix.reindex_apply,
    Matrix.submatrix_one _ finSumFinEquiv.symm.injective]

/-- Entrywise image commutes with reindexing. -/
lemma Matrix.reindex_map {α β : Type} [NonAssocSemiring α] [NonAssocSemiring β] (φ : α →+* β)
    {m m' n n' : Type} (e : m ≃ m') (f : n ≃ n') (M : Matrix m n α) :
    (Matrix.reindex e f M).map φ = Matrix.reindex e f (M.map φ) := by
  ext i j
  simp [Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Entrywise image of a block matrix. -/
lemma Matrix.fromBlocks_map {α β : Type} [NonAssocSemiring α] [NonAssocSemiring β]
    (φ : α →+* β) {n l o m : Type} (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) :
    (Matrix.fromBlocks A B C D).map φ =
      Matrix.fromBlocks (A.map φ) (B.map φ) (C.map φ) (D.map φ) := by
  ext i j
  rcases i with a | a <;> rcases j with b | b <;> simp [Matrix.map_apply, Matrix.fromBlocks]

/-- `fromBlocksSum 1 1 = 1`. -/
lemma fromBlocksSum_one_one {n m : ℕ} :
    fromBlocksSum (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  rw [fromBlocksSum, Matrix.fromBlocks_one, Matrix.reindex_apply,
    Matrix.submatrix_one _ finSumFinEquiv.symm.injective]

/-- Multiplying block-diagonal rectangular matrices with a common identity block. -/
lemma fromBlocksSum_mul_one {n m l k : ℕ} (X : Matrix (Fin n) (Fin m) R)
    (Y : Matrix (Fin m) (Fin l) R) :
    fromBlocksSum X (1 : Matrix (Fin k) (Fin k) R) *
      fromBlocksSum Y (1 : Matrix (Fin k) (Fin k) R) =
      fromBlocksSum (X * Y) (1 : Matrix (Fin k) (Fin k) R) := by
  rw [fromBlocksSum, fromBlocksSum, fromBlocksSum, reindexMul, Matrix.fromBlocks_multiply]
  simp

/-- `cls (1_m) + cls (1_k) = cls (1_{m+k})`. -/
lemma cls_one_sum_one (m k : ℕ) :
    cls (Mat.one R m) + cls (Mat.one R k) = cls (Mat.one R (m + k)) := by
  rw [← cls_sum (Mat.one_isIdem R m) (Mat.one_isIdem R k), Mat.one_sum_one]

/-- The class of the complementary idempotent `1 - q`. -/
lemma cls_one_sub {q : Mat R} (hq : q.IsIdem) :
    cls (Mat.compl q) = cls (Mat.one R q.1) - cls q := by
  have h1 : (Mat.compl q).IsIdem := Mat.isIdem_one_sub hq
  have hmvn : Mat.MvN (Mat.one R q.1) (Mat.sum (Mat.compl q) q) :=
    Mat.mvN_trans (Mat.one_isIdem R q.1) (Mat.sum_idem hq h1) (Mat.sum_idem h1 hq)
      (Mat.mvN_symm (mvN_sum_compl R q hq)) (mvN_sum_comm q (Mat.compl q))
  have h2 : cls (Mat.one R q.1) = cls (Mat.sum (Mat.compl q) q) :=
    cls_eq_of_mvN (Mat.one_isIdem R q.1) (Mat.sum_idem h1 hq) hmvn
  rw [cls_sum h1 hq] at h2
  exact (eq_sub_iff_add_eq).mpr h2.symm

/-- The class of the complementary idempotent `1 - q` (explicit `⟨·, 1 - ·⟩` form). -/
lemma cls_one_sub' {q : Mat R} (hq : q.IsIdem) :
    cls (⟨q.1, 1 - q.2⟩ : Mat R) = cls (Mat.one R q.1) - cls q := cls_one_sub hq


end Bookkeeping

/-! ## 2. The cartesian glueing of matrices -/

section Glue

variable {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]

/-- `Matrix.map` of a zero matrix along a ring hom. -/
@[simp] lemma Matrix.map_zero' {α β : Type} [NonAssocSemiring α] [NonAssocSemiring β]
    {m n : Type} (φ : α →+* β) :
    ((0 : Matrix m n α).map ⇑φ) = (0 : Matrix m n β) := Matrix.map_zero _ φ.map_zero

/-- `Matrix.map` of an identity matrix along a ring hom. -/
@[simp] lemma Matrix.map_one' {α β : Type} [NonAssocSemiring α] [NonAssocSemiring β] {n : Type}
    [DecidableEq n] (φ : α →+* β) : ((1 : Matrix n n α).map ⇑φ) = (1 : Matrix n n β) :=
  Matrix.map_one _ φ.map_zero φ.map_one

/-- The compatibility of the two images of an entry of a pair of matrices. -/
theorem glueProof (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    {n m : ℕ} (X₁ : Matrix (Fin n) (Fin m) P₁) (X₂ : Matrix (Fin n) (Fin m) P₂)
    (h : X₁.map σ₁ = X₂.map σ₂) (i : Fin n) (j : Fin m) : σ₁ (X₁ i j) = σ₂ (X₂ i j) := by
  have := congrFun (congrFun h i) j
  simpa [Matrix.map_apply] using this

/-- Entrywise `hpb`-glueing of matrices: the matrix over `P` with prescribed images. -/
def glueMat (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {n m : ℕ} (X₁ : Matrix (Fin n) (Fin m) P₁) (X₂ : Matrix (Fin n) (Fin m) P₂)
    (h : X₁.map σ₁ = X₂.map σ₂) : Matrix (Fin n) (Fin m) P :=
  fun i j => (hpb (X₁ i j) (X₂ i j) (glueProof ρ₁ ρ₂ σ₁ σ₂ X₁ X₂ h i j)).choose

theorem glueMat_apply_ρ₁ (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {n m : ℕ} (X₁ : Matrix (Fin n) (Fin m) P₁) (X₂ : Matrix (Fin n) (Fin m) P₂)
    (h : X₁.map σ₁ = X₂.map σ₂) (i : Fin n) (j : Fin m) :
    ρ₁ (glueMat ρ₁ ρ₂ σ₁ σ₂ hpb X₁ X₂ h i j) = X₁ i j := by
  unfold glueMat
  exact ((hpb (X₁ i j) (X₂ i j) (glueProof ρ₁ ρ₂ σ₁ σ₂ X₁ X₂ h i j)).choose_spec.1).1

theorem glueMat_apply_ρ₂ (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {n m : ℕ} (X₁ : Matrix (Fin n) (Fin m) P₁) (X₂ : Matrix (Fin n) (Fin m) P₂)
    (h : X₁.map σ₁ = X₂.map σ₂) (i : Fin n) (j : Fin m) :
    ρ₂ (glueMat ρ₁ ρ₂ σ₁ σ₂ hpb X₁ X₂ h i j) = X₂ i j := by
  unfold glueMat
  exact ((hpb (X₁ i j) (X₂ i j) (glueProof ρ₁ ρ₂ σ₁ σ₂ X₁ X₂ h i j)).choose_spec.1).2

theorem glueMat_map_ρ₁ (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {n m : ℕ} (X₁ : Matrix (Fin n) (Fin m) P₁) (X₂ : Matrix (Fin n) (Fin m) P₂)
    (h : X₁.map σ₁ = X₂.map σ₂) :
    (glueMat ρ₁ ρ₂ σ₁ σ₂ hpb X₁ X₂ h).map ρ₁ = X₁ := by
  ext i j
  simpa [Matrix.map_apply] using glueMat_apply_ρ₁ ρ₁ ρ₂ σ₁ σ₂ hpb X₁ X₂ h i j

theorem glueMat_map_ρ₂ (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {n m : ℕ} (X₁ : Matrix (Fin n) (Fin m) P₁) (X₂ : Matrix (Fin n) (Fin m) P₂)
    (h : X₁.map σ₁ = X₂.map σ₂) :
    (glueMat ρ₁ ρ₂ σ₁ σ₂ hpb X₁ X₂ h).map ρ₂ = X₂ := by
  ext i j
  simpa [Matrix.map_apply] using glueMat_apply_ρ₂ ρ₁ ρ₂ σ₁ σ₂ hpb X₁ X₂ h i j

/-- Cartesianity: a matrix over `P` is determined by its two images. -/
theorem mat_eq_of_map_eq (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂) {n m : ℕ}
    {X Y : Matrix (Fin n) (Fin m) P} (h₁ : X.map ρ₁ = Y.map ρ₁)
    (h₂ : X.map ρ₂ = Y.map ρ₂) : X = Y := by
  ext i j
  have hq : σ₁ (ρ₁ (X i j)) = σ₂ (ρ₂ (X i j)) := by
    simpa using congrArg (fun f : P →+* Q => f (X i j)) hcomm
  obtain ⟨w, hw, huniq⟩ := hpb (ρ₁ (X i j)) (ρ₂ (X i j)) hq
  have hA : ρ₁ (X i j) = ρ₁ (X i j) ∧ ρ₂ (X i j) = ρ₂ (X i j) := ⟨rfl, rfl⟩
  have hB : ρ₁ (Y i j) = ρ₁ (X i j) ∧ ρ₂ (Y i j) = ρ₂ (X i j) := by
    constructor
    · have h := congrFun (congrFun h₁ i) j
      simp only [Matrix.map_apply] at h
      exact h.symm
    · have h := congrFun (congrFun h₂ i) j
      simp only [Matrix.map_apply] at h
      exact h.symm
  exact (huniq (X i j) hA).trans (huniq (Y i j) hB).symm

/-- The `.2`-form of the base-change compatibility of a stabilised idempotent. -/
theorem sum_snd_map_compat (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂) (E : Mat P) (a : ℕ) :
    (((Mat.sum (Mat.map ρ₂ E) (Mat.one P₂ a)).2 :
        Matrix (Fin (E.1 + a)) (Fin (E.1 + a)) P₂)).map σ₂ =
      (((Mat.sum (Mat.map ρ₁ E) (Mat.one P₁ a)).2 :
        Matrix (Fin (E.1 + a)) (Fin (E.1 + a)) P₁)).map σ₁ := by
  have hfun : (⇑σ₁ ∘ ⇑ρ₁) = (⇑σ₂ ∘ ⇑ρ₂) := by
    ext x
    exact congrArg (fun f : P →+* Q => f x) hcomm
  have hL : (((Mat.sum (Mat.map ρ₂ E) (Mat.one P₂ a)).2 :
        Matrix (Fin (E.1 + a)) (Fin (E.1 + a)) P₂)).map σ₂ =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (E.2.map (⇑σ₂ ∘ ⇑ρ₂)) 0 0 1) := by
    show (fromBlocksSum (E.2.map ⇑ρ₂) (1 : Matrix (Fin a) (Fin a) P₂)).map ⇑σ₂ = _
    simp only [fromBlocksSum, Matrix.reindex_map, Matrix.fromBlocks_map,
      Matrix.map_map (f := ⇑ρ₂) (g := ⇑σ₂) (M := E.2)]
    rw [Matrix.map_zero' σ₂, Matrix.map_zero' σ₂, Matrix.map_one' σ₂]
    rfl
  have hR : (((Mat.sum (Mat.map ρ₁ E) (Mat.one P₁ a)).2 :
        Matrix (Fin (E.1 + a)) (Fin (E.1 + a)) P₁)).map σ₁ =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (E.2.map (⇑σ₁ ∘ ⇑ρ₁)) 0 0 1) := by
    show (fromBlocksSum (E.2.map ⇑ρ₁) (1 : Matrix (Fin a) (Fin a) P₁)).map ⇑σ₁ = _
    simp only [fromBlocksSum, Matrix.reindex_map, Matrix.fromBlocks_map,
      Matrix.map_map (f := ⇑ρ₁) (g := ⇑σ₁) (M := E.2)]
    rw [Matrix.map_zero' σ₁, Matrix.map_zero' σ₁, Matrix.map_one' σ₁]
    rfl
  rw [hL, hR]
  exact congrArg (fun f => Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (E.2.map f) (0 : Matrix (Fin E.1) (Fin a) Q)
      (0 : Matrix (Fin a) (Fin E.1) Q) (1 : Matrix (Fin a) (Fin a) Q))) hfun.symm

/-- The base change of the stabilised idempotent `E ⊕ 1_a`. -/
theorem sum_snd_map_eq (ρ : P →+* P₁) (E : Mat P) (a : ℕ) :
    ((Mat.sum (Mat.map ρ E) (Mat.one P₁ a)).2 : Matrix (Fin (E.1 + a)) (Fin (E.1 + a)) P₁) =
      ((Mat.sum E (Mat.one P a)).2 : Matrix (Fin (E.1 + a)) (Fin (E.1 + a)) P).map ρ := by
  show (fromBlocksSum (E.2.map ⇑ρ) (1 : Matrix (Fin a) (Fin a) P₁)) =
    (fromBlocksSum E.2 (1 : Matrix (Fin a) (Fin a) P)).map ⇑ρ
  simp only [fromBlocksSum, Matrix.reindex_map, Matrix.fromBlocks_map]
  rw [Matrix.map_zero' ρ, Matrix.map_zero' ρ, Matrix.map_one' ρ]

/-- The base-change compatibility of a block-diagonal stabilisation with identity blocks. -/
theorem sum_one_map_compat (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q) {L : ℕ}
    (M₁ : Matrix (Fin L) (Fin L) P₁) (M₂ : Matrix (Fin L) (Fin L) P₂)
    (hM : M₁.map σ₁ = M₂.map σ₂) (k : ℕ) :
    (Mat.sum ⟨L, M₁⟩ (Mat.one P₁ k)).2.map σ₁ =
      (Mat.sum ⟨L, M₂⟩ (Mat.one P₂ k)).2.map σ₂ := by
  show (fromBlocksSum M₁ (1 : Matrix (Fin k) (Fin k) P₁)).map ⇑σ₁ =
    (fromBlocksSum M₂ (1 : Matrix (Fin k) (Fin k) P₂)).map ⇑σ₂
  simp only [fromBlocksSum, Matrix.reindex_map, Matrix.fromBlocks_map]
  rw [Matrix.map_zero' σ₁, Matrix.map_zero' σ₁, Matrix.map_zero' σ₂, Matrix.map_zero' σ₂,
    Matrix.map_one' σ₁, Matrix.map_one' σ₂, hM]

/-- `fromBlocksSum X 1 = X ⊕ 1_k` at the level of second components. -/
theorem fromBlocksSum_eq_sum_snd {R : Type} [Ring R] (X : Mat R) {k : ℕ} :
    fromBlocksSum X.2 (1 : Matrix (Fin k) (Fin k) R) = (Mat.sum X (Mat.one R k)).2 := rfl

/-- The two "differences" of a pair of MvN data sets over the two legs are mutually inverse
units, provided the two `MvN` targets agree through the commuting square. -/
theorem unit_of_glueing (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q) {N L : ℕ}
    (A₁ : Matrix (Fin N) (Fin L) P₁) (B₁ : Matrix (Fin L) (Fin N) P₁)
    (A₂ : Matrix (Fin N) (Fin L) P₂) (B₂ : Matrix (Fin L) (Fin N) P₂)
    (M₁ : Matrix (Fin L) (Fin L) P₁) (M₂ : Matrix (Fin L) (Fin L) P₂)
    (h₁ : B₁ * A₁ = M₁) (h₂ : A₁ * B₁ = 1) (h₃ : B₂ * A₂ = M₂) (h₄ : A₂ * B₂ = 1)
    (hM : M₁.map σ₁ = M₂.map σ₂) :
    ((A₁.map σ₁) * (B₂.map σ₂)) * ((A₂.map σ₂) * (B₁.map σ₁)) = 1 ∧
      ((A₂.map σ₂) * (B₁.map σ₁)) * ((A₁.map σ₁) * (B₂.map σ₂)) = 1 := by
  constructor
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B₂.map σ₂) (A₂.map σ₂) (B₁.map σ₁),
      ← Matrix.map_mul (f := σ₂), h₃, ← hM, ← h₁, Matrix.map_mul (f := σ₁),
      Matrix.mul_assoc (B₁.map σ₁) (A₁.map σ₁) (B₁.map σ₁),
      ← Matrix.map_mul (f := σ₁), h₂,
      Matrix.map_one (f := ⇑σ₁) (by simp) (by simp), Matrix.mul_one,
      ← Matrix.map_mul (f := σ₁), h₂,
      Matrix.map_one (f := ⇑σ₁) (by simp) (by simp)]
  · rw [Matrix.mul_assoc (A₂.map σ₂) (B₁.map σ₁) ((A₁.map σ₁) * (B₂.map σ₂)),
      ← Matrix.mul_assoc (B₁.map σ₁) (A₁.map σ₁) (B₂.map σ₂),
      ← Matrix.map_mul (f := σ₁), h₁, hM, ← h₃, Matrix.map_mul (f := σ₂),
      Matrix.mul_assoc (B₂.map σ₂) (A₂.map σ₂) (B₂.map σ₂),
      ← Matrix.map_mul (f := σ₂), h₄,
      Matrix.map_one (f := ⇑σ₂) (by simp) (by simp), Matrix.mul_one,
      ← Matrix.map_mul (f := σ₂), h₄,
      Matrix.map_one (f := ⇑σ₂) (by simp) (by simp)]

end Glue

/-! ## 3. Elementary inputs: representatives of `K₀`-classes, stable MvN from equal classes,
and the criterion for a stably free idempotent over `P` -/

section Inputs

/-- **Equal classes give a stable Murray–von Neumann equivalence** (the "detection" half of
`Work.KT.cls_eq_stable_mvN`). -/
theorem mvN_of_cls_eq_aux {R : Type} [Ring R] {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem)
    (h : cls p = cls q) : ∃ k : ℕ, Mat.MvN (p.sum (Mat.one R k)) (q.sum (Mat.one R k)) :=
  (cls_eq_stable_mvN p q hp hq).1 h

/-- Enlarging the stabilising free block of a stable Murray–von Neumann equivalence. -/
theorem mvN_sum_one_add_aux {R : Type} [Ring R] {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem)
    (a t : ℕ) (h : Mat.MvN (p.sum (Mat.one R a)) (q.sum (Mat.one R a))) :
    Mat.MvN (p.sum (Mat.one R (a + t))) (q.sum (Mat.one R (a + t))) :=
  k2_mvN_add_one_right hp hq h t

/-- The criterion for a `P`-module with stably free base changes to be free.  Given MvN data over `P₁` and `P₂` between `e.map ρᵢ` and `1_N` and a unit
`D` over `P₂` whose reduction is the stabilised difference of the two data sets, the stabilised
idempotent `e ⊕ 1_k` is MvN to the free module `1_{N+k}`. -/
theorem mvN_of_unit_compat {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hs : Function.Surjective σ₂) (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {N : ℕ} {e : Mat P}
    (A₁ : Matrix (Fin N) (Fin e.1) P₁) (B₁ : Matrix (Fin e.1) (Fin N) P₁)
    (A₂ : Matrix (Fin N) (Fin e.1) P₂) (B₂ : Matrix (Fin e.1) (Fin N) P₂)
    (h₁ : B₁ * A₁ = e.2.map ρ₁) (h₂ : A₁ * B₁ = 1)
    (h₃ : B₂ * A₂ = e.2.map ρ₂) (h₄ : A₂ * B₂ = 1)
    (k : ℕ) (D : Matrix (Fin (N + k)) (Fin (N + k)) P₂) (hD : IsUnit D)
    (hDmap : D.map σ₂ = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks ((A₁.map σ₁) * (B₂.map σ₂)) (0 : Matrix (Fin N) (Fin k) Q)
          (0 : Matrix (Fin k) (Fin N) Q) (1 : Matrix (Fin k) (Fin k) Q))) :
    Mat.MvN (Mat.sum e (Mat.one P k)) (Mat.one P (N + k)) := by
  -- Stabilise the two trivialisations by the identity block of size `k`.
  let A₁' : Matrix (Fin (N + k)) (Fin (e.1 + k)) P₁ :=
    fromBlocksSum A₁ (1 : Matrix (Fin k) (Fin k) P₁)
  let B₁' : Matrix (Fin (e.1 + k)) (Fin (N + k)) P₁ :=
    fromBlocksSum B₁ (1 : Matrix (Fin k) (Fin k) P₁)
  let A₂' : Matrix (Fin (N + k)) (Fin (e.1 + k)) P₂ :=
    fromBlocksSum A₂ (1 : Matrix (Fin k) (Fin k) P₂)
  let B₂' : Matrix (Fin (e.1 + k)) (Fin (N + k)) P₂ :=
    fromBlocksSum B₂ (1 : Matrix (Fin k) (Fin k) P₂)
  let e' : Matrix (Fin (e.1 + k)) (Fin (e.1 + k)) P :=
    fromBlocksSum e.2 (1 : Matrix (Fin k) (Fin k) P)
  have h₁' : B₁' * A₁' = e'.map ρ₁ := by
    show fromBlocksSum B₁ (1 : Matrix (Fin k) (Fin k) P₁) *
        fromBlocksSum A₁ (1 : Matrix (Fin k) (Fin k) P₁) =
      (fromBlocksSum e.2 (1 : Matrix (Fin k) (Fin k) P)).map ρ₁
    rw [fromBlocksSum_mul, h₁, one_mul, Cone.mvinj_map_fromBlocksSum, Matrix.map_one' ρ₁]
  have h₂' : A₁' * B₁' = 1 := by
    show fromBlocksSum A₁ (1 : Matrix (Fin k) (Fin k) P₁) *
        fromBlocksSum B₁ (1 : Matrix (Fin k) (Fin k) P₁) = 1
    rw [fromBlocksSum_mul, h₂, one_mul, fromBlocksSum_one_one]
  have h₃' : B₂' * A₂' = e'.map ρ₂ := by
    show fromBlocksSum B₂ (1 : Matrix (Fin k) (Fin k) P₂) *
        fromBlocksSum A₂ (1 : Matrix (Fin k) (Fin k) P₂) =
      (fromBlocksSum e.2 (1 : Matrix (Fin k) (Fin k) P)).map ρ₂
    rw [fromBlocksSum_mul, h₃, one_mul, Cone.mvinj_map_fromBlocksSum, Matrix.map_one' ρ₂]
  have h₄' : A₂' * B₂' = 1 := by
    show fromBlocksSum A₂ (1 : Matrix (Fin k) (Fin k) P₂) *
        fromBlocksSum B₂ (1 : Matrix (Fin k) (Fin k) P₂) = 1
    rw [fromBlocksSum_mul, h₄, one_mul, fromBlocksSum_one_one]
  have hDmap' : D.map σ₂ = A₁'.map σ₁ * B₂'.map σ₂ := by
    rw [hDmap]
    rw [Cone.mvinj_map_fromBlocksSum, Cone.mvinj_map_fromBlocksSum,
      Matrix.map_one' σ₁, Matrix.map_one' σ₂, fromBlocksSum_mul, one_mul]
    rw [fromBlocksSum]
  exact Cone.mvinj_mvN_glue ρ₁ ρ₂ σ₁ σ₂ hcomm hpb e' A₁' B₁' A₂' B₂'
    h₁' h₂' h₃' h₄' D hD hDmap'

/-- Every element of `K₀ R` is a difference of the classes of two idempotent matrices. -/
theorem exists_idem_rep_aux {R : Type} [Ring R] (w : K0 R) :
    ∃ p q : Mat R, p.IsIdem ∧ q.IsIdem ∧ w = cls p - cls q := by
  obtain ⟨F, n, hF, hw⟩ := k0_rep w
  exact ⟨F, Mat.one R n, hF, Mat.one_isIdem R n, hw⟩

end Inputs

/-! ## 4. Stable freeness of an idempotent over the Milnor square -/

section StableFree

variable {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]

/-- **An idempotent of `P` whose base changes are stably free of rank `N` is free of rank `N`**,
given the stable unit-lifting hypothesis on the surjective leg `σ₂ : P₂ → Q`. -/
theorem stable_free
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hs : Function.Surjective σ₂) (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    (hlift : ∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) Q), IsUnit u →
        ∃ (k : ℕ) (v : Matrix (Fin (n + k)) (Fin (n + k)) P₂), IsUnit v ∧
          v.map σ₂ = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u 0 0 1))
    {E : Mat P} (hE : E.IsIdem) (N : ℕ)
    (h₁ : cls (Mat.map ρ₁ E) = cls (Mat.one P₁ N))
    (h₂ : cls (Mat.map ρ₂ E) = cls (Mat.one P₂ N)) :
    cls E = cls (Mat.one P N) := by
  classical
  -- Step 1: stable Murray–von Neumann data on each leg
  obtain ⟨a₁, ha₁⟩ := mvN_of_cls_eq_aux (Mat.map_idem ρ₁ hE) (Mat.one_isIdem P₁ N) h₁
  obtain ⟨a₂, ha₂⟩ := mvN_of_cls_eq_aux (Mat.map_idem ρ₂ hE) (Mat.one_isIdem P₂ N) h₂
  -- Step 2: a common stabilisation `max a₁ a₂`
  have h₁' : Mat.MvN (Mat.sum (Mat.map ρ₁ E) (Mat.one P₁ (max a₁ a₂)))
      (Mat.one P₁ (N + max a₁ a₂)) := by
    have h := mvN_sum_one_add_aux (Mat.map_idem ρ₁ hE) (Mat.one_isIdem P₁ N)
      a₁ (max a₁ a₂ - a₁) ha₁
    rw [Nat.add_sub_of_le (le_max_left a₁ a₂)] at h
    rwa [Mat.one_sum_one] at h
  have h₂' : Mat.MvN (Mat.sum (Mat.map ρ₂ E) (Mat.one P₂ (max a₁ a₂)))
      (Mat.one P₂ (N + max a₁ a₂)) := by
    have h := mvN_sum_one_add_aux (Mat.map_idem ρ₂ hE) (Mat.one_isIdem P₂ N)
      a₂ (max a₁ a₂ - a₂) ha₂
    rw [Nat.add_sub_of_le (le_max_right a₁ a₂)] at h
    rwa [Mat.one_sum_one] at h
  -- Step 3: uniform sizes, stabilised idempotents and the witnesses
  let L : ℕ := E.1 + max a₁ a₂
  let M : ℕ := N + max a₁ a₂
  let E₁ : Mat P₁ := ⟨L, (Mat.sum (Mat.map ρ₁ E) (Mat.one P₁ (max a₁ a₂))).2⟩
  let E₂ : Mat P₂ := ⟨L, (Mat.sum (Mat.map ρ₂ E) (Mat.one P₂ (max a₁ a₂))).2⟩
  let E' : Mat P := Mat.sum E (Mat.one P (max a₁ a₂))
  have hMv₁ : Mat.MvN E₁ (⟨M, 1⟩ : Mat P₁) := h₁'
  have hMv₂ : Mat.MvN E₂ (⟨M, 1⟩ : Mat P₂) := h₂'
  obtain ⟨A₁, B₁, hB₁A₁, hA₁B₁⟩ := hMv₁
  obtain ⟨A₂, B₂, hB₂A₂, hA₂B₂⟩ := hMv₂
  let A₁c : Matrix (Fin M) (Fin L) P₁ := A₁
  let B₁c : Matrix (Fin L) (Fin M) P₁ := B₁
  let A₂c : Matrix (Fin M) (Fin L) P₂ := A₂
  let B₂c : Matrix (Fin L) (Fin M) P₂ := B₂
  have hA₁B₁c : A₁c * B₁c = 1 := hA₁B₁
  have hA₂B₂c : A₂c * B₂c = 1 := hA₂B₂
  have hB₁A₁c : B₁c * A₁c = (E₁.2 : Matrix (Fin L) (Fin L) P₁) := hB₁A₁
  have hB₂A₂c : B₂c * A₂c = (E₂.2 : Matrix (Fin L) (Fin L) P₂) := hB₂A₂
  -- the two base changes agree
  have hE₁eq : (E₁.2 : Matrix (Fin L) (Fin L) P₁) =
      (E'.2 : Matrix (Fin L) (Fin L) P).map ρ₁ :=
    sum_snd_map_eq ρ₁ E (max a₁ a₂)
  have hE₂eq : (E₂.2 : Matrix (Fin L) (Fin L) P₂) =
      (E'.2 : Matrix (Fin L) (Fin L) P).map ρ₂ :=
    sum_snd_map_eq ρ₂ E (max a₁ a₂)
  have hE₁eq' : E₁ = Mat.map ρ₁ E' := by
    have h := hE₁eq
    exact congrArg (fun Mm : Matrix (Fin L) (Fin L) P₁ => (⟨L, Mm⟩ : Mat P₁)) h
  have hE₂eq' : E₂ = Mat.map ρ₂ E' := by
    have h := hE₂eq
    exact congrArg (fun Mm : Matrix (Fin L) (Fin L) P₂ => (⟨L, Mm⟩ : Mat P₂)) h
  have hE₁E₂ : (E₁.2 : Matrix (Fin L) (Fin L) P₁).map σ₁ =
      (E₂.2 : Matrix (Fin L) (Fin L) P₂).map σ₂ := by
    rw [hE₁eq, hE₂eq, ← sum_snd_map_eq ρ₁ E (max a₁ a₂),
      ← sum_snd_map_eq ρ₂ E (max a₁ a₂)]
    exact (sum_snd_map_compat ρ₁ ρ₂ σ₁ σ₂ hcomm E (max a₁ a₂)).symm
  -- Step 4: the glueing unit and its lift over `P₂`
  obtain ⟨hWV, hVW⟩ := unit_of_glueing σ₁ σ₂ A₁c B₁c A₂c B₂c E₁.2 E₂.2
    hB₁A₁c hA₁B₁c hB₂A₂c hA₂B₂c hE₁E₂
  obtain ⟨k, D, hDunit, hD⟩ := hlift M ((A₁c.map σ₁) * (B₂c.map σ₂))
    (isUnit_iff_exists.mpr ⟨_, hWV, hVW⟩)
  -- Step 5: apply the criterion
  have hB₁A₁' : B₁c * A₁c = (E'.2 : Matrix (Fin L) (Fin L) P).map ρ₁ := hB₁A₁c.trans hE₁eq
  have hB₂A₂' : B₂c * A₂c = (E'.2 : Matrix (Fin L) (Fin L) P).map ρ₂ := hB₂A₂c.trans hE₂eq
  have hcrit : Mat.MvN (Mat.sum E' (Mat.one P k)) (Mat.one P (M + k)) :=
    mvN_of_unit_compat ρ₁ ρ₂ σ₁ σ₂ hs hcomm hpb A₁c B₁c A₂c B₂c
      hB₁A₁' hA₁B₁c hB₂A₂' hA₂B₂c k D hDunit hD
  -- Step 6: conclude by cancelling the free blocks
  have hcls : cls (Mat.sum E' (Mat.one P k)) = cls (Mat.one P (M + k)) :=
    cls_eq_of_mvN (Mat.sum_idem (Mat.sum_idem hE (Mat.one_isIdem P (max a₁ a₂)))
      (Mat.one_isIdem P k)) (Mat.one_isIdem P _) hcrit
  have hsplit : cls (Mat.sum E' (Mat.one P k)) =
      cls E + cls (Mat.one P (max a₁ a₂)) + cls (Mat.one P k) := by
    show cls (Mat.sum (Mat.sum E (Mat.one P (max a₁ a₂))) (Mat.one P k)) = _
    rw [cls_sum (Mat.sum_idem hE (Mat.one_isIdem P (max a₁ a₂))) (Mat.one_isIdem P k),
      cls_sum hE (Mat.one_isIdem P (max a₁ a₂))]
  rw [hsplit] at hcls
  have hrhs : cls (Mat.one P (M + k)) =
      cls (Mat.one P N) + cls (Mat.one P (max a₁ a₂)) + cls (Mat.one P k) := by
    rw [show M + k = N + (max a₁ a₂ + k) from by omega, cls_one_sum_one, cls_one_sum_one]
    abel
  rw [hrhs] at hcls
  exact add_right_cancel (add_right_cancel hcls)

end StableFree

/-! ## 5. The main theorem -/

/-- **Injectivity half of the Mayer–Vietoris sequence for `K₀`** (Milnor): in a cartesian square of rings with `σ₂ : P₂ → Q` surjective, if every invertible matrix over `Q` stably lifts to an invertible matrix over `P₂`, then `K₀ P → K₀ P₁ ⊕ K₀ P₂` is injective.  Reference: M. Land, *Algebraic K-theory*, §4.3, Lemma 4.56 and Theorem 4.57 (the connecting map `∂ : K₁(Q) → K₀(P)` has image the kernel, and the stable lifting hypothesis makes `GL(P₂) → GL(Q)` surjective, whence `∂ = 0`). -/
theorem k0_mv_inj {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hs : Function.Surjective σ₂) (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    (hlift : ∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) Q), IsUnit u →
        ∃ (k : ℕ) (v : Matrix (Fin (n + k)) (Fin (n + k)) P₂), IsUnit v ∧
          v.map σ₂ = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u 0 0 1)) :
    ∀ w : K0 P, K0.map ρ₁ w = 0 → K0.map ρ₂ w = 0 → w = 0 := by
  intro w hw₁ hw₂
  obtain ⟨p, q, hp, hq, rfl⟩ := exists_idem_rep_aux w
  -- the two legs agree on the classes of `p` and `q`
  have leg₁ : cls (Mat.map ρ₁ p) = cls (Mat.map ρ₁ q) := by
    have h : K0.map ρ₁ (cls p) - K0.map ρ₁ (cls q) = 0 := by
      rw [← map_sub]; exact hw₁
    rw [K0.map_cls ρ₁ hp, K0.map_cls ρ₁ hq] at h
    exact sub_eq_zero.mp h
  have leg₂ : cls (Mat.map ρ₂ p) = cls (Mat.map ρ₂ q) := by
    have h : K0.map ρ₂ (cls p) - K0.map ρ₂ (cls q) = 0 := by
      rw [← map_sub]; exact hw₂
    rw [K0.map_cls ρ₂ hp, K0.map_cls ρ₂ hq] at h
    exact sub_eq_zero.mp h
  -- the idempotent `p ⊕ (1 - q)`
  have hq' : (Mat.compl q).IsIdem := Mat.isIdem_one_sub hq
  have hc₁ : cls (Mat.map ρ₁ (Mat.sum p (Mat.compl q))) = cls (Mat.one P₁ q.1) := by
    rw [Mat.sum_map, Mat.compl_map, Mat.compl,
      cls_sum (Mat.map_idem ρ₁ hp) (Mat.isIdem_one_sub (Mat.map_idem ρ₁ hq)),
      cls_one_sub' (Mat.map_idem ρ₁ hq), leg₁]
    abel
  have hc₂ : cls (Mat.map ρ₂ (Mat.sum p (Mat.compl q))) = cls (Mat.one P₂ q.1) := by
    rw [Mat.sum_map, Mat.compl_map, Mat.compl,
      cls_sum (Mat.map_idem ρ₂ hp) (Mat.isIdem_one_sub (Mat.map_idem ρ₂ hq)),
      cls_one_sub' (Mat.map_idem ρ₂ hq), leg₂]
    abel
  have hfree : cls (Mat.sum p (Mat.compl q)) = cls (Mat.one P q.1) :=
    stable_free ρ₁ ρ₂ σ₁ σ₂ hs hcomm hpb hlift (Mat.sum_idem hp hq') q.1 hc₁ hc₂
  -- conclude
  rw [cls_sum hp hq', cls_one_sub hq] at hfree
  have h' : (cls p - cls q) + cls (Mat.one P q.1) = cls (Mat.one P q.1) := by
    nth_rewrite 2 [← hfree]
    abel
  exact sub_eq_zero.mp (add_right_cancel h')


end

end Work.KT
