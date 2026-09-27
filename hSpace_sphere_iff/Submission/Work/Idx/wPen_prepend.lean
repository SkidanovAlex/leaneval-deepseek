import Mathlib
import Submission.Work.KT.Idx.WPen
import Submission.Work.KT.Idx.PenDefs
import Submission.Work.KT.Basic
import Submission.Work.Idx.WPenBlk
import Submission.Work.Idx.WPenRes
import Submission.Work.Idx.WPenPsi
import Submission.Work.Idx.WPenAppendDefs
import Submission.Work.Idx.penProj_idem
import Submission.Work.Idx.matPenProj_eval
import Submission.Work.Idx.WPenEndgame
import Submission.Work.Idx.wPsi_preSeq
import Submission.Work.Idx.wRow_mul_wIncT
import Submission.Work.Idx.penProjMat_reindex
import Submission.Work.Idx.wQ_isUnit_of_pencil
import Submission.Work.Idx.blkPenProj_preSeq_blocks
import Submission.Work.Idx.MvNGen_add_fromBlocks
import Submission.Work.Idx.wProj_preSeq_blocks
import Submission.Work.Idx.wRow_mul_wProj_zero
import Submission.Work.Idx.wProj_mul_wQbig
import Submission.Work.Idx.blkPenProj_mul_of_mul
import Submission.Work.Idx.wRow_mul_blkPenProj

/-!
# `Work.Idx.wPen_prepend` — prepending a zero coefficient

Assembly file for the prepend step of the Bott index (Hatcher's formula (2)): the class of the
Riesz projection of the companion pencil of `Work.KT.Idx.preSeq X b = (0, b₀, …, b_d)` is the class
of the projection of `b` plus the trivial class `cls ⟨n, 1⟩`.
-/

namespace Work.Idx

open Matrix
open scoped BigOperators

noncomputable section

/-! ## Generic helper lemmas about `Matrix.reindex` -/

section Generic

variable {R : Type*} [CommRing R]

lemma reindex_reindex_aux {l m l' m' l'' m'' : Type*} (e₁ : l ≃ l') (e₂ : m ≃ m')
    (f₁ : l' ≃ l'') (f₂ : m' ≃ m'') (M : Matrix l m R) :
    Matrix.reindex f₁ f₂ (Matrix.reindex e₁ e₂ M) = Matrix.reindex (e₁.trans f₁) (e₂.trans f₂) M := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

lemma reindex_fromBlocks_aux {n o l m n' o' l' m' : Type*}
    (e₁ : n ≃ n') (e₂ : o ≃ o') (f₁ : l ≃ l') (f₂ : m ≃ m')
    (A : Matrix n l R) (B : Matrix n m R) (C : Matrix o l R) (D : Matrix o m R) :
    Matrix.reindex (Equiv.sumCongr e₁ e₂) (Equiv.sumCongr f₁ f₂) (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (Matrix.reindex e₁ f₁ A) (Matrix.reindex e₁ f₂ B)
        (Matrix.reindex e₂ f₁ C) (Matrix.reindex e₂ f₂ D) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]

lemma reindex_add_aux {l m l' m' : Type*} (e₁ : l ≃ l') (e₂ : m ≃ m')
    (M N : Matrix l m R) :
    Matrix.reindex e₁ e₂ (M + N) = Matrix.reindex e₁ e₂ M + Matrix.reindex e₁ e₂ N := by
  ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply]

lemma reindex_smul_aux [Algebra ℂ R] {l m l' m' : Type*} (e₁ : l ≃ l') (e₂ : m ≃ m')
    (c : ℂ) (M : Matrix l m R) :
    Matrix.reindex e₁ e₂ (c • M) = c • Matrix.reindex e₁ e₂ M := by
  ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply]

lemma reindex_zero_aux {l m l' m' : Type*} (e₁ : l ≃ l') (e₂ : m ≃ m') :
    Matrix.reindex e₁ e₂ (0 : Matrix l m R) = 0 := by
  ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply]

lemma reindex_one_aux {l l' : Type*} [Fintype l] [Fintype l'] [DecidableEq l] [DecidableEq l']
    (e : l ≃ l') : Matrix.reindex e e (1 : Matrix l l R) = 1 := by
  simpa only [Matrix.coe_reindexRingEquiv] using (Matrix.reindexRingEquiv R e).map_one

lemma isUnit_reindex_iff_aux {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] (e : ι ≃ ι') (M : Matrix ι ι R) :
    IsUnit (Matrix.reindex e e M) ↔ IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex]
  have h : e.trans e.symm = Equiv.refl ι := Equiv.ext fun x => by simp
  rw [h]
  simp

/-- A product of a right inverse with its left factor is idempotent. -/
lemma mul_self_of_mul_eq_one {S : Type*} [Ring S] (a b : S) (h : a * b = 1) :
    (b * a) * (b * a) = b * a := by
  rw [mul_assoc b a (b * a), ← mul_assoc a b a, h, one_mul]

/-- Rectangular version of `mul_self_of_mul_eq_one` for matrices. -/
lemma mul_self_mat {R : Type*} [Ring R] {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (a : Matrix α β R) (b : Matrix β α R) (h : a * b = 1) :
    (b * a) * (b * a) = b * a := by
  rw [Matrix.mul_assoc b a (b * a), ← Matrix.mul_assoc a b a, h, Matrix.one_mul]

end Generic

/-! ## `MvNGen` transitivity -/

section Trans

variable {S : Type*} [Ring S]

lemma MvNGen_trans_aux {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    {p : Matrix ι₁ ι₁ S} {q : Matrix ι₂ ι₂ S} {r : Matrix ι₃ ι₃ S}
    (hp : p * p = p) (hq : q * q = q) (hr : r * r = r)
    (hpq : MvNGen p q) (hqr : MvNGen q r) : MvNGen p r := by
  obtain ⟨a₁, b₁, hb₁a₁, ha₁b₁⟩ := hpq
  obtain ⟨a₂, b₂, hb₂a₂, ha₂b₂⟩ := hqr
  refine ⟨a₂ * a₁, b₁ * b₂, ?_, ?_⟩
  · rw [Matrix.mul_assoc b₁ b₂ (a₂ * a₁), ← Matrix.mul_assoc b₂ a₂ a₁, hb₂a₂, ← ha₁b₁,
      Matrix.mul_assoc a₁ b₁ a₁, ← Matrix.mul_assoc b₁ a₁ (b₁ * a₁), hb₁a₁, hp]
  · rw [Matrix.mul_assoc a₂ a₁ (b₁ * b₂), ← Matrix.mul_assoc a₁ b₁ b₂, ha₁b₁, ← hb₂a₂,
      Matrix.mul_assoc b₂ a₂ b₂, ← Matrix.mul_assoc a₂ b₂ (a₂ * b₂), ha₂b₂, hr]

end Trans

/-! ## Small block-identity helpers -/

section Blocks

variable {A : Type*} [CommRing A] [Algebra ℂ A]

lemma wUpdate_eq_wCol_mul_wRow {n D : ℕ}
    (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (Ψ : ℤ → Matrix (Fin n) (Fin n) A) :
    wUpdate n D c Ψ = wCol n D Ψ * wRow n D c := by
  ext p q
  simp only [wUpdate, wCol, wRow, Matrix.mul_apply]

end Blocks

section Comp

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The companion pencil of a coefficient sequence is the reindexing of `z • wBA + wBB`. -/
lemma wPenPencil_reindex {n d : ℕ} (c : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (z : ℂ) :
    Work.KT.Idx.wPenPencil X n d c z
      = Matrix.reindex finProdFinEquiv finProdFinEquiv
          (z • wBA (A := C(X, ℂ)) n d + wBB n d c) := by
  rw [Work.KT.Idx.wPenPencil, Work.KT.Idx.wPenAf, Work.KT.Idx.wPenBf,
      wBA_eq_wPenA, wBB_eq_wPenB,
      ← reindex_smul_aux finProdFinEquiv finProdFinEquiv z (Work.KT.Idx.wPenA X n d),
      ← reindex_add_aux finProdFinEquiv finProdFinEquiv
        (z • Work.KT.Idx.wPenA X n d) (Work.KT.Idx.wPenB X n d c)]

/-- The W pencil is a unit whenever the companion pencil is. -/
lemma wBlk_unit_of_wPenPencil {n d : ℕ} (c : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (h : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (Work.KT.Idx.wPenPencil X n d c z)) :
    ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • wBA (A := C(X, ℂ)) n d + wBB n d c) :=
  fun z hz =>
    (isUnit_reindex_iff_aux finProdFinEquiv _).mp (by rw [← wPenPencil_reindex X c z]; exact h z hz)

/-- `wQ` of the companion pencil is a unit on the unit circle. -/
lemma wQ_isUnit_of_wPenPencil {n d : ℕ} (c : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (h : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (Work.KT.Idx.wPenPencil X n d c z)) :
    ∀ z : ℂ, ‖z‖ = 1 → IsUnit (wQ (A := C(X, ℂ)) n d c z) := by
  intro z hz
  have hz0 : z ≠ 0 := by intro h0; rw [h0] at hz; simp at hz
  exact wQ_isUnit_of_pencil (X := X) n d c z hz0 (wBlk_unit_of_wPenPencil X c h z hz)

/-- The Fourier relation `wRow · wCol = 1`. -/
lemma wRow_mul_wCol_aux (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (wQ (A := C(X, ℂ)) n D c z)) :
    wRow n D c * wCol n D (wPsi X n D c) = 1 := by
  have hLHS : wRow n D c * wCol n D (wPsi X n D c)
      = ∑ k : Fin (D + 1), c k * wPsi X n D c ((k : ℤ) + (-1)) := by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.mul_apply]
    rw [Fintype.sum_prod_type]
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.mul_apply]
    rfl
  rw [hLHS, wRow_wPsi X n D c hQ (-1)]
  simp

end Comp

/-! ## The main theorem -/

/-- **Prepend a zero coefficient: the Bott index changes by the trivial class.**

Hatcher's formula (2) in the "W" form: for a coefficient sequence `b : Fin (d+1) → Mₙ(C(X, ℂ))`,
the sequence `(0, b)` (`Work.KT.Idx.preSeq X b`, polynomial `z · q_b`, one more block) has a
companion pencil whose Riesz projection splits as `E₋(M_b) ⊕ 1_n` (the extra summand corresponds
to the block `[E, z]`, whose `E₋` is `1_n`), so the index grows by `cls ⟨n, 1⟩`.

Route.  `Work.KT.Idx.matPenProj` is in `Submission/Work/KT/Idx/PenDefs.lean`; its idempotency is
`Work.Idx.penProj_idem` (in parallel).  Eliminating the superdiagonal `-1` in the last-but-one
block row of the companion pencil of `preSeq X b` by the *z-dependent* (but unit-valued)
substitution `w_{d+1} = u_{d+1} + z w_d` (compare the columns/rows via the polynomial variable)
splits the pencil as the direct sum of the pencil of `b` and the pencil `z ↦ z·1_n` up to
invertible right/left factors that are *constant in `z` after the substitution*; the projection of
a block-diagonal pencil is block-diagonal, the projection is unchanged (up to `Mat.MvN`) by
multiplying the pencil by units constant in `z`, and the projection of the pencil `z ↦ z·1_n` is
`1_n` (`det` has the single root `z = 0`).  Helpers worth having: `det (companion pencil at z)
= det (Σ_j b_j z^j)`, so `det M_{preSeq b} = z^n · det M_b`, i.e. the roots are those of `M_b`
plus `n` roots at `z = 0`; and the additivity of `matPenProj` over block-diagonal pencils. -/
theorem wPen_prepend (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (h : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (Work.KT.Idx.wPenPencil X n d b z))
    (h' : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (Work.KT.Idx.wPenPencil X n (d + 1) (Work.KT.Idx.preSeq X b) z)) :
    Work.KT.cls (⟨(d + 2) * n, Work.KT.Idx.matPenProj X (Work.KT.Idx.wPenAf X n (d + 1))
        (Work.KT.Idx.wPenBf X n (d + 1) (Work.KT.Idx.preSeq X b))⟩ : Work.KT.Mat C(X, ℂ)) =
      Work.KT.cls (⟨(d + 1) * n, Work.KT.Idx.matPenProj X (Work.KT.Idx.wPenAf X n d)
          (Work.KT.Idx.wPenBf X n d b)⟩ : Work.KT.Mat C(X, ℂ))
        + Work.KT.cls (Work.KT.Mat.one C(X, ℂ) n) := by
  have hQ := wQ_isUnit_of_wPenPencil X b h
  have hQ' := wQ_isUnit_of_wPenPencil X (Work.KT.Idx.preSeq X b) h'
  let pb : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ) :=
    blkPenProj X (wBA (A := C(X, ℂ)) n d) (wBB n d b)
  let pbig : Matrix (Fin (d + 2) × Fin n) (Fin (d + 2) × Fin n) C(X, ℂ) :=
    blkPenProj X (wBA (A := C(X, ℂ)) n (d + 1)) (wBB n (d + 1) (Work.KT.Idx.preSeq X b))
  let U : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ) :=
    wUpdate n d b (wPsi X n d b)
  let Inc : Matrix (Fin (d + 2) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ) := wInc (X := X) n d
  have hpb_idem : pb * pb = pb := blkPenProj_idem X b hQ
  have hpbig_idem : pbig * pbig = pbig := blkPenProj_idem X (Work.KT.Idx.preSeq X b) hQ'
  have hIncT : Inc * Matrix.transpose Inc = wQbig (X := X) n d := rfl
  have hcol : ∀ p q : Fin (d + 2) × Fin n, (q.1 : ℕ) = d + 1 →
      wBA (A := C(X, ℂ)) n (d + 1) p q = 0 := by
    intro p q hq
    simp only [wBA]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h2 (by rw [h1]; exact hq)
  have hpbig_qbig : pbig * wQbig (X := X) n d = pbig := by
    show blkPenProj X (wBA (A := C(X, ℂ)) n (d + 1)) (wBB n (d + 1) (Work.KT.Idx.preSeq X b))
        * wQbig (X := X) n d
      = blkPenProj X (wBA (A := C(X, ℂ)) n (d + 1)) (wBB n (d + 1) (Work.KT.Idx.preSeq X b))
    exact blkPenProj_mul_of_mul (X := X) (wBA (A := C(X, ℂ)) n (d + 1))
      (wBB n (d + 1) (Work.KT.Idx.preSeq X b)) (wQbig (X := X) n d)
      (mul_wQbig_of_last_col_zero (X := X) n d (wBA (A := C(X, ℂ)) n (d + 1)) hcol)
      (wBlk_unit_of_wPenPencil X (Work.KT.Idx.preSeq X b) h')
  have hMdef : Matrix.transpose Inc * pbig * Inc = pb + U := by
    show Matrix.transpose (wInc (X := X) n d)
        * blkPenProj X (wBA (A := C(X, ℂ)) n (d + 1)) (wBB n (d + 1) (Work.KT.Idx.preSeq X b))
        * wInc (X := X) n d
      = blkPenProj X (wBA (A := C(X, ℂ)) n d) (wBB n d b) + wUpdate n d b (wPsi X n d b)
    exact blkPenProj_preSeq_blocks (X := X) n d b hQ hQ'
  have hM_idem : (pb + U) * (pb + U) = pb + U := by
    rw [← hMdef]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Inc (Matrix.transpose Inc) (pbig * Inc), hIncT,
        ← Matrix.mul_assoc pbig (wQbig (X := X) n d) (pbig * Inc), hpbig_qbig,
        ← Matrix.mul_assoc pbig pbig Inc, hpbig_idem]
  have hRowCol : wRow n d b * wCol n d (wPsi X n d b) = 1 := wRow_mul_wCol_aux X n d b hQ
  have hUeq : U = wCol n d (wPsi X n d b) * wRow n d b :=
    wUpdate_eq_wCol_mul_wRow b (wPsi X n d b)
  have hU_idem : U * U = U := by
    have hh := mul_self_mat (wRow n d b) (wCol n d (wPsi X n d b)) hRowCol
    rw [hUeq]
    exact hh
  have hRow_pb : wRow n d b * pb = 0 := by
    show wRow n d b * blkPenProj X (wBA (A := C(X, ℂ)) n d) (wBB n d b) = 0
    exact wRow_mul_blkPenProj (X := X) n d b hQ
  have hUPb : U * pb = 0 := by rw [hUeq, Matrix.mul_assoc, hRow_pb, Matrix.mul_zero]
  have hPbU : pb * U = 0 := by
    have h4 : pb * U + U * pb = 0 := by
      have hmm := hM_idem
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hpb_idem, hU_idem] at hmm
      have h2 : pb * U + (U * pb + U) = U := by
        have h3 : pb + (pb * U + (U * pb + U)) = pb + U := by
          rw [← hmm, add_assoc]
        exact add_left_cancel h3
      have h5 : (pb * U + U * pb) + U = 0 + U := by rw [add_assoc, h2, zero_add]
      exact add_right_cancel h5
    rwa [hUPb, add_zero] at h4
  have h1 : MvNGen pbig (pb + U) := by
    refine ⟨Matrix.transpose Inc * pbig, pbig * Inc, ?_, ?_⟩
    · rw [Matrix.mul_assoc pbig Inc (Matrix.transpose Inc * pbig),
          ← Matrix.mul_assoc Inc (Matrix.transpose Inc) pbig, hIncT,
          ← Matrix.mul_assoc pbig (wQbig (X := X) n d) pbig, hpbig_qbig, hpbig_idem]
    · rw [Matrix.mul_assoc (Matrix.transpose Inc) pbig (pbig * Inc),
          ← Matrix.mul_assoc pbig pbig Inc, hpbig_idem,
          ← Matrix.mul_assoc (Matrix.transpose Inc) pbig Inc, hMdef]
  have h2 : MvNGen (pb + U)
      (Matrix.fromBlocks pb (0 : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ))
        (0 : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ)) U) :=
    MvNGen_add_fromBlocks pb U hpb_idem hU_idem hPbU hUPb
  have hidem_FU : (Matrix.fromBlocks pb
        (0 : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ))
        (0 : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ)) U)
      * (Matrix.fromBlocks pb
        (0 : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ))
        (0 : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ)) U)
      = Matrix.fromBlocks pb
        (0 : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ))
        (0 : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ)) U := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hpb_idem, hU_idem]
  have hidem_F1 : (Matrix.fromBlocks pb (0 : Matrix (Fin (d + 1) × Fin n) (Fin n) C(X, ℂ))
        (0 : Matrix (Fin n) (Fin (d + 1) × Fin n) C(X, ℂ))
        (1 : Matrix (Fin n) (Fin n) C(X, ℂ)))
      * (Matrix.fromBlocks pb (0 : Matrix (Fin (d + 1) × Fin n) (Fin n) C(X, ℂ))
        (0 : Matrix (Fin n) (Fin (d + 1) × Fin n) C(X, ℂ))
        (1 : Matrix (Fin n) (Fin n) C(X, ℂ)))
      = Matrix.fromBlocks pb (0 : Matrix (Fin (d + 1) × Fin n) (Fin n) C(X, ℂ))
        (0 : Matrix (Fin n) (Fin (d + 1) × Fin n) C(X, ℂ))
        (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hpb_idem,
      Matrix.mul_one]
  have h3 : MvNGen (Matrix.fromBlocks pb
        (0 : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ))
        (0 : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ)) U)
      (Matrix.fromBlocks pb (0 : Matrix (Fin (d + 1) × Fin n) (Fin n) C(X, ℂ))
        (0 : Matrix (Fin n) (Fin (d + 1) × Fin n) C(X, ℂ))
        (1 : Matrix (Fin n) (Fin n) C(X, ℂ))) := by
    refine ⟨Matrix.fromBlocks pb (0 : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ))
              (0 : Matrix (Fin n) (Fin (d + 1) × Fin n) C(X, ℂ)) (wRow n d b),
            Matrix.fromBlocks pb (0 : Matrix (Fin (d + 1) × Fin n) (Fin n) C(X, ℂ))
              (0 : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ))
              (wCol n d (wPsi X n d b)), ?_, ?_⟩
    · rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hpb_idem, ← hUeq]
    · rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hpb_idem, hRowCol]
  have hdiag : MvNGen pbig
      (Matrix.fromBlocks pb (0 : Matrix (Fin (d + 1) × Fin n) (Fin n) C(X, ℂ))
        (0 : Matrix (Fin n) (Fin (d + 1) × Fin n) C(X, ℂ))
        (1 : Matrix (Fin n) (Fin n) C(X, ℂ))) :=
    MvNGen_trans_aux hpbig_idem hidem_FU hidem_F1
      (MvNGen_trans_aux hpbig_idem hM_idem hidem_FU h1 h2) h3
  have hpbMat_idem : Work.KT.Mat.IsIdem
      (⟨(d + 1) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv pb⟩ :
        Work.KT.Mat C(X, ℂ)) := isIdem_reindex finProdFinEquiv hpb_idem
  have hpbigMat_idem : Work.KT.Mat.IsIdem
      (⟨(d + 2) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv pbig⟩ :
        Work.KT.Mat C(X, ℂ)) := isIdem_reindex finProdFinEquiv hpbig_idem
  have hOne_idem : Work.KT.Mat.IsIdem (Work.KT.Mat.one C(X, ℂ) n) := by
    show Work.KT.Mat.IsIdem
      (⟨n, (1 : Matrix (Fin n) (Fin n) C(X, ℂ))⟩ : Work.KT.Mat C(X, ℂ))
    exact Matrix.one_mul _
  have hsumMat_idem : Work.KT.Mat.IsIdem
      (Work.KT.Mat.sum
        (⟨(d + 1) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv pb⟩ :
          Work.KT.Mat C(X, ℂ)) (Work.KT.Mat.one C(X, ℂ) n)) :=
    Work.KT.Mat.sum_idem hpbMat_idem hOne_idem
  have hmat : Work.KT.Mat.MvN
      (⟨(d + 2) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv pbig⟩ :
        Work.KT.Mat C(X, ℂ))
      ⟨(d + 1) * n + n,
        Matrix.reindex ((Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin n))).trans
            finSumFinEquiv)
          ((Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin n))).trans finSumFinEquiv)
          (Matrix.fromBlocks pb (0 : Matrix (Fin (d + 1) × Fin n) (Fin n) C(X, ℂ))
            (0 : Matrix (Fin n) (Fin (d + 1) × Fin n) C(X, ℂ))
            (1 : Matrix (Fin n) (Fin n) C(X, ℂ)))⟩ :=
    MvNGen.toMat finProdFinEquiv
      ((Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin n))).trans finSumFinEquiv) hdiag
  have hm : Matrix.reindex
        ((Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin n))).trans finSumFinEquiv)
        ((Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin n))).trans finSumFinEquiv)
        (Matrix.fromBlocks pb (0 : Matrix (Fin (d + 1) × Fin n) (Fin n) C(X, ℂ))
          (0 : Matrix (Fin n) (Fin (d + 1) × Fin n) C(X, ℂ))
          (1 : Matrix (Fin n) (Fin n) C(X, ℂ)))
      = (Work.KT.Mat.sum
          (⟨(d + 1) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv pb⟩ :
            Work.KT.Mat C(X, ℂ)) (Work.KT.Mat.one C(X, ℂ) n)).2 := by
    simp only [Work.KT.Mat.sum, Work.KT.Mat.one]
    rw [← reindex_reindex_aux (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin n)))
          (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin n))) finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks pb (0 : Matrix (Fin (d + 1) × Fin n) (Fin n) C(X, ℂ))
            (0 : Matrix (Fin n) (Fin (d + 1) × Fin n) C(X, ℂ))
            (1 : Matrix (Fin n) (Fin n) C(X, ℂ)))]
    rw [reindex_fromBlocks_aux]
    simp only [reindex_zero_aux, reindex_one_aux]
  have hmat' : Work.KT.Mat.MvN
      (⟨(d + 2) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv pbig⟩ :
        Work.KT.Mat C(X, ℂ))
      (Work.KT.Mat.sum
        (⟨(d + 1) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv pb⟩ :
          Work.KT.Mat C(X, ℂ)) (Work.KT.Mat.one C(X, ℂ) n)) := by
    obtain ⟨a, b, hba, hab⟩ := hmat
    exact ⟨a, b, hba, hab.trans hm⟩
  have hbig : Work.KT.Idx.matPenProj X (Work.KT.Idx.wPenAf X n (d + 1))
        (Work.KT.Idx.wPenBf X n (d + 1) (Work.KT.Idx.preSeq X b))
      = Matrix.reindex finProdFinEquiv finProdFinEquiv pbig := by
    rw [Work.KT.Idx.wPenAf, Work.KT.Idx.wPenBf, matPenProj_eq_penProjMat, penProjMat_reindex]
    rfl
  have hsmall : Work.KT.Idx.matPenProj X (Work.KT.Idx.wPenAf X n d)
        (Work.KT.Idx.wPenBf X n d b)
      = Matrix.reindex finProdFinEquiv finProdFinEquiv pb := by
    rw [Work.KT.Idx.wPenAf, Work.KT.Idx.wPenBf, matPenProj_eq_penProjMat, penProjMat_reindex]
    rfl
  rw [hbig, hsmall]
  exact (Work.KT.cls_eq_of_mvN hpbigMat_idem hsumMat_idem hmat').trans
    (Work.KT.cls_sum hpbMat_idem hOne_idem)

end

end Work.Idx
