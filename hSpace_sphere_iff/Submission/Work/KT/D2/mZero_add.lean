import Mathlib
import Submission.Work.KT.D2.mZero
import Submission.Work.KT.D2.windLoop_mul
import Submission.Work.KT.D2.Basic

/-!
# `Work.KT.D2.mZero_add` — additivity of the winding invariant under block sums

`Work.KT.D2.mZero` is the winding invariant of an idempotent matrix over `Kpair ℝ² = C(D²/S¹)`.
This file proves that it is additive under the block sum `Mat.sum`: for idempotents `p`, `q`,
`mZero (p ⊕ q) = mZero p + mZero q`.

The proof chooses, for `p ⊕ q`, the block-diagonal trivialisation `U x = u_p x ⊕ u_q x` built from
the chosen trivialisations `u_p = trivU y0 p`, `u_q = trivU y0 q`.  The universal property
`mZero_eq` identifies `mZero (p ⊕ q)` with the winding of the boundary loop of `U`, the corner
determinant `det (e * U x * e + (1 - e))` factorises as a product of the two corner determinants,
and `degNZ` is additive under products (`degNZ_mul`).  Each factor is recognised, through
`mZero_eq` again (proof-irrelevantly), as `mZero p` and `mZero q`.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.KT.D2

open Matrix
open Classical

noncomputable section

/-! ## Block-diagonal matrices -/

/-- The block-diagonal matrix `[[A, 0], [0, B]]`, reindexed along `finSumFinEquiv` to a
`Fin (n + m)`-indexed matrix.  It is the second component of the block sum `Mat.sum`. -/
def bdp {R : Type} [Ring R] {n m : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin m) (Fin m) R) : Matrix (Fin (n + m)) (Fin (n + m)) R :=
  (Matrix.reindexRingEquiv R (finSumFinEquiv (m := n) (n := m)))
    (Matrix.fromBlocks A 0 0 B)

/-- The second component of `Mat.sum` is the block-diagonal matrix. -/
lemma Mat_sum_snd_bdp {R : Type} [Ring R] {n m : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (N : Matrix (Fin m) (Fin m) R) :
    (Mat.sum (⟨n, M⟩ : Mat R) ⟨m, N⟩).2 = bdp M N := rfl

/-- The block-diagonal embedding is multiplicative. -/
lemma bdp_mul {R : Type} [Ring R] {n m : ℕ} (A A' : Matrix (Fin n) (Fin n) R)
    (B B' : Matrix (Fin m) (Fin m) R) : bdp A B * bdp A' B' = bdp (A * A') (B * B') := by
  unfold bdp
  rw [← map_mul, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_zero, Matrix.zero_mul]

/-- The block-diagonal embedding preserves the identity. -/
lemma bdp_one {R : Type} [Ring R] {n m : ℕ} :
    bdp (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  unfold bdp
  rw [Matrix.fromBlocks_one, map_one]

/-- The block-diagonal embedding is additive. -/
lemma bdp_add {R : Type} [Ring R] {n m : ℕ} (A A' : Matrix (Fin n) (Fin n) R)
    (B B' : Matrix (Fin m) (Fin m) R) : bdp A B + bdp A' B' = bdp (A + A') (B + B') := by
  unfold bdp
  rw [← map_add, Matrix.fromBlocks_add]
  simp

/-- The block-diagonal embedding respects negation. -/
lemma bdp_neg {R : Type} [Ring R] {n m : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin m) (Fin m) R) : - bdp A B = bdp (-A) (-B) := by
  unfold bdp
  rw [← map_neg, Matrix.fromBlocks_neg]
  simp

/-- The block-diagonal embedding respects subtraction. -/
lemma bdp_sub {R : Type} [Ring R] {n m : ℕ} (A A' : Matrix (Fin n) (Fin n) R)
    (B B' : Matrix (Fin m) (Fin m) R) : bdp A B - bdp A' B' = bdp (A - A') (B - B') := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, bdp_neg, bdp_add]

/-- The block-diagonal embedding, applied to `1 - A`, `1 - B`, computes `1 - bdp A B`. -/
lemma one_sub_bdp {R : Type} [Ring R] {n m : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin m) (Fin m) R) :
    (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) - bdp A B = bdp (1 - A) (1 - B) := by
  rw [show (1 : Matrix (Fin (n+m)) (Fin (n+m)) R) =
      bdp (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin m) (Fin m) R) from bdp_one.symm]
  rw [bdp_sub]

/-- The determinant of a block-diagonal matrix is the product of determinants. -/
lemma bdp_det {R : Type} [CommRing R] {n m : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin m) (Fin m) R) : (bdp A B).det = A.det * B.det := by
  unfold bdp
  rw [Matrix.coe_reindexRingEquiv, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

lemma fromBlocks_map' {R S : Type} [Ring R] [Ring S] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (B : Matrix (Fin m) (Fin m) R) (f : R →+* S) :
    (Matrix.fromBlocks A 0 0 B).map f = Matrix.fromBlocks (A.map f) 0 0 (B.map f) := by
  ext i j
  rcases i with a | a <;> rcases j with b | b <;>
    simp only [Matrix.map_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, map_zero]

/-- Entrywise image of a block-diagonal matrix under a ring homomorphism. -/
lemma bdp_map {R S : Type} [Ring R] [Ring S] {n m : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin m) (Fin m) R) (f : R →+* S) :
    (bdp A B).map f = bdp (A.map f) (B.map f) := by
  have h : (bdp A B).map f = ((Matrix.fromBlocks A 0 0 B).map f).submatrix
      (finSumFinEquiv (m:=n) (n:=m)).symm (finSumFinEquiv (m:=n) (n:=m)).symm := rfl
  rw [h, fromBlocks_map']
  rfl

/-- The boundary value of a block-diagonal matrix over `Kpair ℝ²` is the block-diagonal matrix of
the boundary values. -/
lemma bval_bdp {n m : ℕ} (y0 : Ball (Euc 2)) (M : Matrix (Fin n) (Fin n) (Kpair (Euc 2)))
    (N : Matrix (Fin m) (Fin m) (Kpair (Euc 2))) :
    bval (n+m) y0 (bdp M N) = bdp (bval n y0 M) (bval m y0 N) := by
  show (bdp M N).map (augPair (Euc 2) y0).toRingHom = bdp (bval n y0 M) (bval m y0 N)
  rw [bdp_map]
  rfl

/-- The disc family of a block-diagonal matrix is the block-diagonal matrix of the disc families. -/
lemma toCM_bdp {n m : ℕ} (M : Matrix (Fin n) (Fin n) (Kpair (Euc 2)))
    (N : Matrix (Fin m) (Fin m) (Kpair (Euc 2))) (x : Ball (Euc 2)) :
    toCM (n+m) (bdp M N) x = bdp (toCM n M x) (toCM m N x) := by
  show (bdp M N).map (evalAt x) = bdp (toCM n M x) (toCM m N x)
  rw [bdp_map]
  rfl

/-! ## The main theorem -/

theorem mZero_add (y0 : Work.KT.Ball (EuclideanSpace ℝ (Fin 2)))
    (hy0 : y0 ∈ Work.KT.bdry (EuclideanSpace ℝ (Fin 2)))
    (p q : Work.KT.Mat (Work.KT.Kpair (EuclideanSpace ℝ (Fin 2)))) (hp : p.IsIdem)
    (hq : q.IsIdem) :
    Work.KT.D2.mZero y0 hy0 (p.sum q)
      = Work.KT.D2.mZero y0 hy0 p + Work.KT.D2.mZero y0 hy0 q := by
  obtain ⟨n, M⟩ := p
  obtain ⟨m, N⟩ := q
  have hpq : (Mat.sum (⟨n, M⟩ : Mat (Kpair (Euc 2))) ⟨m, N⟩).IsIdem := Mat.sum_idem hp hq
  -- the chosen trivialising families of `p` and `q`
  let up : C(Ball (Euc 2), Matrix (Fin n) (Fin n) ℂ) := trivU y0 ⟨n, M⟩ hp
  let vp : C(Ball (Euc 2), Matrix (Fin n) (Fin n) ℂ) := trivV y0 ⟨n, M⟩ hp
  let uq : C(Ball (Euc 2), Matrix (Fin m) (Fin m) ℂ) := trivU y0 ⟨m, N⟩ hq
  let vq : C(Ball (Euc 2), Matrix (Fin m) (Fin m) ℂ) := trivV y0 ⟨m, N⟩ hq
  -- the block-diagonal trivialising families
  have hc : Continuous (fun x : Ball (Euc 2) => bdp (up x) (uq x)) := by
    have hW : Continuous (fun x : Ball (Euc 2) => Matrix.fromBlocks (up x) 0 0 (uq x)) := by
      apply continuous_pi; intro i; apply continuous_pi; intro j
      rcases i with a | a <;> rcases j with b | b <;>
        simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
            Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
      · exact (continuous_apply b).comp ((continuous_apply a).comp up.continuous)
      · exact continuous_const
      · exact continuous_const
      · exact (continuous_apply b).comp ((continuous_apply a).comp uq.continuous)
    apply continuous_pi; intro i; apply continuous_pi; intro j
    exact (continuous_apply (finSumFinEquiv.symm j)).comp
      ((continuous_apply (finSumFinEquiv.symm i)).comp hW)
  have hc' : Continuous (fun x : Ball (Euc 2) => bdp (vp x) (vq x)) := by
    have hW : Continuous (fun x : Ball (Euc 2) => Matrix.fromBlocks (vp x) 0 0 (vq x)) := by
      apply continuous_pi; intro i; apply continuous_pi; intro j
      rcases i with a | a <;> rcases j with b | b <;>
        simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
            Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
      · exact (continuous_apply b).comp ((continuous_apply a).comp vp.continuous)
      · exact continuous_const
      · exact continuous_const
      · exact (continuous_apply b).comp ((continuous_apply a).comp vq.continuous)
    apply continuous_pi; intro i; apply continuous_pi; intro j
    exact (continuous_apply (finSumFinEquiv.symm j)).comp
      ((continuous_apply (finSumFinEquiv.symm i)).comp hW)
  let U : C(Ball (Euc 2), Matrix (Fin (n+m)) (Fin (n+m)) ℂ) :=
    ⟨fun x => bdp (up x) (uq x), hc⟩
  let V : C(Ball (Euc 2), Matrix (Fin (n+m)) (Fin (n+m)) ℂ) :=
    ⟨fun x => bdp (vp x) (vq x), hc'⟩
  have huv : ∀ x, U x * V x = 1 := by
    intro x
    show bdp (up x) (uq x) * bdp (vp x) (vq x) = 1
    rw [bdp_mul, show up x * vp x = 1 from (trivU_spec y0 ⟨n,M⟩ hp).1 x,
        show uq x * vq x = 1 from (trivU_spec y0 ⟨m,N⟩ hq).1 x, bdp_one]
  have hvu : ∀ x, V x * U x = 1 := by
    intro x
    show bdp (vp x) (vq x) * bdp (up x) (uq x) = 1
    rw [bdp_mul, show vp x * up x = 1 from (trivU_spec y0 ⟨n,M⟩ hp).2.1 x,
        show vq x * uq x = 1 from (trivU_spec y0 ⟨m,N⟩ hq).2.1 x, bdp_one]
  have hconj : ∀ x, U x * toCM (n+m) (bdp M N) x = bval (n+m) y0 (bdp M N) * U x := by
    intro x
    rw [toCM_bdp, bval_bdp]
    show bdp (up x) (uq x) * bdp (toCM n M x) (toCM m N x)
        = bdp (bval n y0 M) (bval m y0 N) * bdp (up x) (uq x)
    rw [bdp_mul, bdp_mul,
        show up x * toCM n M x = bval n y0 M * up x from (trivU_spec y0 ⟨n,M⟩ hp).2.2 x,
        show uq x * toCM m N x = bval m y0 N * uq x from (trivU_spec y0 ⟨m,N⟩ hq).2.2 x]
  -- boundary data and winding loops
  let ebp : Matrix (Fin n) (Fin n) ℂ := bval n y0 M
  let ebq : Matrix (Fin m) (Fin m) ℂ := bval m y0 N
  let Eb : Matrix (Fin (n+m)) (Fin (n+m)) ℂ := bval (n+m) y0 (bdp M N)
  let Wp : C(Sph (Euc 2), ℂ) := wlmDet n ebp (up.comp inBallCM)
  let Wq : C(Sph (Euc 2), ℂ) := wlmDet m ebq (uq.comp inBallCM)
  let Wpq : C(Sph (Euc 2), ℂ) := wlmDet (n+m) Eb (U.comp inBallCM)
  have hEb : Eb = bdp ebp ebq := bval_bdp y0 M N
  have hWp : ∀ x, Wp x ≠ 0 := trivU_blk_det y0 hy0 ⟨n,M⟩ hp
  have hWq : ∀ x, Wq x ≠ 0 := trivU_blk_det y0 hy0 ⟨m,N⟩ hq
  have hdet : ∀ x : Sph (Euc 2),
      Matrix.det (Eb * U (inBall x) * Eb + (1 - Eb)) = Wp x * Wq x := by
    intro x
    rw [hEb]
    show Matrix.det (bdp ebp ebq * bdp (up (inBall x)) (uq (inBall x)) * bdp ebp ebq
        + (1 - bdp ebp ebq)) = Wp x * Wq x
    rw [bdp_mul, bdp_mul, one_sub_bdp, bdp_add, bdp_det]
    rfl
  have h : ∀ x : Sph (Euc 2), Matrix.det (Eb * U (inBall x) * Eb + (1 - Eb)) ≠ 0 :=
    fun x => by rw [hdet x]; exact mul_ne_zero (hWp x) (hWq x)
  have hfac : Wpq = Wp * Wq := by ext x; exact hdet x
  have hfg : ∀ x, (Wp * Wq) x ≠ 0 := by intro x; rw [← hfac]; exact h x
  have hchain : degNZ Wpq h = degNZ Wp hWp + degNZ Wq hWq := by
    rw [wlmDegNZcongr hfac h hfg, degNZ_mul Wp Wq hWp hWq hfg]
  have hpzero : degNZ Wp hWp = mZero y0 hy0 ⟨n,M⟩ := by
    have h1 : degNZ Wp hWp = windLoop n ebp (up.comp inBallCM) hWp := rfl
    rw [h1]
    exact (mZero_of_idem y0 hy0 ⟨n,M⟩ hp).symm
  have hqzero : degNZ Wq hWq = mZero y0 hy0 ⟨m,N⟩ := by
    have h1 : degNZ Wq hWq = windLoop m ebq (uq.comp inBallCM) hWq := rfl
    rw [h1]
    exact (mZero_of_idem y0 hy0 ⟨m,N⟩ hq).symm
  calc mZero y0 hy0 (Mat.sum (⟨n, M⟩ : Mat (Kpair (Euc 2))) ⟨m, N⟩)
      = windLoop (n+m) Eb (U.comp inBallCM) h :=
        (mZero_eq y0 hy0 (Mat.sum (⟨n, M⟩ : Mat (Kpair (Euc 2))) ⟨m, N⟩) hpq
          U V huv hvu hconj h).symm
    _ = degNZ Wpq h := rfl
    _ = degNZ Wp hWp + degNZ Wq hWq := hchain
    _ = mZero y0 hy0 ⟨n, M⟩ + mZero y0 hy0 ⟨m, N⟩ := by rw [hpzero, hqzero]

end

end Work.KT.D2
