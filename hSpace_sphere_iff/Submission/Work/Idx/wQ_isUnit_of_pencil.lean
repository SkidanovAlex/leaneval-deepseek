import Mathlib
import Submission.Work.Idx.WPenBlk
import Submission.Work.Idx.WPenRes

namespace Work.Idx

open Matrix
open scoped BigOperators

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The "geometric" block column `v ↦ (v, zv, …, z^D v)`, as a matrix whose `b`-th column is the
image of the `b`-th standard basis vector. -/
def wIota (n D : ℕ) (z : ℂ) : Matrix (Fin (D + 1) × Fin n) (Fin n) A :=
  fun p b => (z ^ (p.1 : ℕ)) • (1 : Matrix (Fin n) (Fin n) A) p.2 b

/-- The block column with `1` in the last block (`ε_D` in the derivation). -/
def wEpsD (n D : ℕ) : Matrix (Fin (D + 1) × Fin n) (Fin n) A :=
  fun p b => if p.1 = Fin.last D then (1 : Matrix (Fin n) (Fin n) A) p.2 b else 0

/-- Matrix multiplication as an explicit function.  Written out (rather than using `*`) so that
the assembly below does not run into the `CStarMatrix`/`Matrix` product-instance ambiguity that
arises for matrices over the C⋆-algebra `C(X, ℂ)`. -/
def mmul {l m n : Type*} [Fintype m] (M : Matrix l m A) (N : Matrix m n A) : Matrix l n A :=
  fun i k => ∑ j, M i j * N j k

lemma mmul_eq_mul {l m n : Type*} [Fintype m] (M : Matrix l m A) (N : Matrix m n A) :
    mmul M N = M * N := by
  ext i k
  rw [Matrix.mul_apply]
  rfl

lemma mmul_assoc {l m n o : Type*} [Fintype m] [Fintype n]
    (M : Matrix l m A) (N : Matrix m n A) (P : Matrix n o A) :
    mmul (mmul M N) P = mmul M (mmul N P) := by
  ext i k
  simp only [mmul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun j _ => by rw [mul_assoc]

lemma mmul_one_mul {n o : Type*} [Fintype n] [DecidableEq n] (M : Matrix n o A) :
    mmul (1 : Matrix n n A) M = M := by
  ext i k
  simp only [mmul]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro j _ hji; rw [Matrix.one_apply_ne (fun h => hji h.symm), zero_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The row-block of `(z • wBA n D + wBB n D c) * wIota n D z` at block `k`: it is `0` unless `k`
is the last block, where it is `wQ n D c z`.  (This is the block form of the identity
`(z • wBA + wBB) * wIota = wEpsD * wQ`.) -/
lemma blk_sum_pencil (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ)
    (k : Fin (D + 1)) :
    (∑ i : Fin (D + 1), (z ^ (i : ℕ)) • blkOf (z • wBA n D + wBB n D c) k i)
      = if k = Fin.last D then wQ n D c z else 0 := by
  have hblk : ∀ i : Fin (D + 1),
      blkOf (z • wBA n D + wBB n D c) k i = z • bA (A := A) n D k i + bB n D c k i := by
    intro i
    rw [blkOf_add, blkOf_smul, blkOf_wBA, blkOf_wBB]
  by_cases hk : (k : ℕ) = D
  · have hkl : k = Fin.last D := Fin.ext (by rw [Fin.val_last]; exact hk)
    subst hkl
    rw [if_pos rfl, wQ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hblk i, bA_apply_last n D (Fin.last D) i hk, bB_apply_last n D c (Fin.last D) i hk]
    simp
  · rw [if_neg (fun h => hk (by rw [h, Fin.val_last]))]
    have hklt : (k : ℕ) < D := lt_of_ne_last k hk
    have key : ∀ i : Fin (D + 1),
        (z ^ (i : ℕ)) • blkOf (z • wBA n D + wBB n D c) k i
          = (if i = k then (z ^ ((k : ℕ) + 1)) • (1 : Matrix (Fin n) (Fin n) A) else 0)
            + (if i = isucc k hklt then -((z ^ ((k : ℕ) + 1)) •
                (1 : Matrix (Fin n) (Fin n) A)) else 0) := by
      intro i
      by_cases h1 : i = k
      · subst i
        rw [hblk k, bA_apply_not_last n D k k hk, bB_apply_not_last n D c k k hk]
        have hne : ((k : ℕ) + 1) ≠ (k : ℕ) := by omega
        have hne2 : ¬ (k = isucc k hklt) := by
          intro h; have := congrArg Fin.val h; rw [isucc_val] at this; omega
        rw [if_pos rfl, if_neg hne, if_pos rfl, if_neg hne2, add_zero, add_zero]
        rw [smul_smul, ← pow_succ]
      · by_cases h2 : i = isucc k hklt
        · subst i
          rw [hblk (isucc k hklt), bA_apply_not_last n D k (isucc k hklt) hk,
            bB_apply_not_last n D c k (isucc k hklt) hk]
          have hne1 : ¬ (isucc k hklt = k) := by
            intro h; have := congrArg Fin.val h; rw [isucc_val] at this; omega
          rw [if_neg hne1, if_pos (isucc_val k hklt).symm, if_neg hne1, if_pos rfl,
            smul_zero, zero_add, zero_add, smul_neg]
          simp only [isucc_val]
        · rw [hblk i, bA_apply_not_last n D k i hk, bB_apply_not_last n D c k i hk]
          have hne : (k : ℕ) + 1 ≠ (i : ℕ) := by
            intro h; exact h2 (Fin.ext h.symm)
          rw [if_neg h1, if_neg hne, if_neg h1, if_neg h2]
          simp
    rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ k),
      if_pos (Finset.mem_univ _)]
    rw [add_neg_cancel]

lemma mmul_wIota_apply (n D : ℕ) (z : ℂ)
    (M : Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) A)
    (k : Fin (D + 1)) (a b : Fin n) :
    mmul M (wIota (A := A) n D z) (k, a) b
      = (∑ i : Fin (D + 1), (z ^ (i : ℕ)) • blkOf M k i) a b := by
  simp only [mmul]
  rw [Fintype.sum_prod_type, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.smul_apply]
  simp only [wIota, blkOf]
  rw [Finset.sum_eq_single b]
  · rw [Matrix.one_apply_eq, Algebra.smul_def, Algebra.smul_def, mul_one, mul_comm]
  · intro y _ hyb
    rw [Matrix.one_apply_ne hyb, smul_zero, mul_zero]
  · intro hb; exact absurd (Finset.mem_univ b) hb

lemma mmul_wEpsD_apply (n D : ℕ)
    (M : Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) A) (k : Fin (D + 1)) (a q : Fin n) :
    mmul M (wEpsD (A := A) n D) (k, a) q = blkOf M k (Fin.last D) a q := by
  simp only [mmul]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (Fin.last D)]
  · rw [Finset.sum_congr rfl (fun c _ => by rw [wEpsD, if_pos rfl])]
    simp only [blkOf, Matrix.one_apply]
    rw [Finset.sum_eq_single q]
    · rw [if_pos rfl, mul_one]
    · intro c _ hcq; rw [if_neg hcq, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro j _ hj
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [wEpsD, if_neg hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma mmul_wEpsD_wQ_apply (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ)
    (k : Fin (D + 1)) (a b : Fin n) :
    mmul (wEpsD (A := A) n D) (wQ n D c z) (k, a) b
      = if k = Fin.last D then wQ n D c z a b else 0 := by
  simp only [mmul]
  by_cases hk : k = Fin.last D
  · rw [if_pos hk]
    rw [Finset.sum_eq_single a]
    · rw [wEpsD, if_pos hk, Matrix.one_apply_eq, one_mul]
    · intro q _ hqa
      rw [wEpsD, if_pos hk, Matrix.one_apply_ne (fun h => hqa h.symm), zero_mul]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  · rw [if_neg hk]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [wEpsD, if_neg hk, zero_mul]

/-- `(z • wBA n D + wBB n D c) * wIota n D z = wEpsD n D * wQ n D c z`, in the explicit
multiplication `mmul`. -/
lemma pencil_mmul_wIota (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ) :
    mmul (z • wBA n D + wBB n D c) (wIota (A := A) n D z)
      = mmul (wEpsD (A := A) n D) (wQ n D c z) := by
  ext p b
  obtain ⟨k, a⟩ := p
  rw [mmul_wIota_apply, blk_sum_pencil, mmul_wEpsD_wQ_apply]
  by_cases hk : k = Fin.last D <;> simp [hk]

/-- **The general form of the lemma.** If the W pencil of `c` is a unit then so is `wQ n D c z`,
whenever `z ≠ 0`.  (In fact the argument gives the statement for every `z`, and over an arbitrary
commutative `ℂ`-algebra; the hypothesis `z ≠ 0` of the intended application is not needed.)

Derivation.  Write `P = z • wBA n D + wBB n D c` and let `Pinv` be the inverse of `P` given by
`h`.  The block identity `P * wIota = wEpsD * wQ` (`pencil_mmul_wIota`), the relation
`mmul Pinv P = 1`, and associativity of `mmul` give `wIota = mmul (mmul Pinv (wEpsD)) (wQ)`.
Evaluating at the first block row gives `mmul (blkOf Pinv 0 (last)) (wQ) = 1`; taking determinants
yields `IsUnit (wQ.det)`, hence `IsUnit (wQ)`. -/
theorem wQ_isUnit_of_pencil_gen {A : Type*} [CommRing A] [Algebra ℂ A]
    (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ)
    (h : IsUnit (z • wBA n D + wBB n D c)) :
    IsUnit (wQ n D c z) := by
  obtain ⟨Pinv, hPinv⟩ : ∃ P : Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) A,
      P = (↑(h.unit⁻¹) : Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) A) := ⟨_, rfl⟩
  have hP : (↑h.unit : Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) A)
      = z • wBA n D + wBB n D c := IsUnit.unit_spec h
  have hinvP : mmul Pinv (z • wBA n D + wBB n D c) = 1 := by
    rw [← hP, hPinv]
    exact Units.inv_mul h.unit
  have h2 : wIota (A := A) n D z
      = mmul (mmul Pinv (wEpsD n D)) (wQ n D c z) := by
    rw [mmul_assoc, ← pencil_mmul_wIota, ← mmul_assoc, hinvP, mmul_one_mul]
  have key : mmul (blkOf Pinv (0 : Fin (D + 1)) (Fin.last D)) (wQ n D c z) = 1 := by
    ext a b
    have hE := congrFun (congrFun h2 (((0 : Fin (D + 1)), a))) b
    have hL : wIota (A := A) n D z ((0 : Fin (D + 1)), a) b
        = (1 : Matrix (Fin n) (Fin n) A) a b := by
      simp [wIota]
    have hR : mmul (mmul Pinv (wEpsD n D)) (wQ n D c z) ((0 : Fin (D + 1)), a) b
        = mmul (blkOf Pinv (0 : Fin (D + 1)) (Fin.last D)) (wQ n D c z) a b := by
      have e1 : mmul (mmul Pinv (wEpsD n D)) (wQ n D c z) ((0 : Fin (D + 1)), a) b
          = ∑ q : Fin n, mmul Pinv (wEpsD n D) ((0 : Fin (D + 1)), a) q * wQ n D c z q b :=
        rfl
      have e2 : (∑ q : Fin n, mmul Pinv (wEpsD n D) ((0 : Fin (D + 1)), a) q * wQ n D c z q b)
          = ∑ q : Fin n, blkOf Pinv (0 : Fin (D + 1)) (Fin.last D) a q * wQ n D c z q b := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [mmul_wEpsD_apply]
      have e3 : (∑ q : Fin n, blkOf Pinv (0 : Fin (D + 1)) (Fin.last D) a q * wQ n D c z q b)
          = mmul (blkOf Pinv (0 : Fin (D + 1)) (Fin.last D)) (wQ n D c z) a b := rfl
      rw [e1, e2, e3]
    rw [hL, hR] at hE
    exact hE.symm
  have hdet : (blkOf Pinv (0 : Fin (D + 1)) (Fin.last D)).det * (wQ n D c z).det = 1 := by
    have h : (mmul (blkOf Pinv (0 : Fin (D + 1)) (Fin.last D)) (wQ n D c z)).det = 1 := by
      rw [key, Matrix.det_one]
    rw [mmul_eq_mul, Matrix.det_mul] at h
    exact h
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (IsUnit.of_mul_eq_one_right _ hdet)

end


/-- **The polynomial matrix of a W pencil is a unit whenever the pencil is.**

`wBA n D` is the `z`-coefficient and `wBB n D c` the constant part of the W linearisation of a
coefficient sequence `c : Fin (D+1) → Mₙ(C(X, ℂ))` (`Work.KT.Idx.wPenA`/`wPenB` on the block index
`Fin (D+1) × Fin n`), and `wQ n D c z = ∑_j z^j • c_j`.  Claim: for `z ≠ 0`,
`IsUnit (z • wBA n D + wBB n D c) → IsUnit (wQ n D c z)`.

Route.  `det (z • wBA n D + wBB n D c) = det (wQ n D c z)` (both are polynomials in `z`; the
pencil is block upper-triangular with `z·1` on the diagonal except the last block row; the
last row is the coefficient row; one proves the identity by induction on `D` or by expanding along
the first row, using that the first block column of the pencil is `z·1` in the (0,0) block).  Over
the commutative ring `C(X, ℂ)`, `IsUnit M ↔ IsUnit M.det` (`Matrix.isUnit_iff_isUnit_det`), so
`IsUnit (pencil) → IsUnit (wQ n D c z)`.  (Equivalently: over each point `x : X` the evaluation is
a ring homomorphism, `IsUnit (wQ …)` iff every `wQ n D c z` evaluated at `x` is invertible
(`Work.KT.Fund.isUnit_matrix_forall`), and if `Q v₀ = 0` with `v₀ ≠ 0` then the nonzero vector
whose block `k` is `z^k • v₀` lies in the kernel of the pencil.) -/
theorem wQ_isUnit_of_pencil {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (z : ℂ) (hz : z ≠ 0)
    (h : IsUnit (z • wBA (A := C(X, ℂ)) n D + wBB n D c)) :
    IsUnit (wQ (A := C(X, ℂ)) n D c z) :=
  wQ_isUnit_of_pencil_gen (A := C(X, ℂ)) n D c z h


end Work.Idx
