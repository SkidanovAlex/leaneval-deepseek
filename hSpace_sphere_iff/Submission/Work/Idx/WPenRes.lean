import Mathlib
import Submission.Work.Idx.WPenBlk

/-!
# `Work.Idx.WPenRes` — the explicit inverse of the W pencil

`Work.Idx.wBA`/`wBB` are the W linearisation of a coefficient sequence `c : Fin (D+1) → Mₙ(A)`
(over a commutative `ℂ`-algebra `A`) on the block index `Fin (D+1) × Fin n`, and `wInv n D c z E`
is the claimed explicit inverse of the pencil `z • wBA n D + wBB n D c`, where `E` inverts the
polynomial matrix `wQ n D c z = ∑_j z^j • c_j`.

Here we prove `wBlk_mul_wInv : (z • wBA + wBB) * wInv = 1` (under `wQ * E = 1`) and deduce, via
the determinant, that the pencil is a unit whenever `wQ` is, with
`Ring.inverse (z • wBA + wBB) = wInv n D c z (Ring.inverse (wQ n D c z))`
(`wInv_eq_ringInverse`).  The computation is reduced to the block level by `blkOf` (the
`(k,i)`-block of a block matrix), where the sums range over `Fin (D+1)` only.
-/

namespace Work.Idx

open Matrix
open scoped BigOperators

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The `(k,i)` block of a matrix on the block index `ι × Fin n`. -/
def blkOf {ι : Type*} {n : ℕ} (M : Matrix (ι × Fin n) (ι × Fin n) A) (k i : ι) :
    Matrix (Fin n) (Fin n) A :=
  fun a b => M (k, a) (i, b)

lemma blkOf_add {ι : Type*} {n : ℕ} (M N : Matrix (ι × Fin n) (ι × Fin n) A) (k i : ι) :
    blkOf (M + N) k i = blkOf M k i + blkOf N k i := rfl

lemma blkOf_smul {ι : Type*} {n : ℕ} (r : ℂ) (M : Matrix (ι × Fin n) (ι × Fin n) A) (k i : ι) :
    blkOf (r • M) k i = r • blkOf M k i := rfl

lemma blkOf_one {ι : Type*} [DecidableEq ι] {n : ℕ} (k i : ι) :
    blkOf (1 : Matrix (ι × Fin n) (ι × Fin n) A) k i = if k = i then 1 else 0 := by
  ext a b
  by_cases h : k = i <;> by_cases h2 : a = b <;>
    simp_all [blkOf, Matrix.one_apply, Prod.ext_iff]

lemma blkOf_mul {ι : Type*} [Fintype ι] {n : ℕ}
    (M N : Matrix (ι × Fin n) (ι × Fin n) A) (k i : ι) :
    blkOf (M * N) k i = ∑ j : ι, blkOf M k j * blkOf N j i := by
  ext a b
  rw [blkOf, Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.sum_apply, Matrix.mul_apply, blkOf]

/-- A general additive identity used in the block computation. -/
lemma sub_neg_sub_combine {R : Type*} [Ring R] (X C D : R) :
    (X - C) + -(X - D) = D - C := by abel

/-! ## The block versions of the W linearisation -/

/-- The `z`-coefficient of the W linearisation, as a block matrix. -/
def bA (n D : ℕ) : Matrix (Fin (D + 1)) (Fin (D + 1)) (Matrix (Fin n) (Fin n) A) :=
  fun k i => if k = i then (if (k : ℕ) = D then 0 else 1) else 0

/-- The constant part of the W linearisation, as a block matrix. -/
def bB (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) :
    Matrix (Fin (D + 1)) (Fin (D + 1)) (Matrix (Fin n) (Fin n) A) :=
  fun k i =>
    if (k : ℕ) + 1 = (i : ℕ) then (if (k : ℕ) = D then c i else -1)
    else (if (k : ℕ) = D then c i else 0)

/-- The explicit inverse of the W pencil, as a block matrix. -/
def bInv (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ)
    (E : Matrix (Fin n) (Fin n) A) :
    Matrix (Fin (D + 1)) (Fin (D + 1)) (Matrix (Fin n) (Fin n) A) :=
  fun k i => (z ^ (k : ℕ)) • (E * wde n D c z i) -
    (if (i : ℕ) < (k : ℕ) then (z ^ ((k : ℕ) - 1 - (i : ℕ))) • (1 : Matrix (Fin n) (Fin n) A)
      else 0)

lemma bA_apply_last (n D : ℕ) (i k : Fin (D + 1)) (hi : (i : ℕ) = D) :
    bA (A := A) n D i k = 0 := by
  rw [bA]
  by_cases h : i = k
  · simp only [if_pos h, if_pos hi]
  · simp only [if_neg h]

lemma bB_apply_last (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A)
    (i k : Fin (D + 1)) (hi : (i : ℕ) = D) : bB n D c i k = c k := by
  rw [bB]
  by_cases h : (i : ℕ) + 1 = (k : ℕ)
  · simp only [if_pos h, if_pos hi]
  · simp only [if_neg h, if_pos hi]

lemma bA_apply_not_last (n D : ℕ) (i k : Fin (D + 1)) (hi : (i : ℕ) ≠ D) :
    bA (A := A) n D i k = if k = i then 1 else 0 := by
  rw [bA]
  by_cases h : i = k
  · simp only [if_pos h, if_neg hi, if_pos h.symm]
  · have h' : ¬(k = i) := fun hh => h hh.symm
    simp only [if_neg h, if_neg h']

lemma bB_apply_not_last (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A)
    (i k : Fin (D + 1)) (hi : (i : ℕ) ≠ D) :
    bB n D c i k = if (i : ℕ) + 1 = (k : ℕ) then -1 else 0 := by
  rw [bB]
  by_cases h : (i : ℕ) + 1 = (k : ℕ)
  · simp only [if_pos h, if_neg hi]
  · simp only [if_neg h, if_neg hi]

lemma smul_ite_one (n D : ℕ) (z : ℂ) (i k : Fin (D + 1)) :
    z • (if k = i then (1 : Matrix (Fin n) (Fin n) A) else 0)
      = if k = i then z • (1 : Matrix (Fin n) (Fin n) A) else 0 := by
  by_cases h : k = i <;> simp [h]

@[simp] lemma blkOf_wBA (n D : ℕ) (k i : Fin (D + 1)) :
    blkOf (wBA (A := A) n D) k i = bA n D k i := by
  ext a b
  by_cases h : k = i <;> by_cases h2 : (k : ℕ) = D <;> by_cases h3 : a = b <;>
    simp_all [blkOf, wBA, bA, Matrix.one_apply]

@[simp] lemma blkOf_wBB (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A)
    (k i : Fin (D + 1)) :
    blkOf (wBB n D c) k i = bB n D c k i := by
  ext a b
  by_cases h2 : (k : ℕ) + 1 = (i : ℕ) <;> by_cases h3 : (k : ℕ) = D <;>
    by_cases h4 : a = b <;>
    simp_all [blkOf, wBB, bB, Matrix.one_apply]

@[simp] lemma blkOf_wInv (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ)
    (E : Matrix (Fin n) (Fin n) A) (k i : Fin (D + 1)) :
    blkOf (wInv n D c z E) k i = bInv n D c z E k i := by
  ext a b
  simp only [blkOf, wInv, bInv]

/-- The successor of a block index which is not the last one. -/
def isucc {D : ℕ} (i : Fin (D + 1)) (h : (i : ℕ) < D) : Fin (D + 1) :=
  ⟨(i : ℕ) + 1, Nat.succ_lt_succ h⟩

@[simp] lemma isucc_val {D : ℕ} (i : Fin (D + 1)) (h : (i : ℕ) < D) :
    ((isucc i h : Fin (D + 1)) : ℕ) = (i : ℕ) + 1 := rfl

lemma lt_of_ne_last {D : ℕ} (i : Fin (D + 1)) (h : (i : ℕ) ≠ D) : (i : ℕ) < D := by
  have := i.isLt; omega

/-- `wd` vanishes at the last index. -/
lemma wd_last (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ) :
    wd n D c z (Fin.last D) = 0 := by
  rw [wd]
  refine Finset.sum_eq_zero fun k hk => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  have hk' : (Fin.last D : ℕ) < (k : ℕ) := hk
  have : (k : ℕ) < D + 1 := k.isLt
  simp only [Fin.val_last] at hk'
  omega

/-! ## The two block computations -/

/-- **The last block row of the pencil applied to `bInv`.** -/
lemma sum_c_mul_bInv (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ)
    {E : Matrix (Fin n) (Fin n) A} (hE : wQ n D c z * E = 1) (j : Fin (D + 1)) :
    ∑ k : Fin (D + 1), c k * bInv n D c z E k j = if (j : ℕ) = D then 1 else 0 := by
  have hterm : ∀ k : Fin (D + 1),
      c k * bInv n D c z E k j
        = (z ^ (k : ℕ)) • (c k * (E * wde n D c z j))
          - (if (j : ℕ) < (k : ℕ) then (z ^ ((k : ℕ) - 1 - (j : ℕ))) • c k else 0) := by
    intro k
    rw [bInv, mul_sub]
    congr 1
    · rw [mul_smul_comm]
    · by_cases h : (j : ℕ) < (k : ℕ) <;> simp [h, mul_smul_comm]
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib]
  have h1 : (∑ k : Fin (D + 1), (z ^ (k : ℕ)) • (c k * (E * wde n D c z j)))
      = wde n D c z j := by
    have hthis : ∀ k : Fin (D + 1), (z ^ (k : ℕ)) • (c k * (E * wde n D c z j))
        = ((z ^ (k : ℕ)) • c k) * (E * wde n D c z j) := by
      intro k
      rw [smul_mul_assoc]
    rw [Finset.sum_congr rfl fun k _ => hthis k, ← Finset.sum_mul]
    have hw : (∑ k : Fin (D + 1), (z ^ (k : ℕ)) • c k) = wQ n D c z := rfl
    rw [hw, ← mul_assoc, hE, one_mul]
  have h2 : (∑ k : Fin (D + 1),
        (if (j : ℕ) < (k : ℕ) then (z ^ ((k : ℕ) - 1 - (j : ℕ))) • c k else 0))
      = wd n D c z j := by
    rw [wd, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : j < k
    · rw [if_pos (Fin.lt_def.mp h), if_pos h]
    · rw [if_neg (fun hh => h (Fin.lt_def.mpr hh)), if_neg h]
  rw [h1, h2]
  by_cases hj : (j : ℕ) = D
  · have hj' : j = Fin.last D := Fin.ext (by rw [Fin.val_last]; exact hj)
    subst hj'
    rw [wd_last, wde]
    simp
  · rw [wde, if_neg hj, if_neg hj, sub_self]

/-- **A non-last block row of the pencil applied to `bInv`.** -/
lemma sum_row_mul_bInv (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ)
    (E : Matrix (Fin n) (Fin n) A) (i j : Fin (D + 1)) (hi : (i : ℕ) ≠ D) :
    ∑ k : Fin (D + 1),
        ((if k = i then z • (1 : Matrix (Fin n) (Fin n) A) else 0)
          + (if (i : ℕ) + 1 = (k : ℕ) then -(1 : Matrix (Fin n) (Fin n) A) else 0))
        * bInv n D c z E k j = if i = j then 1 else 0 := by
  have hi' : (i : ℕ) < D := lt_of_ne_last i hi
  have step1 : ∀ k : Fin (D + 1),
      ((if k = i then z • (1 : Matrix (Fin n) (Fin n) A) else 0)
          + (if (i : ℕ) + 1 = (k : ℕ) then -(1 : Matrix (Fin n) (Fin n) A) else 0))
        * bInv n D c z E k j
      = (if k = i then z • bInv n D c z E k j else 0)
        + (if k = isucc i hi' then -(bInv n D c z E k j) else 0) := by
    intro k
    rw [add_mul]
    congr 1
    · by_cases h : k = i
      · rw [if_pos h, if_pos h, smul_mul_assoc, one_mul]
      · rw [if_neg h, if_neg h, zero_mul]
    · by_cases h : (i : ℕ) + 1 = (k : ℕ)
      · have hk : k = isucc i hi' := Fin.ext (by rw [isucc_val, h])
        rw [if_pos h, if_pos hk, neg_mul, one_mul]
      · rw [if_neg h, if_neg (fun hh => h (by rw [hh, isucc_val])), zero_mul]
  rw [Finset.sum_congr rfl fun k _ => step1 k, Finset.sum_add_distrib]
  have h1 : (∑ k : Fin (D + 1), (if k = i then z • bInv n D c z E k j else 0))
      = z • bInv n D c z E i j := by
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
  have h2 : (∑ k : Fin (D + 1), (if k = isucc i hi' then -(bInv n D c z E k j) else 0))
      = -(bInv n D c z E (isucc i hi') j) := by
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  rw [h1, h2]
  have hXi : bInv n D c z E i j = (z ^ (i : ℕ)) • (E * wde n D c z j)
      - (if (j : ℕ) < (i : ℕ) then (z ^ ((i : ℕ) - 1 - (j : ℕ))) •
          (1 : Matrix (Fin n) (Fin n) A) else 0) := rfl
  have hXs : bInv n D c z E (isucc i hi') j = (z ^ ((i : ℕ) + 1)) • (E * wde n D c z j)
      - (if (j : ℕ) < (i : ℕ) + 1 then (z ^ ((i : ℕ) - (j : ℕ))) •
          (1 : Matrix (Fin n) (Fin n) A) else 0) := by
    rw [bInv, isucc_val]
    have hexp : ((i : ℕ) + 1) - 1 - (j : ℕ) = (i : ℕ) - (j : ℕ) := by omega
    rw [hexp]
  rw [hXi, hXs, smul_sub]
  have hzY : z • ((z ^ (i : ℕ)) • (E * wde n D c z j))
      = (z ^ ((i : ℕ) + 1)) • (E * wde n D c z j) := by
    rw [smul_smul, pow_succ']
  have hzC : z • (if (j : ℕ) < (i : ℕ) then (z ^ ((i : ℕ) - 1 - (j : ℕ))) •
        (1 : Matrix (Fin n) (Fin n) A) else 0)
      = (if (j : ℕ) < (i : ℕ) then (z ^ ((i : ℕ) - (j : ℕ))) •
        (1 : Matrix (Fin n) (Fin n) A) else 0) := by
    by_cases h : (j : ℕ) < (i : ℕ)
    · have hexp : (i : ℕ) - 1 - (j : ℕ) + 1 = (i : ℕ) - (j : ℕ) := by omega
      rw [if_pos h, if_pos h, smul_smul, ← pow_succ' z ((i : ℕ) - 1 - (j : ℕ)), hexp]
    · rw [if_neg h, if_neg h, smul_zero]
  rw [hzY, hzC, sub_neg_sub_combine]
  by_cases hij : i = j
  · subst hij
    have hD : (if (i : ℕ) < (i : ℕ) + 1 then (z ^ ((i : ℕ) - (i : ℕ))) •
          (1 : Matrix (Fin n) (Fin n) A) else 0) = 1 := by
      rw [if_pos (by omega), Nat.sub_self, pow_zero, one_smul]
    have hC : (if (i : ℕ) < (i : ℕ) then (z ^ ((i : ℕ) - (i : ℕ))) •
          (1 : Matrix (Fin n) (Fin n) A) else 0) = 0 := by
      rw [if_neg (by omega)]
    rw [hD, hC, sub_zero, if_pos rfl]
  · rcases lt_or_gt_of_ne (fun hh => hij (Fin.ext hh)) with h | h
    · -- `i < j` : both indicators vanish
      have hD : (if (j : ℕ) < (i : ℕ) + 1 then (z ^ ((i : ℕ) - (j : ℕ))) •
            (1 : Matrix (Fin n) (Fin n) A) else 0) = 0 := if_neg (by omega)
      have hC : (if (j : ℕ) < (i : ℕ) then (z ^ ((i : ℕ) - (j : ℕ))) •
            (1 : Matrix (Fin n) (Fin n) A) else 0) = 0 := if_neg (by omega)
      rw [hD, hC, sub_self, if_neg hij]
    · -- `j < i` : both indicators hold, with the same exponent
      have hD : (if (j : ℕ) < (i : ℕ) + 1 then (z ^ ((i : ℕ) - (j : ℕ))) •
            (1 : Matrix (Fin n) (Fin n) A) else 0)
          = (z ^ ((i : ℕ) - (j : ℕ))) • (1 : Matrix (Fin n) (Fin n) A) := if_pos (by omega)
      have hC : (if (j : ℕ) < (i : ℕ) then (z ^ ((i : ℕ) - (j : ℕ))) •
            (1 : Matrix (Fin n) (Fin n) A) else 0)
          = (z ^ ((i : ℕ) - (j : ℕ))) • (1 : Matrix (Fin n) (Fin n) A) := if_pos h
      rw [hD, hC, sub_self, if_neg hij]

/-- **The block identity.** -/
lemma bB_mul_bInv (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ)
    {E : Matrix (Fin n) (Fin n) A} (hE : wQ n D c z * E = 1) (i j : Fin (D + 1)) :
    ∑ k : Fin (D + 1), (z • (bA n D i k) + bB n D c i k) * bInv n D c z E k j
      = if i = j then 1 else 0 := by
  by_cases hi : (i : ℕ) = D
  · have hrow : ∀ k : Fin (D + 1), z • (bA n D i k) + bB n D c i k = c k := by
      intro k
      rw [bA_apply_last n D i k hi, bB_apply_last n D c i k hi, smul_zero, zero_add]
    rw [Finset.sum_congr rfl fun k _ => by rw [hrow k]]
    rw [sum_c_mul_bInv n D c z hE j]
    have hil : i = Fin.last D := Fin.ext (by rw [Fin.val_last]; exact hi)
    subst hil
    by_cases hj : (j : ℕ) = D
    · rw [if_pos hj, if_pos (Fin.ext (by rw [Fin.val_last]; exact hj.symm))]
    · rw [if_neg hj, if_neg (fun hh => hj (by rw [← hh, Fin.val_last]))]
  · have hi' : (i : ℕ) < D := lt_of_ne_last i hi
    have hrow : ∀ k : Fin (D + 1), z • (bA n D i k) + bB n D c i k
        = (if k = i then z • (1 : Matrix (Fin n) (Fin n) A) else 0)
          + (if (i : ℕ) + 1 = (k : ℕ) then -(1 : Matrix (Fin n) (Fin n) A) else 0) := by
      intro k
      rw [bA_apply_not_last n D i k hi, bB_apply_not_last n D c i k hi, smul_ite_one]
    rw [Finset.sum_congr rfl fun k _ => by rw [hrow k]]
    exact sum_row_mul_bInv n D c z E i j hi

/-- **The W pencil times its explicit inverse.** -/
theorem wBlk_mul_wInv (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ)
    {E : Matrix (Fin n) (Fin n) A} (hE : wQ n D c z * E = 1) :
    (z • wBA n D + wBB n D c) * wInv n D c z E = 1 := by
  ext p q
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  change blkOf ((z • wBA n D + wBB n D c) * wInv n D c z E) i j a b =
    (1 : Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) A) (i, a) (j, b)
  rw [blkOf_mul]
  simp only [blkOf_add, blkOf_smul, blkOf_wBA, blkOf_wBB, blkOf_wInv]
  rw [bB_mul_bInv n D c z hE i j]
  by_cases hij : i = j <;> by_cases hab : a = b <;>
    simp_all [Matrix.one_apply, Matrix.zero_apply, Prod.ext_iff]

/-- **`Ring.inverse` of the W pencil.**  If the polynomial matrix `wQ n D c z` is a unit, then
so is the pencil, and its `Ring.inverse` is `wInv` with `E = Ring.inverse (wQ n D c z)`. -/
theorem wInv_eq_ringInverse (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ)
    (hQ : IsUnit (wQ n D c z)) :
    Ring.inverse (z • wBA n D + wBB n D c) = wInv n D c z (Ring.inverse (wQ n D c z)) := by
  have hQE : wQ n D c z * Ring.inverse (wQ n D c z) = 1 := Ring.mul_inverse_cancel _ hQ
  have hmul := wBlk_mul_wInv n D c z hQE
  have hdet : (z • wBA n D + wBB n D c).det *
      (wInv n D c z (Ring.inverse (wQ n D c z))).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  have hunit : IsUnit (z • wBA n D + wBB n D c) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact ⟨⟨_, _, hdet, by rw [mul_comm, hdet]⟩, rfl⟩
  have hspec : (↑(IsUnit.unit hunit) : Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) A)
      = z • wBA n D + wBB n D c := IsUnit.unit_spec hunit
  have hinv : (↑((IsUnit.unit hunit)⁻¹) : Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) A)
      = wInv n D c z (Ring.inverse (wQ n D c z)) := by
    calc (↑((IsUnit.unit hunit)⁻¹) : Matrix _ _ A)
        = ↑((IsUnit.unit hunit)⁻¹) * 1 := (mul_one _).symm
      _ = ↑((IsUnit.unit hunit)⁻¹) *
            (↑(IsUnit.unit hunit) * wInv n D c z (Ring.inverse (wQ n D c z))) := by
            rw [hspec, hmul]
      _ = (↑((IsUnit.unit hunit)⁻¹) * ↑(IsUnit.unit hunit)) *
            wInv n D c z (Ring.inverse (wQ n D c z)) := by rw [mul_assoc]
      _ = 1 * wInv n D c z (Ring.inverse (wQ n D c z)) := by rw [Units.inv_mul]
      _ = wInv n D c z (Ring.inverse (wQ n D c z)) := one_mul _
  rw [← hspec, Ring.inverse_unit, hinv]

end

end Work.Idx
