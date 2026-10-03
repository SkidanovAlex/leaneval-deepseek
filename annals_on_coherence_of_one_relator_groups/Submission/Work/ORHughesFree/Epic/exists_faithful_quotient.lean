import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.Faithful.rankZeroIdeal_mem_iff
import Submission.Work.ORHughesFree.RankAPI.rk_add_le
import Submission.Work.ORHughesFree.RankAPI.rk_submatrix

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.ORHughesFree.Epic

open Matrix

variable {R : Type*} [Ring R]

namespace QuotientRank

/-! ## Rank of matrices whose entries have rank zero

If `D` is a matrix all of whose `1 × 1` entries have rank zero, then `rk D = 0`.  The proof
writes `D` as the sum of its "single entry" matrices `singleEntry (D i j) i j`, uses that
`rk (A + B) ≤ rk A + rk B` and that a single-entry matrix is a product of a column, a `1 × 1`
matrix and a row, so that its rank is bounded by the rank of the `1 × 1` entry. -/

/-- `matMul M N` is the matrix product of `M` and `N`.  It is defined explicitly (rather than
through the `*` notation) so that the relevant computations happen at the matrix-product
instance; this keeps the elaboration independent of the `Matrix`-valued `HMul` instances that
appear in the presence of C⋆-algebra type copies. -/
def matMul {l : Type*} {m : Type*} {n : Type*} {α : Type*} [Fintype m] [Mul α]
    [AddCommMonoid α] (M : Matrix l m α) (N : Matrix m n α) : Matrix l n α :=
  fun i k => ∑ j, M i j * N j k

theorem matMul_apply {l m n α : Type*} [Fintype m] [Mul α] [AddCommMonoid α]
    (M : Matrix l m α) (N : Matrix m n α) (i : l) (k : n) :
    matMul M N i k = ∑ j, M i j * N j k := rfl

theorem matMul_map {α β : Type*} [Semiring α] [Semiring β] (f : α →+* β) {l m n : ℕ}
    (M : Matrix (Fin l) (Fin m) α) (N : Matrix (Fin m) (Fin n) α) :
    (matMul M N).map f = matMul (M.map f) (N.map f) := by
  ext i k
  simp only [matMul, Matrix.map_apply]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => map_mul f (M i j) (N j k))

theorem rk_matMul_le_left (rk : SylvesterRank R) {l m k : ℕ}
    (M : Matrix (Fin l) (Fin m) R) (N : Matrix (Fin m) (Fin k) R) :
    rk.rk l k (matMul M N) ≤ rk.rk l m M := rk.rk_mul_le_left M N

theorem rk_matMul_le_right (rk : SylvesterRank R) {l m k : ℕ}
    (M : Matrix (Fin l) (Fin m) R) (N : Matrix (Fin m) (Fin k) R) :
    rk.rk l k (matMul M N) ≤ rk.rk m k N := rk.rk_mul_le_right M N

/-- The `n × 1` column vector with a `1` in position `i`. -/
def colVec {n : ℕ} (i : Fin n) : Matrix (Fin n) (Fin 1) R :=
  fun i' _ => if i' = i then (1 : R) else 0

/-- The `1 × m` row vector with a `1` in position `j`. -/
def rowVec {m : ℕ} (j : Fin m) : Matrix (Fin 1) (Fin m) R :=
  fun _ j' => if j' = j then (1 : R) else 0

/-- The `n × m` matrix with `a` in position `(i, j)` and `0` elsewhere. -/
def singleEntry {n m : ℕ} (a : R) (i : Fin n) (j : Fin m) : Matrix (Fin n) (Fin m) R :=
  fun i' j' => if i' = i ∧ j' = j then a else 0

theorem oneByOne_mul (a b : R) : oneByOne (a * b) = matMul (oneByOne a) (oneByOne b) := by
  ext i j; simp [oneByOne, matMul]

/-- A single-entry matrix is a product of a column vector, the `1 × 1` matrix of its entry and
a row vector. -/
theorem singleEntry_eq (a : R) {n m : ℕ} (i : Fin n) (j : Fin m) :
    matMul (matMul (colVec i) (oneByOne a)) (rowVec j) = singleEntry a i j := by
  ext i' j'
  simp only [matMul, Fin.sum_univ_one, colVec, rowVec, oneByOne, singleEntry]
  by_cases hi : i' = i <;> by_cases hj : j' = j <;> simp [hi, hj]

/-- The rank of a single-entry matrix is at most the rank of its entry. -/
theorem rk_singleEntry_le (rk : SylvesterRank R) (a : R) {n m : ℕ} (i : Fin n)
    (j : Fin m) : rk.rk n m (singleEntry a i j) ≤ rk.rk 1 1 (oneByOne a) := by
  rw [← singleEntry_eq]
  calc rk.rk n m (matMul (matMul (colVec i) (oneByOne a)) (rowVec j))
      ≤ rk.rk n 1 (matMul (colVec i) (oneByOne a)) := rk_matMul_le_left rk _ _
    _ ≤ rk.rk 1 1 (oneByOne a) := rk_matMul_le_right rk (colVec i) (oneByOne a)

/-- Subadditivity of the rank over a finite sum of matrices. -/
theorem rk_sum_le (rk : SylvesterRank R) {ι : Type*} (s : Finset ι) {n m : ℕ}
    (f : ι → Matrix (Fin n) (Fin m) R) :
    rk.rk n m (∑ i ∈ s, f i) ≤ ∑ i ∈ s, rk.rk n m (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [rk.rk_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc rk.rk n m (f a + ∑ i ∈ s, f i)
          ≤ rk.rk n m (f a) + rk.rk n m (∑ i ∈ s, f i) := RankAPI.rk_add_le rk _ _
        _ ≤ rk.rk n m (f a) + ∑ i ∈ s, rk.rk n m (f i) := add_le_add le_rfl ih

/-- Every matrix is the sum of its single-entry matrices. -/
theorem singleEntry_sum {n m : ℕ} (D : Matrix (Fin n) (Fin m) R) :
    D = ∑ p : Fin n × Fin m, singleEntry (D p.1 p.2) p.1 p.2 := by
  ext i j
  have h : (∑ p : Fin n × Fin m, singleEntry (D p.1 p.2) p.1 p.2) i j
      = ∑ p : Fin n × Fin m, singleEntry (D p.1 p.2) p.1 p.2 i j := by
    simp only [Matrix.sum_apply]
  rw [h, Finset.sum_eq_single (i, j)]
  · simp [singleEntry]
  · rintro ⟨p1, p2⟩ _ hp
    simp only [singleEntry]
    rw [if_neg]
    intro hcon
    exact hp (Prod.ext hcon.1.symm hcon.2.symm)
  · intro h; exact absurd (Finset.mem_univ (i, j)) h

/-- A matrix all of whose entries have rank zero has rank zero. -/
theorem rk_eq_zero_of_entries_rankZero (rk : SylvesterRank R) {n m : ℕ}
    (D : Matrix (Fin n) (Fin m) R) (h : ∀ i j, rk.rk 1 1 (oneByOne (D i j)) = 0) :
    rk.rk n m D = 0 := by
  rw [singleEntry_sum (D := D)]
  refine le_antisymm ?_ (rk.rk_nonneg n m _)
  calc rk.rk n m (∑ p : Fin n × Fin m, singleEntry (D p.1 p.2) p.1 p.2)
      ≤ ∑ p : Fin n × Fin m, rk.rk n m (singleEntry (D p.1 p.2) p.1 p.2) :=
        rk_sum_le rk _ _
    _ ≤ ∑ p : Fin n × Fin m, rk.rk 1 1 (oneByOne (D p.1 p.2)) :=
        Finset.sum_le_sum (fun p _ => rk_singleEntry_le rk (D p.1 p.2) p.1 p.2)
    _ = 0 := by simp [h]

end QuotientRank

open QuotientRank

/-- The ideal of elements of rank zero with respect to a Sylvester rank function `rk`. -/
def rkZeroIdeal (rk : SylvesterRank R) : Ideal R :=
  Ideal.span {b : R | rk.rk 1 1 (oneByOne b) = 0}

/-- Membership in `rkZeroIdeal rk` is exactly vanishing of the rank of the `1 × 1` matrix. -/
theorem mem_rkZeroIdeal (rk : SylvesterRank R) (a : R) :
    a ∈ rkZeroIdeal rk ↔ rk.rk 1 1 (oneByOne a) = 0 :=
  Faithful.rankZeroIdeal_mem_iff rk a

/-- A matrix all of whose entries lie in `rkZeroIdeal rk` has rank zero. -/
theorem rk_eq_zero_of_entries_mem (rk : SylvesterRank R) {n m : ℕ}
    (D : Matrix (Fin n) (Fin m) R) (h : ∀ i j, D i j ∈ rkZeroIdeal rk) :
    rk.rk n m D = 0 :=
  QuotientRank.rk_eq_zero_of_entries_rankZero rk D
    (fun i j => (mem_rkZeroIdeal rk (D i j)).mp (h i j))

/-- The rank function is constant on matrices that agree modulo the rank-zero ideal. -/
theorem rk_eq_of_map_mk_eq (rk : SylvesterRank R) [(rkZeroIdeal rk).IsTwoSided] {n m : ℕ}
    (A B : Matrix (Fin n) (Fin m) R)
    (h : A.map (Ideal.Quotient.mk (rkZeroIdeal rk)) = B.map (Ideal.Quotient.mk (rkZeroIdeal rk))) :
    rk.rk n m A = rk.rk n m B := by
  have hpoint : ∀ i j, Ideal.Quotient.mk (rkZeroIdeal rk) (A i j)
      = Ideal.Quotient.mk (rkZeroIdeal rk) (B i j) := by
    intro i j
    simpa using congr_fun (congr_fun h i) j
  have hAB : ∀ i j, (A - B) i j ∈ rkZeroIdeal rk := by
    intro i j
    rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub, hpoint i j, sub_self]
  have hBA : ∀ i j, (B - A) i j ∈ rkZeroIdeal rk := by
    intro i j
    rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub, hpoint i j, sub_self]
  have h1 : rk.rk n m A ≤ rk.rk n m B := by
    have hdecomp : A = B + (A - B) := by abel
    rw [hdecomp]
    calc rk.rk n m (B + (A - B)) ≤ rk.rk n m B + rk.rk n m (A - B) := RankAPI.rk_add_le rk _ _
      _ = rk.rk n m B + 0 := by rw [rk_eq_zero_of_entries_mem rk _ hAB]
      _ = rk.rk n m B := by ring
  have h2 : rk.rk n m B ≤ rk.rk n m A := by
    have hdecomp : B = A + (B - A) := by abel
    rw [hdecomp]
    calc rk.rk n m (A + (B - A)) ≤ rk.rk n m A + rk.rk n m (B - A) := RankAPI.rk_add_le rk _ _
      _ = rk.rk n m A + 0 := by rw [rk_eq_zero_of_entries_mem rk _ hBA]
      _ = rk.rk n m A := by ring
  exact le_antisymm h1 h2

/-- The rank-zero ideal is two-sided. -/
theorem rkZeroIdeal_isTwoSided (rk : SylvesterRank R) : (rkZeroIdeal rk).IsTwoSided := by
  refine Ideal.IsTwoSided.mk (fun {a} b ha => ?_)
  rw [mem_rkZeroIdeal] at ha ⊢
  rw [QuotientRank.oneByOne_mul]
  refine le_antisymm ?_ (rk.rk_nonneg 1 1 _)
  calc rk.rk 1 1 (QuotientRank.matMul (oneByOne a) (oneByOne b))
      ≤ rk.rk 1 1 (oneByOne a) := QuotientRank.rk_matMul_le_left rk _ _
    _ = 0 := ha

/-- A chosen representative of an element of a quotient ring. -/
noncomputable def elLift (I : Ideal R) [I.IsTwoSided] (x : R ⧸ I) : R :=
  Classical.choose (Ideal.Quotient.mk_surjective x)

theorem mk_elLift (I : Ideal R) [I.IsTwoSided] (x : R ⧸ I) :
    Ideal.Quotient.mk I (elLift I x) = x :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective x)

/-- A chosen lift of a matrix over a quotient ring. -/
noncomputable def matLift (I : Ideal R) [I.IsTwoSided] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (R ⧸ I)) : Matrix (Fin n) (Fin m) R :=
  A.map (elLift I)

theorem matLift_map (I : Ideal R) [I.IsTwoSided] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (R ⧸ I)) :
    (matLift I A).map (Ideal.Quotient.mk I) = A := by
  rw [matLift, Matrix.map_map]
  ext i j
  exact mk_elLift I (A i j)

/-- The Sylvester rank function induced on the quotient by the rank-zero ideal
([JZLA20, §2.4]). -/
noncomputable def quotientRank (rk : SylvesterRank R) [(rkZeroIdeal rk).IsTwoSided] :
    SylvesterRank (R ⧸ rkZeroIdeal rk) where
  rk n m A := rk.rk n m (matLift (rkZeroIdeal rk) A)
  rk_nonneg n m A := rk.rk_nonneg n m _
  rk_zero n m := by
    have h : (matLift (rkZeroIdeal rk)
          (0 : Matrix (Fin n) (Fin m) (R ⧸ rkZeroIdeal rk))).map (Ideal.Quotient.mk (rkZeroIdeal rk))
        = (0 : Matrix (Fin n) (Fin m) R).map (Ideal.Quotient.mk (rkZeroIdeal rk)) := by
      rw [matLift_map]; simp
    exact (rk_eq_of_map_mk_eq rk _ _ h).trans (rk.rk_zero n m)
  rk_one := by
    have h : (matLift (rkZeroIdeal rk)
          (1 : Matrix (Fin 1) (Fin 1) (R ⧸ rkZeroIdeal rk))).map (Ideal.Quotient.mk (rkZeroIdeal rk))
        = (1 : Matrix (Fin 1) (Fin 1) R).map (Ideal.Quotient.mk (rkZeroIdeal rk)) := by
      rw [matLift_map]
      ext i j
      fin_cases i; fin_cases j
      simp
    exact (rk_eq_of_map_mk_eq rk _ _ h).trans rk.rk_one
  rk_mul_le_left := by
    intro n m k A B
    have h : (matLift (rkZeroIdeal rk) (A * B)).map (Ideal.Quotient.mk (rkZeroIdeal rk))
        = (QuotientRank.matMul (matLift (rkZeroIdeal rk) A)
            (matLift (rkZeroIdeal rk) B)).map (Ideal.Quotient.mk (rkZeroIdeal rk)) := by
      rw [matLift_map, QuotientRank.matMul_map, matLift_map, matLift_map]
      rfl
    exact (rk_eq_of_map_mk_eq rk _ _ h).trans_le (QuotientRank.rk_matMul_le_left rk _ _)
  rk_mul_le_right := by
    intro n m k A B
    have h : (matLift (rkZeroIdeal rk) (A * B)).map (Ideal.Quotient.mk (rkZeroIdeal rk))
        = (QuotientRank.matMul (matLift (rkZeroIdeal rk) A)
            (matLift (rkZeroIdeal rk) B)).map (Ideal.Quotient.mk (rkZeroIdeal rk)) := by
      rw [matLift_map, QuotientRank.matMul_map, matLift_map, matLift_map]
      rfl
    exact (rk_eq_of_map_mk_eq rk _ _ h).trans_le (QuotientRank.rk_matMul_le_right rk _ _)
  rk_blockDiag := by
    intro n m p q A B
    have h : (matLift (rkZeroIdeal rk) (blockDiagFin A B)).map (Ideal.Quotient.mk (rkZeroIdeal rk))
        = (blockDiagFin (matLift (rkZeroIdeal rk) A) (matLift (rkZeroIdeal rk) B)).map
            (Ideal.Quotient.mk (rkZeroIdeal rk)) := by
      rw [matLift_map, blockDiagFin_map, matLift_map, matLift_map]
    exact (rk_eq_of_map_mk_eq rk _ _ h).trans (rk.rk_blockDiag _ _)
  rk_blockUpper := by
    intro n m p q A B C
    have h : (matLift (rkZeroIdeal rk) (blockUpperFin A B C)).map (Ideal.Quotient.mk (rkZeroIdeal rk))
        = (blockUpperFin (matLift (rkZeroIdeal rk) A) (matLift (rkZeroIdeal rk) B)
            (matLift (rkZeroIdeal rk) C)).map (Ideal.Quotient.mk (rkZeroIdeal rk)) := by
      rw [matLift_map, blockUpperFin_map, matLift_map, matLift_map, matLift_map]
    exact le_trans (rk.rk_blockUpper _ _ _)
      (le_of_eq (rk_eq_of_map_mk_eq rk _ _ h).symm)

/-- **[JZLA20, §2.4]** A Sylvester matrix rank function `rk` on a ring `R` induces a faithful
Sylvester rank function on the quotient `R ⧸ I` by the rank-zero ideal
`I = {a : R | rk (1 × 1 matrix a) = 0}`; the induced rank of the reduction of a matrix is the
rank of the matrix itself. -/
theorem exists_faithful_quotient {R : Type*} [Ring R] (rk : SylvesterRank R) :
    ∃ (I : Ideal R) (_ : I.IsTwoSided) (rk' : SylvesterRank (R ⧸ I)),
      (∀ a : R, a ∈ I ↔ rk.rk 1 1 (oneByOne a) = 0) ∧ rk'.IsFaithful ∧
      (∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
        rk'.rk n m (A.map (Ideal.Quotient.mk I)) = rk.rk n m A) := by
  classical
  have hI : (rkZeroIdeal rk).IsTwoSided := rkZeroIdeal_isTwoSided rk
  haveI : (rkZeroIdeal rk).IsTwoSided := hI
  refine ⟨rkZeroIdeal rk, hI, quotientRank rk, ?_, ?_, ?_⟩
  · intro a
    exact mem_rkZeroIdeal rk a
  · intro a ha
    have hmat : matLift (rkZeroIdeal rk) (oneByOne a)
        = oneByOne (elLift (rkZeroIdeal rk) a) := by
      ext i j; simp [matLift, oneByOne]
    have ha' : rk.rk 1 1 (oneByOne (elLift (rkZeroIdeal rk) a)) = 0 := by
      have ha'' : rk.rk 1 1 (matLift (rkZeroIdeal rk) (oneByOne a)) = 0 := ha
      rwa [hmat] at ha''
    have hmem : elLift (rkZeroIdeal rk) a ∈ rkZeroIdeal rk := (mem_rkZeroIdeal rk _).mpr ha'
    have hzero : Ideal.Quotient.mk (rkZeroIdeal rk) (elLift (rkZeroIdeal rk) a) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    rwa [mk_elLift] at hzero
  · intro n m A
    have h : (matLift (rkZeroIdeal rk) (A.map (Ideal.Quotient.mk (rkZeroIdeal rk)))).map
        (Ideal.Quotient.mk (rkZeroIdeal rk)) = A.map (Ideal.Quotient.mk (rkZeroIdeal rk)) :=
      matLift_map (rkZeroIdeal rk) _
    exact rk_eq_of_map_mk_eq rk _ _ h

end Work.ORHughesFree.Epic
