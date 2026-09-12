import Mathlib
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Submission.ZRowBasis

noncomputable section
open scoped BigOperators
open Matrix

/-!
# Adapted ℤ-basis for the flag spanned by an independent family of integer vectors

`Submission.MinkFlagBasis.exists_flag_basis` (used by `Submission.MinkGlue`):

For `u : Fin d → Fin d → ℤ` with `LinearIndependent ℤ u`, there is a family
`e : Fin d → Fin d → ℤ` whose columns form a (unimodular) ℤ-basis of the
standard lattice (i.e. the determinant of the matrix `M i j := e j i` is `±1`),
such that for every `k : Fin (d+1)` the real span of the first `k` columns of `e`
equals the real span of the first `k` columns of `u`:

    span_ℝ {e j ↦ ℝ-vector : j.val < k} = span_ℝ {u j ↦ ℝ-vector : j.val < k}

This is the classical statement that every flag of rational subspaces
(`W_k := span_ℝ (u_0, …, u_{k-1})`) admits a ℤ-basis of `ℤ^d` adapted to it.

(Note: the index `j : Fin k.val` is cast into `Fin d` along the order-preserving
inclusion `Fin.castLE`, i.e. we take the columns with `j.val < k.val`.)
-/

namespace Submission.MinkFlagBasis

open Submission.ZRowBasis

/-- Real vector given by column `j` of the integer family `x : Fin d → Fin d → ℤ`. -/
def colReal (d : ℕ) (x : Fin d → Fin d → ℤ) (j : Fin d) : Fin d → ℝ :=
  fun i : Fin d => ((x j i : ℤ) : ℝ)

/-- The set of the first `k` columns (with `k ≤ d`) of the integer family `x`,
viewed as vectors in `Fin d → ℝ`. -/
def firstCols (d k : ℕ) (hk : k ≤ d) (x : Fin d → Fin d → ℤ) : Set (Fin d → ℝ) :=
  Set.range (fun j : Fin k => fun i : Fin d => ((x (Fin.castLE hk j) i : ℤ) : ℝ))


lemma fin_eq_zero_or_succ {n : ℕ} (i : Fin (n+1)) : i = 0 ∨ ∃ j : Fin n, i = Fin.succ j := by
  by_cases h : (i : ℕ) = 0
  · left; apply Fin.ext; simpa using h
  · right
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h
    refine ⟨⟨k, ?_⟩, ?_⟩
    · have : k < n := by
        have := i.isLt
        rw [hk] at this
        omega
      exact this
    · apply Fin.ext
      simp [hk]

def padHead {n : ℕ} {R : Type*} [Zero R] [One R]
    (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  Fin.cons (Fin.cons 1 (fun _ : Fin n => 0)) (fun r : Fin n => Fin.cons 0 (M r))

@[simp] lemma padHead_00 {n : ℕ} {R : Type*} [Zero R] [One R] (M : Matrix (Fin n) (Fin n) R) :
    padHead M 0 0 = 1 := by simp [padHead]
@[simp] lemma padHead_0s {n : ℕ} {R : Type*} [Zero R] [One R] (M : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    padHead M 0 (Fin.succ j) = 0 := by simp [padHead]
@[simp] lemma padHead_s0 {n : ℕ} {R : Type*} [Zero R] [One R] (M : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    padHead M (Fin.succ i) 0 = 0 := by simp [padHead]
@[simp] lemma padHead_ss {n : ℕ} {R : Type*} [Zero R] [One R] (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    padHead M (Fin.succ i) (Fin.succ j) = M i j := by simp [padHead]

def padEnd {n : ℕ} {R : Type*} [Zero R] [One R]
    (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  Fin.snoc (fun i : Fin n => Fin.snoc (M i) 0) (Fin.snoc (fun _ : Fin n => 0) 1)

@[simp] lemma padEnd_cc {n : ℕ} {R : Type*} [Zero R] [One R] (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    padEnd M (Fin.castSucc i) (Fin.castSucc j) = M i j := by simp [padEnd]
@[simp] lemma padEnd_cl {n : ℕ} {R : Type*} [Zero R] [One R] (M : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    padEnd M (Fin.castSucc i) (Fin.last n) = 0 := by simp [padEnd]
@[simp] lemma padEnd_lc {n : ℕ} {R : Type*} [Zero R] [One R] (M : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    padEnd M (Fin.last n) (Fin.castSucc j) = 0 := by simp [padEnd]
@[simp] lemma padEnd_ll {n : ℕ} {R : Type*} [Zero R] [One R] (M : Matrix (Fin n) (Fin n) R) :
    padEnd M (Fin.last n) (Fin.last n) = 1 := by simp [padEnd]

lemma det_padHead {n : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R) :
    (padHead M).det = M.det := by
  rw [Matrix.det_succ_column_zero]
  rw [Fin.sum_univ_succ]
  simp
  have hsub : (padHead M).submatrix Fin.succ Fin.succ = M := by
    ext r c; simp [Matrix.submatrix]
  rw [hsub]

lemma det_padEnd {n : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R) :
    (padEnd M).det = M.det := by
  rw [Matrix.det_succ_row (padEnd M) (Fin.last n)]
  rw [Fin.sum_univ_castSucc]
  simp
  have hsub : (padEnd M).submatrix Fin.castSucc Fin.castSucc = M := by
    ext r c; simp [Matrix.submatrix]
  rw [hsub]

lemma padHead_mul_ss {q : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin q) (Fin q) R)
    (T : Matrix (Fin (q+1)) (Fin (q+1)) R) (r c : Fin q) :
    (padHead M * T) (Fin.succ r) (Fin.succ c) = (M * T.submatrix Fin.succ Fin.succ) r c := by
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ]
  simp [padHead]

lemma padHead_mul_s0 {q : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin q) (Fin q) R)
    (T : Matrix (Fin (q+1)) (Fin (q+1)) R) (r : Fin q) :
    (padHead M * T) (Fin.succ r) 0 =
      (M *ᵥ (fun k : Fin q => T (Fin.succ k) 0)) r := by
  rw [Matrix.mul_apply, Matrix.mulVec, Fin.sum_univ_succ]
  simp [padHead, dotProduct]

lemma det_col0_zero {q : ℕ} {R : Type*} [CommRing R] (T : Matrix (Fin (q+1)) (Fin (q+1)) R)
    (h : ∀ r0 : Fin q, T (Fin.succ r0) 0 = 0) :
    T.det = T 0 0 * (T.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h]

lemma det_ne_zero_of_col_ne_zero {q : ℕ} (A : Matrix (Fin (q+1)) (Fin (q+1)) ℤ)
    (hA : A.det ≠ 0) : A.col 0 ≠ 0 := by
  intro hc
  apply hA
  exact Matrix.det_eq_zero_of_column_eq_zero (j := 0) (h := fun i => congr_fun hc i)

lemma upperTri_of_padHead {q : ℕ} (V0 : Matrix (Fin q) (Fin q) ℤ)
    (T : Matrix (Fin (q+1)) (Fin (q+1)) ℤ)
    (hT0 : ∀ r0 : Fin q, T (Fin.succ r0) 0 = 0)
    (hV0 : (V0 * T.submatrix Fin.succ Fin.succ).IsUpperTriangular) :
    (padHead V0 * T).IsUpperTriangular := by
  rw [Matrix.IsUpperTriangular]
  intro i j hij
  rcases fin_eq_zero_or_succ i with hi0 | ⟨r0, hi0⟩
  · exfalso
    subst i
    exact (not_lt_of_ge (Fin.zero_le j)) hij
  · subst i
    rcases fin_eq_zero_or_succ j with hj0 | ⟨c0, hj0⟩
    · subst j
      rw [padHead_mul_s0 V0 T r0]
      have hzero : (fun k : Fin q => T (Fin.succ k) 0) = 0 := by
        funext k; exact hT0 k
      simp [hzero]
    · subst j
      have hgt : c0 < r0 := Fin.succ_lt_succ_iff.mp hij
      rw [padHead_mul_ss V0 T r0 c0]
      exact hV0 hgt

theorem triangInt (n : ℕ) : ∀ A : Matrix (Fin n) (Fin n) ℤ, A.det ≠ 0 →
    ∃ V : Matrix (Fin n) (Fin n) ℤ,
      V.det = 1 ∧ (V * A).IsUpperTriangular := by
  induction n with
  | zero =>
      intro A hA
      refine ⟨1, ?_, ?_⟩
      · simp
      · rw [Matrix.IsUpperTriangular]
        intro i j hij
        exact False.elim (Fin.elim0 i)
  | succ q ih =>
      intro A hA
      have hc0 : A.col 0 ≠ 0 := det_ne_zero_of_col_ne_zero A hA
      obtain ⟨Qc, hQcdet, hQ0, hQrest⟩ := clearVec q (A.col 0) hc0
      let T : Matrix (Fin (q+1)) (Fin (q+1)) ℤ := Qc * A
      have hT0 : ∀ r0 : Fin q, T (Fin.succ r0) 0 = 0 := by
        intro r0
        dsimp [T]
        rw [Matrix.mul_apply]
        change (Qc *ᵥ (A.col 0)) (Fin.succ r0) = 0
        exact hQrest (Fin.succ r0) (Fin.succ_ne_zero r0)
      let B : Matrix (Fin q) (Fin q) ℤ := T.submatrix Fin.succ Fin.succ
      have hdetT : T.det ≠ 0 := by
        dsimp [T]
        rw [Matrix.det_mul, hQcdet, one_mul]
        exact hA
      have hdetB : B.det ≠ 0 := by
        have hmul : T 0 0 * B.det ≠ 0 := by
          rw [← det_col0_zero T hT0]
          exact hdetT
        exact (mul_ne_zero_iff.mp (by simpa [B] using hmul)).2
      obtain ⟨V0, hV0det, hV0tri⟩ := ih B hdetB
      let V : Matrix (Fin (q+1)) (Fin (q+1)) ℤ := padHead V0 * Qc
      refine ⟨V, ?_, ?_⟩
      · dsimp [V]
        rw [Matrix.det_mul, det_padHead, hV0det, hQcdet]
        simp
      · dsimp [V]
        rw [Matrix.mul_assoc]
        apply upperTri_of_padHead V0 T hT0
        simpa [B] using hV0tri

-- det A ≠ 0 from LinearIndependent
lemma det_ne_zero_of_linearIndependent (d : ℕ) (u : Fin d → Fin d → ℤ)
    (hu : LinearIndependent ℤ u) :
    (Matrix.of (fun i j : Fin d => u j i)).det ≠ 0 := by
  let A : Matrix (Fin d) (Fin d) ℤ := Matrix.of (fun i j => u j i)
  have hcol : LinearIndependent ℤ A.col := by
    convert hu using 1
    · ext j i; rfl
  have hinj : Function.Injective A.mulVec := (Matrix.mulVec_injective_iff).mpr hcol
  have hA : A.det ≠ 0 := by
    intro hd
    rw [← Matrix.exists_mulVec_eq_zero_iff] at hd
    rcases hd with ⟨v, hv0, hv⟩
    exact hv0 (hinj (by simpa using hv))
  simpa [A] using hA

lemma triang_decomp {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (hA : A.det ≠ 0) :
    ∃ E R : Matrix (Fin d) (Fin d) ℤ,
      E.det = 1 ∧ R.IsUpperTriangular ∧ R.det ≠ 0 ∧ A = E * R := by
  obtain ⟨V, hVdet, hVtri⟩ := triangInt d A hA
  let E : Matrix (Fin d) (Fin d) ℤ := V⁻¹
  let R : Matrix (Fin d) (Fin d) ℤ := V * A
  refine ⟨E, R, ?_, ?_, ?_, ?_⟩
  · dsimp [E]
    rw [Matrix.det_nonsing_inv, hVdet]
    simp
  · simpa [R] using hVtri
  · dsimp [R]
    rw [Matrix.det_mul, hVdet, one_mul]
    exact hA
  · dsimp [E, R]
    have hVunit : IsUnit V.det := by rw [hVdet]; exact isUnit_one
    calc
      A = (V⁻¹ * V) * A := by rw [Matrix.nonsing_inv_mul V hVunit, Matrix.one_mul]
      _ = V⁻¹ * (V * A) := by rw [Matrix.mul_assoc]

lemma upperTri_inv {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ)
    (hT : T.IsUpperTriangular) (hdet : T.det ≠ 0) : T⁻¹.IsUpperTriangular := by
  have huT : IsUnit T := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdet
  letI : Invertible T := huT.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular (M := T) (b := id) hT

lemma upperTri_map_int {d : ℕ} (R : Matrix (Fin d) (Fin d) ℤ) (hR : R.IsUpperTriangular) :
    (R.map (fun z : ℤ => (z : ℝ))).IsUpperTriangular := by
  rw [Matrix.IsUpperTriangular]
  intro i j hij
  change ((R i j : ℤ) : ℝ) = 0
  exact_mod_cast hR hij

lemma det_map_int {d : ℕ} (R : Matrix (Fin d) (Fin d) ℤ) :
    (R.map (fun z : ℤ => (z : ℝ))).det = (R.det : ℝ) := by
  simpa using ((Int.castRingHom ℝ).map_det R).symm

def firstColsReal (d k : ℕ) (hk : k ≤ d) (X : Matrix (Fin d) (Fin d) ℝ) : Set (Fin d → ℝ) :=
  Set.range (fun j : Fin k => fun i : Fin d => X i (Fin.castLE hk j))

lemma col_eq_sum {d : ℕ} (X Y T : Matrix (Fin d) (Fin d) ℝ) (h : X = Y * T) (cc : Fin d) :
    (fun i : Fin d => X i cc) = ∑ j : Fin d, (T j cc) • Y.col j := by
  funext r
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Matrix.col]
  rw [h, Matrix.mul_apply]
  congr 1 with j
  simp [Matrix.transpose_apply, mul_comm]

lemma colSpan_le {d k : ℕ} (hk : k ≤ d) {X Y T : Matrix (Fin d) (Fin d) ℝ}
    (h : X = Y * T) (hT : ∀ ⦃i j : Fin d⦄, j < i → T i j = 0) :
    Submodule.span ℝ (firstColsReal d k hk X) ≤ Submodule.span ℝ (firstColsReal d k hk Y) := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨c, rfl⟩
  let cc : Fin d := Fin.castLE hk c
  let S : Set (Fin d → ℝ) := firstColsReal d k hk Y
  have hmem : (fun i : Fin d => X i cc) ∈ Submodule.span ℝ S := by
    rw [col_eq_sum X Y T h cc]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    by_cases hlt : cc < j
    · have hT0 : T j cc = 0 := hT hlt
      rw [hT0]
      simp
    · have hjv : j.val < k := by
        have h1 : j.val ≤ cc.val := le_of_not_gt hlt
        exact lt_of_le_of_lt h1 c.isLt
      let j' : Fin k := ⟨j.val, hjv⟩
      have hjcast : Fin.castLE hk j' = j := by
        apply Fin.ext
        exact Fin.val_castLE hk j'
      have hcol : Y.col j ∈ S := by
        refine ⟨j', ?_⟩
        funext i
        dsimp [Matrix.col, S, firstColsReal]
        rw [hjcast]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hcol)
  simpa [cc, S] using hmem

-- main assembly
theorem main_assem {d : ℕ} (u : Fin d → Fin d → ℤ) (hu : LinearIndependent ℤ u) :
    ∃ e : Fin d → Fin d → ℤ,
      (Matrix.det (Matrix.of (fun i j : Fin d => (e j i : ℤ))) = 1 ∨
        Matrix.det (Matrix.of (fun i j : Fin d => (e j i : ℤ))) = -1) ∧
      (∀ k : Fin (d + 1),
        Submodule.span ℝ (firstColsReal d k.val (Nat.le_of_lt_succ k.2)
          ((Matrix.of (fun i j : Fin d => (e j i : ℤ))).map (fun z : ℤ => (z : ℝ)))) =
        Submodule.span ℝ (firstColsReal d k.val (Nat.le_of_lt_succ k.2)
          ((Matrix.of (fun i j : Fin d => (u j i : ℤ))).map (fun z : ℤ => (z : ℝ))))) := by
  let A : Matrix (Fin d) (Fin d) ℤ := Matrix.of (fun i j : Fin d => u j i)
  have hA : A.det ≠ 0 := det_ne_zero_of_linearIndependent d u hu
  obtain ⟨E, R, hEdet, hRtri, hRdet, hAR⟩ := triang_decomp A hA
  let e : Fin d → Fin d → ℤ := fun j i => E i j
  refine ⟨e, ?det, ?spans⟩
  · left
    have hE : (Matrix.of (fun i j : Fin d => (e j i : ℤ))) = E := by
      dsimp [e]
      ext i j
      rfl
    simpa [hE] using hEdet
  · intro k
    let hk : k.val ≤ d := Nat.le_of_lt_succ k.2
    let X : Matrix (Fin d) (Fin d) ℝ := A.map (fun z : ℤ => (z : ℝ))
    let Y : Matrix (Fin d) (Fin d) ℝ := E.map (fun z : ℤ => (z : ℝ))
    let U : Matrix (Fin d) (Fin d) ℝ := R.map (fun z : ℤ => (z : ℝ))
    have hXY : X = Y * U := by
      dsimp [X, Y, U]
      rw [← Matrix.map_mul_intCast]
      exact congrArg (fun M : Matrix (Fin d) (Fin d) ℤ => M.map (fun z : ℤ => (z : ℝ))) hAR
    have hUtri : U.IsUpperTriangular := by
      dsimp [U]
      exact upperTri_map_int R hRtri
    have hUdet : U.det ≠ 0 := by
      dsimp [U]
      rw [det_map_int]
      exact_mod_cast hRdet
    have hUinv : U⁻¹.IsUpperTriangular := upperTri_inv U hUtri hUdet
    have hYX : Y = X * U⁻¹ := by
      have hUisUnit : IsUnit U.det := isUnit_iff_ne_zero.mpr hUdet
      calc
        Y = Y * (U * U⁻¹) := by rw [Matrix.mul_nonsing_inv U hUisUnit]; simp
        _ = (Y * U) * U⁻¹ := by rw [Matrix.mul_assoc]
        _ = X * U⁻¹ := by rw [← hXY]
    change Submodule.span ℝ (firstColsReal d k.val hk
          ((Matrix.of (fun i j : Fin d => (e j i : ℤ))).map (fun z : ℤ => (z : ℝ)))) =
          Submodule.span ℝ (firstColsReal d k.val hk
          ((Matrix.of (fun i j : Fin d => (u j i : ℤ))).map (fun z : ℤ => (z : ℝ))))
    have hYdef : (Matrix.of (fun i j : Fin d => (e j i : ℤ))).map (fun z : ℤ => (z : ℝ)) = Y := by
      dsimp [Y, e]
      ext i j; rfl
    have hXdef : (Matrix.of (fun i j : Fin d => (u j i : ℤ))).map (fun z : ℤ => (z : ℝ)) = X := by
      dsimp [X, A]
    rw [hYdef, hXdef]
    apply le_antisymm
    · exact colSpan_le hk (h := hYX) (hT := fun ⦃i j⦄ h => by
        simpa using hUinv (i := i) (j := j) h)
    · exact colSpan_le hk (h := hXY) (hT := fun ⦃i j⦄ h => by
        simpa using hUtri (i := i) (j := j) h)


/-- The set of the first `k` columns of an integer family coincides with the first `k`
columns of its real-valued matrix. -/
lemma firstCols_eq_real {d k : ℕ} (hk : k ≤ d) (x : Fin d → Fin d → ℤ) :
    firstCols d k hk x =
      firstColsReal d k hk ((Matrix.of (fun i j : Fin d => (x j i : ℤ))).map (fun z : ℤ => (z : ℝ))) := by
  rfl

/-- A rational flag spanned by the columns of an independent integer family admits an
adapted unimodular ℤ-basis. -/
theorem exists_flag_basis {d : ℕ} (u : Fin d → Fin d → ℤ)
    (hu : LinearIndependent ℤ u) :
    ∃ e : Fin d → Fin d → ℤ,
      (Matrix.det (Matrix.of (fun i j : Fin d => (e j i : ℤ))) = 1 ∨
        Matrix.det (Matrix.of (fun i j : Fin d => (e j i : ℤ))) = -1) ∧
      (∀ k : Fin (d + 1),
        Submodule.span ℝ (firstCols d k.val (Nat.le_of_lt_succ k.2) e) =
          Submodule.span ℝ (firstCols d k.val (Nat.le_of_lt_succ k.2) u)) := by
  obtain ⟨e, hdet, hspans⟩ := main_assem u hu
  refine ⟨e, hdet, ?_⟩
  intro k
  specialize hspans k
  rw [firstCols_eq_real (Nat.le_of_lt_succ k.2) e]
  rw [firstCols_eq_real (Nat.le_of_lt_succ k.2) u]
  exact hspans

end Submission.MinkFlagBasis
