import Mathlib
import Submission.Work.Mostow.geomFiniteThickThinDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.poAux

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix


noncomputable section

variable {n : ℕ}

/-- `pmSign n` is the sign pattern of `pmOneMat`. -/
def pmSign (n : ℕ) : Fin n ⊕ Fin 1 → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

@[simp] lemma pmSign_inl (n : ℕ) (i : Fin n) : pmSign n (Sum.inl i) = 1 := rfl
@[simp] lemma pmSign_inr (n : ℕ) (i : Fin 1) : pmSign n (Sum.inr i) = -1 := rfl

lemma abs_pmSign (n : ℕ) (i : Fin n ⊕ Fin 1) : |pmSign n i| = 1 := by
  rcases i with i | i <;> simp

lemma pmOneMat_eq_diagonal :
    (pmOneMat : MatrixSum (Fin n) (Fin 1) ℝ) = Matrix.diagonal (pmSign n) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rw [pmOneMat, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply, Matrix.one_apply]
    simp [pmSign]
  · rw [pmOneMat, Matrix.fromBlocks_apply₁₂, Matrix.diagonal_apply]
    simp [pmSign, Sum.inl_ne_inr]
  · rw [pmOneMat, Matrix.fromBlocks_apply₂₁, Matrix.diagonal_apply]
    simp [pmSign, Sum.inr_ne_inl]
  · rw [pmOneMat, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, pmSign_inr]
    have h : (Sum.inr i : Fin n ⊕ Fin 1) = Sum.inr j := by simp [Subsingleton.elim i j]
    rw [if_pos h]
    simp [Matrix.neg_apply, Subsingleton.elim i j]

/-- The size `n+1` of matrices in `O(n,1)`, as a real number. -/
def msz (n : ℕ) : ℝ := (n : ℝ) + 1

lemma one_le_msz (n : ℕ) : 1 ≤ msz n := by
  have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  simp only [msz]; linarith

lemma msz_nonneg (n : ℕ) : 0 ≤ msz n := le_trans zero_le_one (one_le_msz n)

lemma card_sum_fin (n : ℕ) : Fintype.card (Fin n ⊕ Fin 1) = n + 1 := by simp [Fintype.card_sum]

lemma sum_const_sum (n : ℕ) (c : ℝ) : (∑ _k : Fin n ⊕ Fin 1, c) = msz n * c := by
  rw [Finset.sum_const, Finset.card_univ, card_sum_fin, nsmul_eq_mul]
  simp [msz]

/-- The `(i,j)` entry of the identity matrix of `O(n,1)`. -/
def dE (n : ℕ) (i j : Fin n ⊕ Fin 1) : ℝ := (1 : MatrixSum (Fin n) (Fin 1) ℝ) i j

lemma dE_apply (i j : Fin n ⊕ Fin 1) : dE n i j = if i = j then (1 : ℝ) else 0 := by
  rw [dE, show (1 : MatrixSum (Fin n) (Fin 1) ℝ)
      = (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) from rfl]
  exact Matrix.one_apply

@[simp] lemma dE_self (i : Fin n ⊕ Fin 1) : dE n i i = 1 := by rw [dE_apply, if_pos rfl]

lemma dE_ne {i j : Fin n ⊕ Fin 1} (h : i ≠ j) : dE n i j = 0 := by rw [dE_apply, if_neg h]

lemma abs_dE_le (i j : Fin n ⊕ Fin 1) : |dE n i j| ≤ 1 := by
  rw [dE_apply]; split <;> simp

lemma dE_nonneg (i j : Fin n ⊕ Fin 1) : 0 ≤ dE n i j := by
  rw [dE_apply]; split <;> norm_num

lemma abs_dE_comm (i j : Fin n ⊕ Fin 1) : |dE n i j| = |dE n j i| := by
  rw [dE_apply, dE_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

lemma sub_one_entry (A : O1 n) (i j : Fin n ⊕ Fin 1) :
    (mat A - 1) i j = mat A i j - dE n i j := by
  rw [Matrix.sub_apply]
  rfl

lemma one_entry_eq_dE (i j : Fin n ⊕ Fin 1) :
    (1 : MatrixSum (Fin n) (Fin 1) ℝ) i j = dE n i j := by
  rw [show (1 : MatrixSum (Fin n) (Fin 1) ℝ)
      = (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) from rfl]
  rw [Matrix.one_apply, dE_apply]

/-- The identity matrix of `O(n,1)` has entries `dE`. -/
lemma sum_dE_col (j : Fin n ⊕ Fin 1) : (∑ k : Fin n ⊕ Fin 1, dE n k j) = 1 := by
  rw [Finset.sum_eq_single j]
  · rw [dE_self]
  · intro b _ hb; rw [dE_ne hb]
  · intro h'; exact absurd (Finset.mem_univ j) h'

lemma sum_abs_dE_col (j : Fin n ⊕ Fin 1) : (∑ k : Fin n ⊕ Fin 1, |dE n k j|) = 1 := by
  rw [← sum_dE_col (n := n) j]
  exact Finset.sum_congr rfl fun k _ => abs_of_nonneg (dE_nonneg (n := n) k j)

lemma mat_one_entry (i j : Fin n ⊕ Fin 1) : mat (1 : O1 n) i j = dE n i j := by
  rw [show mat (1 : O1 n) = (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) from rfl]
  rw [Matrix.one_apply, dE_apply]

/-- `Near1 A q`: every entry of `A` is within `q` of the identity matrix. -/
def Near1 (A : O1 n) (q : ℝ) : Prop :=
  ∀ i j : Fin n ⊕ Fin 1, |mat A i j - dE n i j| ≤ q

lemma Near1.nonneg {A : O1 n} {q : ℝ} (h : Near1 A q) : 0 ≤ q :=
  le_trans (abs_nonneg _) (h (Sum.inr 0) (Sum.inr 0))

lemma near1_one : Near1 (1 : O1 n) 0 := by
  intro i j
  rw [mat_one_entry, sub_self, abs_zero]

/-- Entrywise bound for an element with `Near1 A q`. -/
lemma abs_entry_le {A : O1 n} {q : ℝ} (h : Near1 A q) (i j : Fin n ⊕ Fin 1) :
    |mat A i j| ≤ q + |dE n i j| := by
  have h0 := h i j
  calc |mat A i j| = |(mat A i j - dE n i j) + dE n i j| := by ring_nf
    _ ≤ |mat A i j - dE n i j| + |dE n i j| := abs_add_le _ _
    _ ≤ q + |dE n i j| := by linarith

lemma abs_entry_le' {A : O1 n} {q : ℝ} (h : Near1 A q) (hq : 0 ≤ q) (i j : Fin n ⊕ Fin 1) :
    |mat A i j| ≤ 1 + q := by
  refine le_trans (abs_entry_le h i j) ?_
  have := abs_dE_le (n := n) i j
  linarith

/-! ## Matrix bookkeeping -/

@[simp] lemma mat_one_coe : mat (1 : O1 n) = 1 := rfl

@[simp] lemma mat_mul_coe (A B : O1 n) : mat (A * B) = mat A * mat B := rfl

lemma star_eq_inv (A : O1 n) : (star A : O1 n) = A⁻¹ := rfl

lemma mat_inv_coe (A : O1 n) : mat A⁻¹ = (mat A)⁻¹ := by
  have h : mat A⁻¹ * mat A = 1 := by rw [← mat_mul_coe, inv_mul_cancel, mat_one_coe]
  exact (inv_eq_left_inv h).symm

lemma mat_inv_entry (A : O1 n) (i j : Fin n ⊕ Fin 1) :
    mat A⁻¹ i j = pmSign n i * pmSign n j * mat A j i := by
  rw [← star_eq_inv A, mat_star, pmOneMat_eq_diagonal, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.transpose_apply]
  ring

lemma abs_inv_entry_le {A : O1 n} {q : ℝ} (h : Near1 A q) (i j : Fin n ⊕ Fin 1) :
    |mat A⁻¹ i j| ≤ q + |dE n i j| := by
  rw [mat_inv_entry, abs_mul, abs_mul, abs_pmSign, abs_pmSign, one_mul, one_mul,
    abs_dE_comm]
  exact abs_entry_le h j i

lemma abs_inv_entry_le' {A : O1 n} {q : ℝ} (h : Near1 A q) (hq : 0 ≤ q) (i j : Fin n ⊕ Fin 1) :
    |mat A⁻¹ i j| ≤ 1 + q := by
  refine le_trans (abs_inv_entry_le h i j) ?_
  have := abs_dE_le (n := n) i j
  linarith

lemma abs_inv_matrix_entry_le' {A : O1 n} {q : ℝ} (h : Near1 A q) (hq : 0 ≤ q)
    (i j : Fin n ⊕ Fin 1) : |(mat A)⁻¹ i j| ≤ 1 + q := by
  rw [← mat_inv_coe]
  exact abs_inv_entry_le' h hq i j

/-! ## Products -/

lemma dE_mul_sum {B : MatrixSum (Fin n) (Fin 1) ℝ} (i j : Fin n ⊕ Fin 1) :
    (∑ k, dE n i k * B k j) = B i j := by
  rw [Finset.sum_eq_single i]
  · rw [dE_self, one_mul]
  · intro b _ hb; rw [dE_ne (fun h => hb h.symm), zero_mul]
  · intro h'; exact absurd (Finset.mem_univ i) h'

lemma sum_mul_dE {A : MatrixSum (Fin n) (Fin 1) ℝ} (i j : Fin n ⊕ Fin 1) :
    (∑ k, A i k * dE n k j) = A i j := by
  rw [Finset.sum_eq_single j]
  · rw [dE_self, mul_one]
  · intro b _ hb
    exact mul_eq_zero_of_right _ (dE_ne hb)
  · intro h'; exact absurd (Finset.mem_univ j) h'

lemma sum_dE_dE (i j : Fin n ⊕ Fin 1) : (∑ k, dE n i k * dE n k j) = dE n i j :=
  dE_mul_sum i j

lemma sub_mul_sub_apply {A B : MatrixSum (Fin n) (Fin 1) ℝ} (i j : Fin n ⊕ Fin 1) :
    (∑ k, (A i k - dE n i k) * (B k j - dE n k j))
      = (A * B) i j - A i j - B i j + dE n i j := by
  have h1 : (∑ k, (A i k - dE n i k) * (B k j - dE n k j))
      = ∑ k, ((A i k * B k j - A i k * dE n k j) - dE n i k * B k j
          + dE n i k * dE n k j) :=
    Finset.sum_congr rfl fun k _ => by ring
  have hAB : (A * B) i j = ∑ k, A i k * B k j := Matrix.mul_apply
  have e1 : (∑ k, A i k * B k j) = (A * B) i j := hAB.symm
  have e2 : (∑ k, A i k * dE n k j) = A i j := sum_mul_dE i j
  have e3 : (∑ k, dE n i k * B k j) = B i j := dE_mul_sum i j
  have e4 : (∑ k, dE n i k * dE n k j) = dE n i j := sum_dE_dE i j
  rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    e1, e2, e3, e4]

lemma sub_mul_apply {A B : MatrixSum (Fin n) (Fin 1) ℝ} (i j : Fin n ⊕ Fin 1) :
    (A * B) i j - dE n i j =
      (∑ k, (A i k - dE n i k) * B k j) + (B i j - dE n i j) := by
  have hA : (A * B) i j = ∑ k, A i k * B k j := Matrix.mul_apply
  have hsum : (∑ k, (A i k - dE n i k) * B k j) = (∑ k, A i k * B k j) - B i j := by
    rw [← dE_mul_sum (n := n) (B := B) i j]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [sub_mul]
  rw [hA, hsum]; ring

lemma near1_mul' {A B : O1 n} {a b : ℝ} (hA : Near1 A a) (hB : Near1 B b) :
    Near1 (A * B) (msz n * a * b + a + b) := by
  intro i j
  have ha : 0 ≤ a := hA.nonneg
  have hb : 0 ≤ b := hB.nonneg
  have hsub : mat (A * B) i j - dE n i j =
      (∑ k, (mat A i k - dE n i k) * mat B k j) + (mat B i j - dE n i j) := by
    rw [mat_mul_coe]
    exact sub_mul_apply (n := n) (A := mat A) (B := mat B) i j
  rw [hsub]
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |∑ k, (mat A i k - dE n i k) * mat B k j| ≤ msz n * a * b + a := by
    calc |∑ k, (mat A i k - dE n i k) * mat B k j|
        ≤ ∑ k, |(mat A i k - dE n i k) * mat B k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, a * (b + |dE n k j|) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hA i k) (abs_entry_le hB k j) (abs_nonneg _) ha
      _ = a * (msz n * b + 1) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_const_sum, sum_abs_dE_col]
      _ = msz n * a * b + a := by ring
  have h2 : |mat B i j - dE n i j| ≤ b := hB i j
  linarith [h1, h2]

lemma near1_pow {A : O1 n} {q : ℝ} (hA : Near1 A q) (hq : 0 ≤ q) (j : ℕ) :
    Near1 (A ^ j) ((1 + msz n * q) ^ j - 1) := by
  have hmsz : 1 ≤ msz n := one_le_msz n
  have h1q : 1 ≤ 1 + msz n * q := by nlinarith [msz_nonneg n]
  induction j with
  | zero => simpa using near1_one
  | succ k ih =>
      have hstep := near1_mul' ih hA
      have hP : 0 ≤ (1 + msz n * q) ^ k - 1 := by
        have := one_le_pow₀ h1q (n := k); linarith
      have hle : msz n * ((1 + msz n * q) ^ k - 1) * q + ((1 + msz n * q) ^ k - 1) + q
          ≤ (1 + msz n * q) ^ (k + 1) - 1 := by
        have hq' : (0:ℝ) ≤ q := hq
        have hq'' : 0 ≤ q * (msz n - 1) := mul_nonneg hq' (by linarith)
        have h3 : 0 ≤ (1 + msz n * q) ^ k := le_of_lt (pow_pos (by linarith) k)
        rw [pow_succ]
        nlinarith [hq'', hq', hP, h3, msz_nonneg n, hmsz]
      intro i j
      exact le_trans (hstep i j) hle

/-! ## Commutators -/

lemma abs_sub_comm_mul_le {A B : O1 n} {q : ℝ} (hA : Near1 A q) (hB : Near1 B q)
    (i j : Fin n ⊕ Fin 1) :
    |(mat A * mat B - mat B * mat A) i j| ≤ 2 * (msz n * q * q) := by
  have hq : 0 ≤ q := hA.nonneg
  have key : (mat A * mat B - mat B * mat A) i j =
      (∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)) -
        (∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)) := by
    have p1 := sub_mul_sub_apply (n := n) (A := mat A) (B := mat B) i j
    have p2 := sub_mul_sub_apply (n := n) (A := mat B) (B := mat A) i j
    rw [show (mat A * mat B - mat B * mat A) i j
        = (mat A * mat B) i j - (mat B * mat A) i j from rfl, p1, p2]
    abel
  have b1 : |∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)| ≤ msz n * (q * q) := by
    calc |∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)|
        ≤ ∑ k, |(mat A i k - dE n i k) * (mat B k j - dE n k j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, q * q := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) hq
      _ = msz n * (q * q) := sum_const_sum n _
  have b2 : |∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)| ≤ msz n * (q * q) := by
    calc |∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)|
        ≤ ∑ k, |(mat B i k - dE n i k) * (mat A k j - dE n k j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, q * q := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hB i k) (hA k j) (abs_nonneg _) hq
      _ = msz n * (q * q) := sum_const_sum n _
  have htri : |(∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)) -
      (∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j))|
      ≤ |∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)|
        + |∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)| := by
    calc |(∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)) -
            (∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j))|
        = |(∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)) +
            (-(∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)))| := by ring_nf
      _ ≤ |∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)|
            + |-(∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j))| := abs_add_le _ _
      _ = |∑ k, (mat A i k - dE n i k) * (mat B k j - dE n k j)|
            + |∑ k, (mat B i k - dE n i k) * (mat A k j - dE n k j)| := by rw [abs_neg]
  rw [key]
  linarith [htri, b1, b2]

/-- The commutator defect is quadratic in the defect of the factors. -/
lemma near1_commutator {A B : O1 n} {q : ℝ} (hA : Near1 A q) (hB : Near1 B q)
    (hq : q ≤ 1 / 4) :
    Near1 (A * B * A⁻¹ * B⁻¹) (8 * (msz n) ^ 3 * q ^ 2) := by
  have hq0 : 0 ≤ q := hA.nonneg
  have hAA : mat A * (mat A)⁻¹ = 1 := by
    have h : mat A * mat A⁻¹ = 1 := by rw [← mat_mul_coe, mul_inv_cancel, mat_one_coe]
    rwa [mat_inv_coe] at h
  have hBB : mat B * (mat B)⁻¹ = 1 := by
    have h : mat B * mat B⁻¹ = 1 := by rw [← mat_mul_coe, mul_inv_cancel, mat_one_coe]
    rwa [mat_inv_coe] at h
  have hBA : (mat B * mat A) * ((mat A)⁻¹ * (mat B)⁻¹) = 1 := by
    rw [mul_assoc, ← mul_assoc (mat A), hAA, one_mul, hBB]
  have hmat : mat (A * B * A⁻¹ * B⁻¹) - 1 = (mat A * mat B - mat B * mat A) *
      ((mat A)⁻¹ * (mat B)⁻¹) := by
    have hL : mat (A * B * A⁻¹ * B⁻¹) = (mat A * mat B) * ((mat A)⁻¹ * (mat B)⁻¹) := by
      rw [mat_mul_coe, mat_mul_coe, mat_mul_coe, mat_inv_coe, mat_inv_coe, mul_assoc]
    rw [hL]
    have hexp : (mat A * mat B) * ((mat A)⁻¹ * (mat B)⁻¹) - 1
        = (mat A * mat B) * ((mat A)⁻¹ * (mat B)⁻¹)
          - (mat B * mat A) * ((mat A)⁻¹ * (mat B)⁻¹) := by rw [hBA]
    rw [hexp, ← sub_mul]
  intro i j
  have hkey : mat (A * B * A⁻¹ * B⁻¹) i j - dE n i j =
      ((mat A * mat B - mat B * mat A) * ((mat A)⁻¹ * (mat B)⁻¹)) i j := by
    have hD : (mat (A * B * A⁻¹ * B⁻¹) - 1) i j
        = mat (A * B * A⁻¹ * B⁻¹) i j - dE n i j := by
      exact sub_one_entry (A * B * A⁻¹ * B⁻¹) i j
    have hentry : (mat (A * B * A⁻¹ * B⁻¹) - 1) i j
        = ((mat A * mat B - mat B * mat A) * ((mat A)⁻¹ * (mat B)⁻¹)) i j := by
      rw [hmat]
    rw [← hD, hentry]
  rw [hkey, Matrix.mul_apply]
  have hfactor : ∀ k, |((mat A)⁻¹ * (mat B)⁻¹) k j| ≤ msz n * (1 + q) * (1 + q) := by
    intro k
    calc |((mat A)⁻¹ * (mat B)⁻¹) k j| ≤ ∑ l, |(mat A)⁻¹ k l * (mat B)⁻¹ l j| := by
          rw [Matrix.mul_apply]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l, (1 + q) * (1 + q) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [abs_mul]
          exact mul_le_mul (abs_inv_matrix_entry_le' hA hq0 k l) (abs_inv_matrix_entry_le' hB hq0 l j)
            (abs_nonneg _) (by linarith)
      _ = msz n * ((1 + q) * (1 + q)) := sum_const_sum n _
      _ = msz n * (1 + q) * (1 + q) := by ring
  calc |∑ k, (mat A * mat B - mat B * mat A) i k * ((mat A)⁻¹ * (mat B)⁻¹) k j|
      ≤ ∑ k, |(mat A * mat B - mat B * mat A) i k| * |((mat A)⁻¹ * (mat B)⁻¹) k j| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
        exact Finset.sum_congr rfl fun k _ => abs_mul _ _
    _ ≤ ∑ k, (2 * (msz n * q * q)) * (msz n * (1 + q) * (1 + q)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hnn : (0:ℝ) ≤ 2 * (msz n * q * q) :=
          mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (msz_nonneg n) hq0) hq0)
        exact mul_le_mul (abs_sub_comm_mul_le hA hB i k) (hfactor k) (abs_nonneg _) hnn
    _ = msz n * ((2 * (msz n * q * q)) * (msz n * (1 + q) * (1 + q))) := sum_const_sum n _
    _ = 2 * (msz n) ^ 3 * (q * q) * ((1 + q) * (1 + q)) := by ring
    _ ≤ 2 * (msz n) ^ 3 * (q * q) * 4 := by
        have h1 : (0:ℝ) ≤ msz n := msz_nonneg n
        have h2 : (1 + q) * (1 + q) ≤ 4 := by nlinarith
        have h3 : (0:ℝ) ≤ 2 * (msz n) ^ 3 * (q * q) :=
          mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h1 3)) (mul_nonneg hq0 hq0)
        exact mul_le_mul_of_nonneg_left h2 h3
    _ = 8 * (msz n) ^ 3 * q ^ 2 := by ring

/-- `NearId q g`: the element `g` of `PO n 1` has a matrix representative within `q` of `1`. -/
def NearId (q : ℝ) (g : PO n 1) : Prop :=
  ∃ A : O1 n, (A : PO n 1) = g ∧ Near1 A q



lemma NearId.mono {q q' : ℝ} (h : q ≤ q') {g : PO n 1} (hg : NearId q g) : NearId q' g := by
  obtain ⟨A, hA, h1⟩ := hg
  exact ⟨A, hA, fun i j => le_trans (h1 i j) h⟩

/-- Conjugation preserves discreteness of subgroups of `PO n 1`. -/
lemma isDiscrete_map_conj {Γ : Subgroup (PO n 1)} (hdisc : IsDiscrete (SetLike.coe Γ))
    (h : PO n 1) : IsDiscrete (SetLike.coe (Γ.map (MulAut.conj h⁻¹).toMonoidHom)) := by
  haveI : DiscreteTopology ↥Γ := isDiscrete_iff_discreteTopology.mp hdisc
  set φ : PO n 1 ≃* PO n 1 := MulAut.conj h⁻¹ with hφ
  have hmem : ∀ y ∈ Γ.map φ.toMonoidHom, φ.symm y ∈ Γ := by
    intro y hy
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy
    rw [show φ.symm y = φ.symm (φ.toMonoidHom g) from by rw [hgy]]
    rw [show φ.symm (φ.toMonoidHom g) = g from MulEquiv.symm_apply_apply φ g]
    exact hg
  have hcont : Continuous (fun y : ↥(Γ.map φ.toMonoidHom) =>
      (⟨φ.symm (y : PO n 1), hmem y y.2⟩ : ↥Γ)) := by
    refine Continuous.subtype_mk ?_ _
    have h1 : Continuous (fun x : PO n 1 => φ.symm x) := by
      have heq : (fun x : PO n 1 => φ.symm x) = fun x => h * x * h⁻¹ := by
        funext x
        have h2 : φ.symm x = (MulAut.conj h) x := by
          rw [hφ]
          show (MulAut.conj h⁻¹).symm x = _
          simp [MulAut.conj_apply]
        rw [h2, MulAut.conj_apply]
      rw [heq]
      fun_prop
    exact h1.comp continuous_subtype_val
  have hinj : Function.Injective (fun y : ↥(Γ.map φ.toMonoidHom) =>
      (⟨φ.symm (y : PO n 1), hmem y y.2⟩ : ↥Γ)) := by
    intro a b hab
    have h2 : φ.symm (a : PO n 1) = φ.symm (b : PO n 1) := Subtype.ext_iff.mp hab
    exact Subtype.ext (φ.symm.injective h2)
  exact isDiscrete_iff_discreteTopology.mpr (DiscreteTopology.of_continuous_injective hcont hinj)

/-- Assembly of `margulisPair` from the two delegated pieces: the uniform bounded-power
pigeonhole `nearId_conj_power_uniform` and the near-identity Margulis core
`nearId_pair_commuting`. -/
theorem margulisPair_of_pieces (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hpig : ∀ η : ℝ, 0 < η → ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧ 0 < N ∧
      ∀ (u : E n), ∃ h : PO n 1, h • (0 : E n) = u ∧
        ∀ (g : PO n 1), hdist u (g • u) < δ →
          ∃ j : ℕ, 0 < j ∧ j ≤ N ∧ NearId η (h⁻¹ * g ^ j * h))
    (hend : ∃ q : ℝ, 0 < q ∧ q ≤ 1 / 1000 ∧
      ∀ (Γ : Subgroup (PO n 1)), IsDiscrete (SetLike.coe Γ) →
        ∀ γ δ : Γ, NearId q (γ : PO n 1) → NearId q (δ : PO n 1) →
          ∃ m k : ℕ, 0 < m ∧ 0 < k ∧
            (γ : PO n 1) ^ m * (δ : PO n 1) ^ k = (δ : PO n 1) ^ k * (γ : PO n 1) ^ m) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (Γ : Subgroup (PO n 1)), IsDiscrete (SetLike.coe Γ) → ∀ u : E n,
      ∀ γ δ : Γ, hdist u ((γ : PO n 1) • u) < ε → hdist u ((δ : PO n 1) • u) < ε →
        ∃ m k : ℕ, 0 < m ∧ 0 < k ∧
          (γ : PO n 1) ^ m * (δ : PO n 1) ^ k = (δ : PO n 1) ^ k * (γ : PO n 1) ^ m := by
  obtain ⟨q, hq, hq1, hend⟩ := hend
  obtain ⟨N, δ, hδ, hN, hpig⟩ := hpig q hq
  refine ⟨δ, hδ, ?_⟩
  intro Γ hdisc u γ δ' hγ hδ'
  obtain ⟨h, -, hunif⟩ := hpig u
  obtain ⟨j, hj, -, hnearγ⟩ := hunif (γ : PO n 1) hγ
  obtain ⟨k, hk, -, hneard⟩ := hunif (δ' : PO n 1) hδ'
  set φ : PO n 1 ≃* PO n 1 := MulAut.conj h⁻¹ with hφ
  have hdisc' : IsDiscrete (SetLike.coe (Γ.map φ.toMonoidHom)) := isDiscrete_map_conj hdisc h
  set U : PO n 1 := h⁻¹ * (γ : PO n 1) ^ j * h with hU
  set V : PO n 1 := h⁻¹ * (δ' : PO n 1) ^ k * h with hV
  have hmemU : U ∈ Γ.map φ.toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨(γ : PO n 1) ^ j, Γ.pow_mem γ.2 j, ?_⟩
    rw [hU]
    show φ ((γ : PO n 1) ^ j) = h⁻¹ * (γ : PO n 1) ^ j * h
    rw [hφ, MulAut.conj_apply]
    simp
  have hmemV : V ∈ Γ.map φ.toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨(δ' : PO n 1) ^ k, Γ.pow_mem δ'.2 k, ?_⟩
    rw [hV]
    show φ ((δ' : PO n 1) ^ k) = h⁻¹ * (δ' : PO n 1) ^ k * h
    rw [hφ, MulAut.conj_apply]
    simp
  have hnearU : NearId q U := hnearγ
  have hnearV : NearId q V := hneard
  obtain ⟨m, k', hm, hk', hcomm⟩ := hend (Γ.map φ.toMonoidHom) hdisc'
    ⟨U, hmemU⟩ ⟨V, hmemV⟩ hnearU hnearV
  have hcomm' : U ^ m * V ^ k' = V ^ k' * U ^ m := hcomm
  have conjpow : ∀ (x : PO n 1) (t : ℕ), (h⁻¹ * x * h) ^ t = h⁻¹ * x ^ t * h := by
    intro x t
    have hx : h⁻¹ * x * h = (MulAut.conj h⁻¹) x := by
      rw [MulAut.conj_apply]; simp
    rw [hx, ← map_pow, MulAut.conj_apply]
    simp
  have key : ((γ : PO n 1) ^ j) ^ m * ((δ' : PO n 1) ^ k) ^ k' =
      ((δ' : PO n 1) ^ k) ^ k' * ((γ : PO n 1) ^ j) ^ m := by
    have h2 : h⁻¹ * ((γ : PO n 1) ^ j) ^ m * h * (h⁻¹ * ((δ' : PO n 1) ^ k) ^ k' * h) =
        h⁻¹ * ((δ' : PO n 1) ^ k) ^ k' * h * (h⁻¹ * ((γ : PO n 1) ^ j) ^ m * h) := by
      simpa only [hU, hV, conjpow] using hcomm'
    have h4 := congrArg (fun t => h * t * h⁻¹) h2
    have h5 : h * (h⁻¹ * ((γ : PO n 1) ^ j) ^ m * h * (h⁻¹ * ((δ' : PO n 1) ^ k) ^ k' * h)) * h⁻¹
        = ((γ : PO n 1) ^ j) ^ m * ((δ' : PO n 1) ^ k) ^ k' := by group
    have h6 : h * (h⁻¹ * ((δ' : PO n 1) ^ k) ^ k' * h * (h⁻¹ * ((γ : PO n 1) ^ j) ^ m * h)) * h⁻¹
        = ((δ' : PO n 1) ^ k) ^ k' * ((γ : PO n 1) ^ j) ^ m := by group
    rw [h5, h6] at h4
    exact h4
  refine ⟨j * m, k * k', Nat.mul_pos hj hm, Nat.mul_pos hk hk', ?_⟩
  rw [pow_mul, pow_mul]
  exact key



end

end Work.Mostow
