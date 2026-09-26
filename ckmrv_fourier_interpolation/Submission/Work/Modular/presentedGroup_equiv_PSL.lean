import Mathlib
import Submission.Work.Modular.GroupAlgebra

namespace Work.Modular

open Work.Modular
open scoped MonoidAlgebra MatrixGroups

namespace PresGroup

/-!
## Part 1: the matrix computation for alternating words
-/

def Sm : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]
def N1 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]
def N2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, 1]
def RM : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 1]
def Nonneg (A : Matrix (Fin 2) (Fin 2) ℤ) : Prop := ∀ i j, 0 ≤ A i j
def isR (a : Fin 3) : Bool := decide (a ≠ 0)
def letterMat (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℤ :=
  if a = 0 then Sm else if a = 1 then RM else RM * RM
def matWord (l : List (Fin 3)) : Matrix (Fin 2) (Fin 2) ℤ := (l.map letterMat).prod
def tOf : List (Fin 3) → ℕ
  | [] => 0
  | a :: _ => if isR a then 1 else 0
def dOf (l : List (Fin 3)) : ℕ := if l.getLast? = some 0 then 1 else 0
/-- An alternating list of letters. -/
def Alternating : List (Fin 3) → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => isR a ≠ isR b ∧ Alternating (b :: l)
/-- The inductive invariant of the block argument. -/
def Good (l : List (Fin 3)) (N : Matrix (Fin 2) (Fin 2) ℤ) (δ : ℕ) : Prop :=
  Nonneg N ∧ N.det = 1 ∧ δ = dOf l ∧
    (matWord l = Sm ^ tOf l * N * Sm ^ δ ∨ matWord l = -(Sm ^ tOf l * N * Sm ^ δ)) ∧
    (tOf l = 1 → N ≠ 1) ∧ (l ≠ [] → tOf l = 0 → δ = 0 → N ≠ 1)

theorem Sm_sq_neg : Sm * Sm = (-1 : Matrix (Fin 2) (Fin 2) ℤ) := by decide
theorem RM_eq : RM = Sm * N1 := by decide
theorem RMRM_eq : RM * RM = Sm * N2 := by decide
theorem not_nonneg_Sm : ¬ Nonneg (Sm : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro h; have := h 0 1; simp [Sm] at this
theorem not_nonneg_neg_Sm : ¬ Nonneg (-Sm : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro h; have := h 1 0; simp [Sm] at this
theorem not_nonneg_neg_one : ¬ Nonneg (-1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro h; have := h 0 0; simp at this
theorem nonneg_one : Nonneg (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp
theorem nonneg_N1 : Nonneg N1 := by intro i j; fin_cases i <;> fin_cases j <;> decide
theorem nonneg_N2 : Nonneg N2 := by intro i j; fin_cases i <;> fin_cases j <;> decide
theorem N1_det : N1.det = 1 := by decide
theorem N2_det : N2.det = 1 := by decide
theorem N1_ne_one : N1 ≠ (1 : Matrix (Fin 2) (Fin 2) ℤ) := by decide
theorem N2_ne_one : N2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℤ) := by decide
theorem nonneg_mul {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : Nonneg A) (hB : Nonneg B) :
    Nonneg (A * B) := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  have h1 := hA i 0; have h2 := hA i 1; have h3 := hB 0 j; have h4 := hB 1 j
  nlinarith
theorem det_mul' {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det = 1) (hB : B.det = 1) :
    (A * B).det = 1 := by rw [Matrix.det_mul, hA, hB, one_mul]
theorem two_factor {N P : Matrix (Fin 2) (Fin 2) ℤ} (hN : Nonneg N) (hP : Nonneg P)
    (hNd : N.det = 1) (h : N * P = 1) : N = 1 ∧ P = 1 := by
  have hP' : P = N.adjugate := by
    have h2 : N.adjugate * (N * P) = N.adjugate * 1 := by rw [h]
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, hNd, one_smul, Matrix.one_mul,
      Matrix.mul_one] at h2
    exact h2
  have h10 : N 1 0 = 0 := by
    have hh := hP 1 0
    rw [hP', Matrix.adjugate_fin_two] at hh
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at hh
    have := hN 1 0
    omega
  have h01 : N 0 1 = 0 := by
    have hh := hP 0 1
    rw [hP', Matrix.adjugate_fin_two] at hh
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at hh
    have := hN 0 1
    omega
  have hdet : N 0 0 * N 1 1 = 1 := by
    rw [Matrix.det_fin_two, h01, h10] at hNd
    linarith
  have h00 : N 0 0 = 1 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · have := hN 0 0; omega
  have h11 : N 1 1 = 1 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2
    · have := hN 1 1; omega
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h01, h10]
  · rw [hP', Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h01, h10]

@[simp] theorem matWord_nil : matWord [] = 1 := by simp [matWord]
@[simp] theorem matWord_cons (a : Fin 3) (l : List (Fin 3)) :
    matWord (a :: l) = letterMat a * matWord l := by simp [matWord]
@[simp] theorem tOf_cons (a : Fin 3) (l : List (Fin 3)) : tOf (a :: l) = if isR a then 1 else 0 := rfl
@[simp] theorem dOf_cons_cons (a b : Fin 3) (l : List (Fin 3)) :
    dOf (a :: b :: l) = dOf (b :: l) := by simp [dOf, List.getLast?_cons_cons]
@[simp] theorem letterMat_zero : letterMat 0 = Sm := by decide
@[simp] theorem letterMat_one : letterMat 1 = RM := by decide
@[simp] theorem letterMat_two : letterMat 2 = RM * RM := by decide
@[simp] theorem isR_zero : isR 0 = false := by decide
@[simp] theorem isR_one : isR 1 = true := by decide
@[simp] theorem isR_two : isR 2 = true := by decide
@[simp] theorem Alternating_cons_cons (a b : Fin 3) (l : List (Fin 3)) :
    Alternating (a :: b :: l) ↔ isR a ≠ isR b ∧ Alternating (b :: l) := by simp only [Alternating]
theorem isR_eq_true_of_ne_false {a : Fin 3} (h : isR a ≠ false) : isR a = true := by
  cases h' : isR a <;> simp_all
theorem isR_eq_false_of_ne_true {a : Fin 3} (h : isR a ≠ true) : isR a = false := by
  cases h' : isR a <;> simp_all
theorem isR_of_alt_false {a b : Fin 3} (ha : isR a = false) (h : isR a ≠ isR b) : isR b = true := by
  rw [ha] at h; exact isR_eq_true_of_ne_false h.symm
theorem isR_of_alt_true {a b : Fin 3} (ha : isR a = true) (h : isR a ≠ isR b) : isR b = false := by
  rw [ha] at h; exact isR_eq_false_of_ne_true h.symm
theorem eq_zero_of_isR_false {a : Fin 3} (h : isR a = false) : a = 0 := by
  revert h; fin_cases a <;> decide

theorem hA (N : Matrix (Fin 2) (Fin 2) ℤ) (δ : ℕ) : Sm * (Sm * N * Sm ^ δ) = -(N * Sm ^ δ) := by
  rw [mul_assoc Sm N (Sm ^ δ), ← mul_assoc Sm Sm (N * Sm ^ δ), Sm_sq_neg, neg_one_mul]
theorem hB (N : Matrix (Fin 2) (Fin 2) ℤ) (δ : ℕ) : Sm * (-(Sm * N * Sm ^ δ)) = N * Sm ^ δ := by
  rw [mul_neg, hA, neg_neg]
theorem hC (N : Matrix (Fin 2) (Fin 2) ℤ) (δ : ℕ) :
    (Sm * N1) * (N * Sm ^ δ) = Sm * (N1 * N) * Sm ^ δ := by
  rw [mul_assoc Sm N1 (N * Sm ^ δ), ← mul_assoc N1 N (Sm ^ δ), mul_assoc Sm (N1 * N) (Sm ^ δ)]
theorem hD (N : Matrix (Fin 2) (Fin 2) ℤ) (δ : ℕ) :
    (Sm * N1) * (-(N * Sm ^ δ)) = -(Sm * (N1 * N) * Sm ^ δ) := by rw [mul_neg, hC]
theorem hE (N : Matrix (Fin 2) (Fin 2) ℤ) (δ : ℕ) :
    (Sm * N2) * (N * Sm ^ δ) = Sm * (N2 * N) * Sm ^ δ := by
  rw [mul_assoc Sm N2 (N * Sm ^ δ), ← mul_assoc N2 N (Sm ^ δ), mul_assoc Sm (N2 * N) (Sm ^ δ)]
theorem hF (N : Matrix (Fin 2) (Fin 2) ℤ) (δ : ℕ) :
    (Sm * N2) * (-(N * Sm ^ δ)) = -(Sm * (N2 * N) * Sm ^ δ) := by rw [mul_neg, hE]

theorem good_nil : Good ([] : List (Fin 3)) 1 0 := by
  refine ⟨nonneg_one, by decide, by decide, ?_, ?_, ?_⟩
  · left; simp [matWord, tOf, dOf]
  · intro h; simp [tOf] at h
  · intro h; simp at h
theorem good_zero : Good ([0] : List (Fin 3)) 1 1 := by
  refine ⟨nonneg_one, by decide, by decide, ?_, ?_, ?_⟩
  · left; simp [matWord, tOf, dOf, letterMat, isR]
  · intro h; simp [tOf, isR] at h
  · intro _ _ h; norm_num at h
theorem good_one : Good ([1] : List (Fin 3)) N1 0 := by
  refine ⟨nonneg_N1, N1_det, by decide, ?_, ?_, ?_⟩
  · left; simp [matWord, tOf, letterMat, isR, RM_eq]
  · intro _; exact N1_ne_one
  · intro _ h; simp [tOf, isR] at h
theorem good_two : Good ([2] : List (Fin 3)) N2 0 := by
  refine ⟨nonneg_N2, N2_det, by decide, ?_, ?_, ?_⟩
  · left; simp [matWord, tOf, letterMat, isR, RMRM_eq]
  · intro _; exact N2_ne_one
  · intro _ h; simp [tOf, isR] at h

theorem good_step (a b : Fin 3) (l : List (Fin 3)) (hab : isR a ≠ isR b)
    (haltl : Alternating (b :: l)) (N : Matrix (Fin 2) (Fin 2) ℤ) (δ : ℕ)
    (hN : Nonneg N) (hNd : N.det = 1) (hδ : δ = dOf (b :: l))
    (hform : matWord (b :: l) = Sm ^ tOf (b :: l) * N * Sm ^ δ ∨
      matWord (b :: l) = -(Sm ^ tOf (b :: l) * N * Sm ^ δ))
    (hcond1 : tOf (b :: l) = 1 → N ≠ 1)
    (hcond2 : b :: l ≠ [] → tOf (b :: l) = 0 → δ = 0 → N ≠ 1) :
    ∃ N' δ', Good (a :: b :: l) N' δ' := by
  have ha : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  rcases ha with rfl | rfl | rfl
  · -- a = 0
    have hb : isR b = true := isR_of_alt_false (by decide) hab
    have ht : tOf (b :: l) = 1 := by rw [tOf_cons, hb]; rfl
    have hd : δ = dOf ((0 : Fin 3) :: b :: l) := by rw [dOf_cons_cons]; exact hδ
    have ht0 : tOf ((0 : Fin 3) :: b :: l) = 0 := by simp
    have hform' : matWord (b :: l) = Sm * N * Sm ^ δ ∨ matWord (b :: l) = -(Sm * N * Sm ^ δ) := by
      rw [ht] at hform; simpa using hform
    refine ⟨N, δ, hN, hNd, hd, ?_, ?_, ?_⟩
    · rcases hform' with h | h
      · right; rw [matWord_cons, h, letterMat_zero, ht0, pow_zero, one_mul, hA]
      · left; rw [matWord_cons, h, letterMat_zero, ht0, pow_zero, one_mul, hB]
    · intro h; rw [ht0] at h; exact absurd h (by norm_num)
    · intro _ _ h0; exact hcond1 ht
  · -- a = 1
    have hb : isR b = false := isR_of_alt_true (by decide) hab
    have hb0 : b = 0 := eq_zero_of_isR_false hb
    subst hb0
    have ht0 : tOf ((0 : Fin 3) :: l) = 0 := by simp
    have hd : δ = dOf ((1 : Fin 3) :: 0 :: l) := by rw [dOf_cons_cons]; exact hδ
    have ht1 : tOf ((1 : Fin 3) :: 0 :: l) = 1 := by simp
    have hform' : matWord ((0 : Fin 3) :: l) = N * Sm ^ δ ∨
        matWord ((0 : Fin 3) :: l) = -(N * Sm ^ δ) := by
      rw [ht0] at hform; simpa using hform
    refine ⟨N1 * N, δ, nonneg_mul nonneg_N1 hN, det_mul' N1_det hNd, hd, ?_, ?_, ?_⟩
    · rcases hform' with h | h
      · left; rw [matWord_cons, h, letterMat_one, RM_eq, ht1, pow_one, hC]
      · right; rw [matWord_cons, h, letterMat_one, RM_eq, ht1, pow_one, hD]
    · intro _ heq; exact N1_ne_one (two_factor nonneg_N1 hN N1_det heq).1
    · intro _ h; rw [ht1] at h; exact absurd h (by norm_num)
  · -- a = 2
    have hb : isR b = false := isR_of_alt_true (by decide) hab
    have hb0 : b = 0 := eq_zero_of_isR_false hb
    subst hb0
    have ht0 : tOf ((0 : Fin 3) :: l) = 0 := by simp
    have hd : δ = dOf ((2 : Fin 3) :: 0 :: l) := by rw [dOf_cons_cons]; exact hδ
    have ht1 : tOf ((2 : Fin 3) :: 0 :: l) = 1 := by simp
    have hform' : matWord ((0 : Fin 3) :: l) = N * Sm ^ δ ∨
        matWord ((0 : Fin 3) :: l) = -(N * Sm ^ δ) := by
      rw [ht0] at hform; simpa using hform
    refine ⟨N2 * N, δ, nonneg_mul nonneg_N2 hN, det_mul' N2_det hNd, hd, ?_, ?_, ?_⟩
    · rcases hform' with h | h
      · left; rw [matWord_cons, h, letterMat_two, RMRM_eq, ht1, pow_one, hE]
      · right; rw [matWord_cons, h, letterMat_two, RMRM_eq, ht1, pow_one, hF]
    · intro _ heq; exact N2_ne_one (two_factor nonneg_N2 hN N2_det heq).1
    · intro _ h; rw [ht1] at h; exact absurd h (by norm_num)

theorem matWord_form : ∀ (l : List (Fin 3)), Alternating l → ∃ N δ, Good l N δ := by
  intro l
  induction l with
  | nil => intro _; exact ⟨1, 0, good_nil⟩
  | cons a rest ih =>
    intro halt
    cases rest with
    | nil =>
      have ha : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
      rcases ha with rfl | rfl | rfl
      · exact ⟨1, 1, good_zero⟩
      · exact ⟨N1, 0, good_one⟩
      · exact ⟨N2, 0, good_two⟩
    | cons b l =>
      rw [Alternating_cons_cons] at halt
      obtain ⟨hab, haltl⟩ := halt
      obtain ⟨N, δ, hgood⟩ := ih haltl
      obtain ⟨hN, hNd, hδ, hform, hcond1, hcond2⟩ := hgood
      exact good_step a b l hab haltl N δ hN hNd hδ hform hcond1 hcond2

theorem tOf_le_one (l : List (Fin 3)) : tOf l ≤ 1 := by
  cases l with
  | nil => simp [tOf]
  | cons a l => simp only [tOf_cons]; split <;> omega
theorem dOf_le_one (l : List (Fin 3)) : dOf l ≤ 1 := by
  rw [dOf]; split_ifs <;> omega

theorem smul_mul_negSm (X : Matrix (Fin 2) (Fin 2) ℤ) : X * Sm * (-Sm) = X := by
  rw [mul_assoc, show Sm * (-Sm) = (1 : Matrix (Fin 2) (Fin 2) ℤ) from by decide, mul_one]
theorem negSm_mul_smul (X : Matrix (Fin 2) (Fin 2) ℤ) : (-Sm) * (Sm * X) = X := by
  rw [← mul_assoc, show (-Sm) * Sm = (1 : Matrix (Fin 2) (Fin 2) ℤ) from by decide, one_mul]
theorem Sm_conj (X : Matrix (Fin 2) (Fin 2) ℤ) : (-Sm) * (Sm * X * Sm) * (-Sm) = X := by
  rw [← mul_assoc (-Sm) (Sm * X) Sm, ← mul_assoc (-Sm) Sm X,
    show (-Sm) * Sm = (1 : Matrix (Fin 2) (Fin 2) ℤ) from by decide, one_mul]
  rw [mul_assoc X Sm (-Sm), show Sm * (-Sm) = (1 : Matrix (Fin 2) (Fin 2) ℤ) from by decide,
    mul_one]

theorem eq_neg_Sm_of_mul_Sm_eq {X : Matrix (Fin 2) (Fin 2) ℤ} (h : X * Sm = 1) : X = -Sm := by
  have hh := congrArg (fun Y => Y * (-Sm)) h
  rw [smul_mul_negSm] at hh
  rw [show (1 : Matrix (Fin 2) (Fin 2) ℤ) * (-Sm) = -Sm from by decide] at hh
  exact hh
theorem eq_Sm_of_mul_Sm_eq_neg {X : Matrix (Fin 2) (Fin 2) ℤ} (h : X * Sm = -1) : X = Sm := by
  have hh := congrArg (fun Y => Y * (-Sm)) h
  rw [smul_mul_negSm] at hh
  rw [show (-1 : Matrix (Fin 2) (Fin 2) ℤ) * (-Sm) = Sm from by decide] at hh
  exact hh
theorem eq_neg_Sm_of_Sm_mul_eq {X : Matrix (Fin 2) (Fin 2) ℤ} (h : Sm * X = 1) : X = -Sm := by
  have hh := congrArg (fun Y => (-Sm) * Y) h
  rw [negSm_mul_smul] at hh
  rw [show (-Sm) * (1 : Matrix (Fin 2) (Fin 2) ℤ) = -Sm from by decide] at hh
  exact hh
theorem eq_Sm_of_Sm_mul_eq_neg {X : Matrix (Fin 2) (Fin 2) ℤ} (h : Sm * X = -1) : X = Sm := by
  have hh := congrArg (fun Y => (-Sm) * Y) h
  rw [negSm_mul_smul] at hh
  rw [show (-Sm) * (-1 : Matrix (Fin 2) (Fin 2) ℤ) = Sm from by decide] at hh
  exact hh
theorem eq_neg_one_of_conj {X : Matrix (Fin 2) (Fin 2) ℤ} (h : Sm * X * Sm = 1) : X = -1 := by
  have hh := congrArg (fun Y => (-Sm) * Y * (-Sm)) h
  rw [Sm_conj] at hh
  rw [show (-Sm) * (1 : Matrix (Fin 2) (Fin 2) ℤ) * (-Sm) =
    (-1 : Matrix (Fin 2) (Fin 2) ℤ) from by decide] at hh
  exact hh
theorem eq_one_of_conj {X : Matrix (Fin 2) (Fin 2) ℤ} (h : Sm * X * Sm = -1) : X = 1 := by
  have hh := congrArg (fun Y => (-Sm) * Y * (-Sm)) h
  rw [Sm_conj] at hh
  rw [show (-Sm) * (-1 : Matrix (Fin 2) (Fin 2) ℤ) * (-Sm) =
    (1 : Matrix (Fin 2) (Fin 2) ℤ) from by decide] at hh
  exact hh

theorem aux (N : Matrix (Fin 2) (Fin 2) ℤ) (hN : Nonneg N)
    (t δ : ℕ) (ht : t ≤ 1) (hδ : δ ≤ 1)
    (h1 : t = 1 → N ≠ 1) (h2 : t = 0 → δ = 0 → N ≠ 1)
    (h : Sm ^ t * N * Sm ^ δ = 1 ∨ Sm ^ t * N * Sm ^ δ = -1) : False := by
  have ht' : t = 0 ∨ t = 1 := by omega
  have hδ' : δ = 0 ∨ δ = 1 := by omega
  rcases ht' with rfl | rfl <;> rcases hδ' with rfl | rfl
  · rcases h with h | h
    · exact h2 rfl rfl (by simpa using h)
    · have hh : N = -1 := by simpa using h
      rw [hh] at hN; exact not_nonneg_neg_one hN
  · rcases h with h | h
    · have h'' : N * Sm = 1 := by simpa using h
      rw [eq_neg_Sm_of_mul_Sm_eq h''] at hN; exact not_nonneg_neg_Sm hN
    · have h'' : N * Sm = -1 := by simpa using h
      rw [eq_Sm_of_mul_Sm_eq_neg h''] at hN; exact not_nonneg_Sm hN
  · rcases h with h | h
    · have h'' : Sm * N = 1 := by simpa using h
      rw [eq_neg_Sm_of_Sm_mul_eq h''] at hN; exact not_nonneg_neg_Sm hN
    · have h'' : Sm * N = -1 := by simpa using h
      rw [eq_Sm_of_Sm_mul_eq_neg h''] at hN; exact not_nonneg_Sm hN
  · simp only [pow_one] at h
    rcases h with h | h
    · have h3 : N = -1 := eq_neg_one_of_conj h
      rw [h3] at hN; exact not_nonneg_neg_one hN
    · exact h1 rfl (eq_one_of_conj h)

theorem matWord_ne (l : List (Fin 3)) (halt : Alternating l) (hne : l ≠ []) :
    matWord l ≠ 1 ∧ matWord l ≠ -1 := by
  obtain ⟨N, δ, hN, hNd, hδ, hform, hcond1, hcond2⟩ := matWord_form l halt
  have hδ1 : δ ≤ 1 := by rw [hδ]; exact dOf_le_one l
  constructor
  · intro hone
    rcases hform with h | h
    · exact aux N hN (tOf l) δ (tOf_le_one l) hδ1 hcond1 (fun h0 => hcond2 hne h0)
        (Or.inl (by rw [h] at hone; exact hone))
    · exact aux N hN (tOf l) δ (tOf_le_one l) hδ1 hcond1 (fun h0 => hcond2 hne h0)
        (Or.inr (by rw [h] at hone; exact neg_eq_iff_eq_neg.mp hone))
  · intro hone
    rcases hform with h | h
    · exact aux N hN (tOf l) δ (tOf_le_one l) hδ1 hcond1 (fun h0 => hcond2 hne h0)
        (Or.inr (by rw [h] at hone; exact hone))
    · exact aux N hN (tOf l) δ (tOf_le_one l) hδ1 hcond1 (fun h0 => hcond2 hne h0)
        (Or.inl (by rw [h] at hone; exact neg_inj.mp hone))

theorem det_letterMat (a : Fin 3) : (letterMat a).det = 1 := by
  fin_cases a <;> decide

theorem det_matWord (l : List (Fin 3)) : (matWord l).det = 1 := by
  induction l with
  | nil => simp [matWord]
  | cons a l ih => rw [matWord_cons, Matrix.det_mul, det_letterMat, ih, one_mul]


/-!
## Part 2: the free product `ℤ/2 ∗ ℤ/3` and `PSL(2,ℤ)`
-/

abbrev C2 : Type := Multiplicative (ZMod 2)
abbrev C3 : Type := Multiplicative (ZMod 3)

/-- The family of the two cyclic groups. -/
@[reducible] def Cyc : Bool → Type
  | false => C2
  | true => C3

instance instGroupCyc (b : Bool) : Group (Cyc b) := by
  cases b
  · exact inferInstanceAs (Group C2)
  · exact inferInstanceAs (Group C3)

instance instDecEqCyc (b : Bool) : DecidableEq (Cyc b) := by
  cases b
  · exact inferInstanceAs (DecidableEq C2)
  · exact inferInstanceAs (DecidableEq C3)

instance instFintypeCyc (b : Bool) : Fintype (Cyc b) := by
  cases b
  · exact inferInstanceAs (Fintype C2)
  · exact inferInstanceAs (Fintype C3)

/-- The free product `ℤ/2 ∗ ℤ/3`, in reduced-word form. -/
abbrev FP : Type := Monoid.CoprodI Cyc

/-- `PSL(2,ℤ)`. -/
abbrev PSL2Z : Type := Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℤ

/-- The class of a matrix of determinant `1` in `PSL(2,ℤ)`. -/
noncomputable def psl : SL(2, ℤ) →* PSL2Z :=
  QuotientGroup.mk' (Subgroup.center (SL(2, ℤ)))

/-- The matrix of a letter of `Fin 3`, as an element of `SL(2,ℤ)`. -/
def letterSL (a : Fin 3) : SL(2, ℤ) :=
  if a = 0 then ModularGroup.S
  else if a = 1 then ModularGroup.S * ModularGroup.T
  else (ModularGroup.S * ModularGroup.T) * (ModularGroup.S * ModularGroup.T)

/-- A reduced list of letters, as an element of `SL(2,ℤ)`. -/
def wordSL (l : List (Fin 3)) : SL(2, ℤ) := ⟨matWord l, det_matWord l⟩

theorem wordSL_coe (l : List (Fin 3)) :
    ((wordSL l : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = matWord l := rfl

theorem letterSL_zero : letterSL 0 = ModularGroup.S := by simp [letterSL]
theorem letterSL_one : letterSL 1 = ModularGroup.S * ModularGroup.T := by simp [letterSL]
theorem letterSL_two : letterSL 2 = (ModularGroup.S * ModularGroup.T) *
    (ModularGroup.S * ModularGroup.T) := by simp [letterSL]

theorem letterSL_coe (a : Fin 3) :
    ((letterSL a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = letterMat a := by
  fin_cases a <;>
    · simp only [letterSL, letterMat, Sm, RM, Fin.isValue, ite_true, ite_false,
        Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T]
      decide

theorem neg_one_mem_center : (-1 : SL(2, ℤ)) ∈ Subgroup.center (SL(2, ℤ)) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by norm_num, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem center_eq (A : SL(2, ℤ)) (hA : A ∈ Subgroup.center (SL(2, ℤ))) : A = 1 ∨ A = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, h⟩ := hA
  have hr' : r * r = 1 := by simpa [pow_two] using hr
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hr' with rfl | rfl
  · left
    apply Subtype.ext
    rw [← h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · right
    apply Subtype.ext
    rw [← h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp


theorem psl_neg_one : psl (-1 : SL(2, ℤ)) = 1 := by
  rw [show (1 : PSL2Z) = psl 1 from (map_one psl).symm]
  exact QuotientGroup.eq.mpr (by simpa using neg_one_mem_center)

theorem psl_neg (g : SL(2, ℤ)) : psl (-g) = psl g := by
  have h : -g = (-1 : SL(2, ℤ)) * g := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [show (((-g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) =
      -(g : Matrix (Fin 2) (Fin 2) ℤ) from by simp [Matrix.SpecialLinearGroup.coe_neg]]
    rw [show (((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) = -1 from by simp]
    rw [neg_one_mul]
  rw [h, map_mul, psl_neg_one, one_mul]

theorem pslS_sq : psl (ModularGroup.S : SL(2, ℤ)) ^ 2 = 1 := by
  rw [← map_pow, pow_two, show (ModularGroup.S * ModularGroup.S : SL(2, ℤ)) = -1 from by decide,
    psl_neg_one]

theorem pslST_cube : psl ((ModularGroup.S * ModularGroup.T : SL(2, ℤ))) ^ 3 = 1 := by
  rw [← map_pow, show ((ModularGroup.S * ModularGroup.T : SL(2, ℤ))) ^ 3 = -1 from by decide,
    psl_neg_one]

/-- The cyclic-group universal property, in multiplicative form. -/
def zmodHom (n : ℕ) [NeZero n] {G : Type*} [Group G] (g : G) (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* G where
  toFun x := g ^ x.toAdd.val
  map_one' := by simp
  map_mul' x y := by
    show g ^ (x * y).toAdd.val = g ^ x.toAdd.val * g ^ y.toAdd.val
    rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hg, pow_add]

noncomputable def homC2 : C2 →* PSL2Z := zmodHom 2 (psl (ModularGroup.S : SL(2, ℤ))) pslS_sq
noncomputable def homC3 : C3 →* PSL2Z :=
  zmodHom 3 (psl (ModularGroup.S * ModularGroup.T : SL(2, ℤ))) pslST_cube

noncomputable def homOf : (b : Bool) → Cyc b →* PSL2Z
  | false => homC2
  | true => homC3

/-- The canonical map `ℤ/2 ∗ ℤ/3 → PSL(2,ℤ)`. -/
noncomputable def Psi : FP →* PSL2Z := Monoid.CoprodI.lift homOf

theorem Psi_gC2 : Psi (Monoid.CoprodI.of (i := false) (Multiplicative.ofAdd 1 : C2)) =
    psl (ModularGroup.S : SL(2, ℤ)) := by
  rw [Psi, Monoid.CoprodI.lift_of]
  show (psl (ModularGroup.S : SL(2, ℤ))) ^ (Multiplicative.ofAdd 1 : C2).toAdd.val =
    psl (ModularGroup.S : SL(2, ℤ))
  rw [show (Multiplicative.ofAdd 1 : C2).toAdd.val = 1 from rfl, pow_one]

theorem Psi_gC3 : Psi (Monoid.CoprodI.of (i := true) (Multiplicative.ofAdd 1 : C3)) =
    psl (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) := by
  rw [Psi, Monoid.CoprodI.lift_of]
  show (psl (ModularGroup.S * ModularGroup.T : SL(2, ℤ))) ^
    (Multiplicative.ofAdd 1 : C3).toAdd.val =
    psl (ModularGroup.S * ModularGroup.T : SL(2, ℤ))
  rw [show (Multiplicative.ofAdd 1 : C3).toAdd.val = 1 from rfl, pow_one]

/-- The letter of a reduced word, as an element of `Fin 3`. -/
def codeOf : (b : Bool) → Cyc b → Fin 3
  | false, _ => 0
  | true, x => if x = 1 then 0 else if x = Multiplicative.ofAdd 1 then 1 else 2

/-- The list of letters of a reduced word. -/
def wordCode (w : Monoid.CoprodI.Word Cyc) : List (Fin 3) :=
  w.toList.map fun l => codeOf l.1 l.2

theorem isR_codeOf (b : Bool) (x : Cyc b) (hx : x ≠ 1) : isR (codeOf b x) = b := by
  cases b
  · rfl
  · revert x hx
    decide

theorem letter_compat (b : Bool) (x : Cyc b) (hx : x ≠ 1) :
    psl (letterSL (codeOf b x)) = homOf b x := by
  cases b
  · -- first factor: `C2`
    have hx1 : x = Multiplicative.ofAdd 1 := by revert x hx; decide
    subst hx1
    show psl (letterSL (codeOf false (Multiplicative.ofAdd 1 : C2))) = homC2 _
    rw [show codeOf false (Multiplicative.ofAdd 1 : C2) = 0 from rfl, letterSL_zero]
    show psl (ModularGroup.S : SL(2, ℤ)) =
      (psl (ModularGroup.S : SL(2, ℤ))) ^ (Multiplicative.ofAdd 1 : C2).toAdd.val
    rw [show (Multiplicative.ofAdd 1 : C2).toAdd.val = 1 from rfl, pow_one]
  · -- second factor: `C3`
    have hx1 : x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2 := by
      revert x hx; decide
    rcases hx1 with h | h
    · subst h
      show psl (letterSL (codeOf true (Multiplicative.ofAdd 1 : C3))) = homC3 _
      rw [show codeOf true (Multiplicative.ofAdd 1 : C3) = 1 from rfl, letterSL_one]
      show psl (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) =
        (psl (ModularGroup.S * ModularGroup.T : SL(2, ℤ))) ^
          (Multiplicative.ofAdd 1 : C3).toAdd.val
      rw [show (Multiplicative.ofAdd 1 : C3).toAdd.val = 1 from rfl, pow_one]
    · subst h
      show psl (letterSL (codeOf true (Multiplicative.ofAdd 2 : C3))) = homC3 _
      rw [show codeOf true (Multiplicative.ofAdd 2 : C3) = 2 from rfl, letterSL_two]
      show psl ((ModularGroup.S * ModularGroup.T) * (ModularGroup.S * ModularGroup.T) :
          SL(2, ℤ)) =
        (psl (ModularGroup.S * ModularGroup.T : SL(2, ℤ))) ^
          (Multiplicative.ofAdd 2 : C3).toAdd.val
      rw [show (Multiplicative.ofAdd 2 : C3).toAdd.val = 2 from rfl, pow_two, map_mul]

theorem wordCode_eq_nil_iff (w : Monoid.CoprodI.Word Cyc) : wordCode w = [] ↔ w.toList = [] := by
  simp [wordCode]

theorem wordCode_cons (i : Bool) (m : Cyc i) (w : Monoid.CoprodI.Word Cyc) (h1 : w.fstIdx ≠ some i)
    (h2 : m ≠ 1) :
    wordCode (Monoid.CoprodI.Word.cons m w h1 h2) = codeOf i m :: wordCode w := by
  simp [wordCode, Monoid.CoprodI.Word.cons_toList]

theorem Alternating_wordCode (w : Monoid.CoprodI.Word Cyc) : Alternating (wordCode w) := by
  suffices h : ∀ (l : List (Σ b, Cyc b)), (∀ x ∈ l, x.2 ≠ 1) →
      List.IsChain (fun a b => a.1 ≠ b.1) l → Alternating (l.map fun x => codeOf x.1 x.2) by
    exact h w.toList w.ne_one w.chain_ne
  intro l
  induction l with
  | nil => intro _ _; trivial
  | cons a t ih =>
    intro hne hchain
    cases t with
    | nil => trivial
    | cons b t' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hab, hchain'⟩ := hchain
      have ha : a.2 ≠ 1 := hne a (by simp)
      have hb : b.2 ≠ 1 := hne b (by simp)
      have hne' : ∀ x ∈ b :: t', x.2 ≠ 1 := fun x hx => hne x (by simp [hx])
      simp only [List.map_cons, Alternating]
      constructor
      · rw [isR_codeOf a.1 a.2 ha, isR_codeOf b.1 b.2 hb]
        exact hab
      · exact ih hne' hchain'

theorem Psi_of (i : Bool) (m : Cyc i) : Psi (Monoid.CoprodI.of m) = homOf i m := by
  simp only [Psi, Monoid.CoprodI.lift_of]

theorem wordSL_cons (a : Fin 3) (l : List (Fin 3)) :
    wordSL (a :: l) = letterSL a * wordSL l := by
  apply Subtype.ext
  rw [wordSL_coe, Matrix.SpecialLinearGroup.coe_mul, wordSL_coe, letterSL_coe, matWord_cons]

theorem wordSL_nil : wordSL ([] : List (Fin 3)) = 1 := by
  apply Subtype.ext
  simp [wordSL, matWord]

theorem word_compat (w : Monoid.CoprodI.Word Cyc) :
    psl (wordSL (wordCode w)) = Psi w.prod := by
  induction w using Monoid.CoprodI.Word.consRecOn with
  | empty => simp [Monoid.CoprodI.Word.prod_empty, wordCode, wordSL_nil]
  | cons i m w h1 h2 ih =>
    rw [Monoid.CoprodI.Word.prod_cons, wordCode_cons i m w h1 h2, wordSL_cons, map_mul, map_mul,
      ih, letter_compat i m h2, Psi_of]

theorem Psi_eq_one_imp (x : FP) (hx : Psi x = 1) : x = 1 := by
  by_contra hne
  let w : Monoid.CoprodI.Word Cyc := Monoid.CoprodI.Word.equiv x
  have hwprod : w.prod = x := by
    show Monoid.CoprodI.Word.equiv.symm (Monoid.CoprodI.Word.equiv x) = x
    exact Monoid.CoprodI.Word.equiv.symm_apply_apply x
  have hwne : w ≠ Monoid.CoprodI.Word.empty := by
    intro h
    exact hne (by rw [← hwprod, h, Monoid.CoprodI.Word.prod_empty])
  have hcode : wordCode w ≠ [] := by
    intro h
    exact hwne (Monoid.CoprodI.Word.ext (by simpa [wordCode] using h))
  have hker : psl.ker = Subgroup.center (SL(2, ℤ)) := QuotientGroup.ker_mk' _
  have h2 : (wordSL (wordCode w) : SL(2, ℤ)) ∈ Subgroup.center (SL(2, ℤ)) := by
    have h3 : psl (wordSL (wordCode w)) = 1 := by rw [word_compat, hwprod, hx]
    have h4 : (wordSL (wordCode w) : SL(2, ℤ)) ∈ psl.ker := MonoidHom.mem_ker.mpr h3
    rwa [hker] at h4
  rcases center_eq _ h2 with h | h
  · have hmat : matWord (wordCode w) = 1 := by
      rw [← wordSL_coe (wordCode w), h]
      rfl
    exact (matWord_ne (wordCode w) (Alternating_wordCode w) hcode).1 hmat
  · have hmat : matWord (wordCode w) = -1 := by
      rw [← wordSL_coe (wordCode w), h]
      rfl
    exact (matWord_ne (wordCode w) (Alternating_wordCode w) hcode).2 hmat

theorem Psi_injective : Function.Injective Psi := by
  intro x y hxy
  have h : Psi (x * y⁻¹) = 1 := by rw [map_mul, hxy, map_inv, mul_inv_cancel]
  have := Psi_eq_one_imp _ h
  rwa [mul_inv_eq_one] at this

theorem psl_surjective : Function.Surjective psl := QuotientGroup.mk'_surjective _

theorem psl_closure_S_T :
    Subgroup.closure ({psl (ModularGroup.S : SL(2, ℤ)), psl (ModularGroup.T : SL(2, ℤ))} :
      Set PSL2Z) = ⊤ := by
  have h := MonoidHom.map_closure psl ({ModularGroup.S, ModularGroup.T} : Set (SL(2, ℤ)))
  rw [SpecialLinearGroup.SL2Z_generators,
    Subgroup.map_top_of_surjective psl psl_surjective] at h
  rw [h]
  congr 1
  rw [Set.image_insert_eq, Set.image_singleton]

theorem psl_T_eq : psl (ModularGroup.T : SL(2, ℤ)) =
    psl (ModularGroup.S : SL(2, ℤ)) * psl (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) := by
  have h : (ModularGroup.T : SL(2, ℤ)) =
      -((ModularGroup.S : SL(2, ℤ)) * (ModularGroup.S * ModularGroup.T)) := by decide
  calc psl (ModularGroup.T : SL(2, ℤ))
      = psl (-((ModularGroup.S : SL(2, ℤ)) * (ModularGroup.S * ModularGroup.T))) := congrArg psl h
    _ = psl ((ModularGroup.S : SL(2, ℤ)) * (ModularGroup.S * ModularGroup.T)) := psl_neg _
    _ = psl (ModularGroup.S : SL(2, ℤ)) * psl (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) :=
        map_mul psl _ _

theorem Psi_range_top : Psi.range = ⊤ := by
  rw [eq_top_iff, ← psl_closure_S_T, Subgroup.closure_le]
  intro x hx
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact ⟨Monoid.CoprodI.of (i := false) (Multiplicative.ofAdd 1 : C2), Psi_gC2⟩
  · rw [psl_T_eq]
    exact mul_mem ⟨Monoid.CoprodI.of (i := false) (Multiplicative.ofAdd 1 : C2), Psi_gC2⟩
      ⟨Monoid.CoprodI.of (i := true) (Multiplicative.ofAdd 1 : C3), Psi_gC3⟩

theorem Psi_surjective : Function.Surjective Psi := by
  intro z
  have : z ∈ Psi.range := by rw [Psi_range_top]; exact Subgroup.mem_top z
  exact this

noncomputable def PsiEquiv : FP ≃* PSL2Z :=
  MulEquiv.ofBijective Psi ⟨Psi_injective, Psi_surjective⟩


/-!
## Part 3: `Γ ≅ ℤ/2 ∗ ℤ/3 ≅ PSL(2,ℤ)`
-/

/-- The generators of `FP`. -/
noncomputable def gC2 : FP := Monoid.CoprodI.of (i := false) (Multiplicative.ofAdd 1 : C2)
noncomputable def gC3 : FP := Monoid.CoprodI.of (i := true) (Multiplicative.ofAdd 1 : C3)

theorem gC2_sq : gC2 ^ 2 = 1 := by
  have h : (Multiplicative.ofAdd 1 : C2) ^ (2 : ℕ) = 1 := by decide
  rw [gC2, ← map_pow, h, map_one]

theorem gC3_cube : gC3 ^ 3 = 1 := by
  have h : (Multiplicative.ofAdd 1 : C3) ^ (3 : ℕ) = 1 := by decide
  rw [gC3, ← map_pow, h, map_one]

theorem gC2_mul_self : gC2 * gC2 = 1 := by rw [← pow_two]; exact gC2_sq

theorem genS_mul_self : genS * genS = 1 := by rw [← pow_two]; exact genS_sq

theorem Psi_gC2' : Psi gC2 = psl (ModularGroup.S : SL(2, ℤ)) := Psi_gC2
theorem Psi_gC3' : Psi gC3 = psl (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) := Psi_gC3

/-- The image of the two generators of the presented group in `FP`. -/
noncomputable def toFreeF : Fin 2 → FP := fun i => if i = 0 then gC2 else gC2 * gC3

theorem toFreeF_zero : toFreeF (0 : Fin 2) = gC2 := by simp [toFreeF]
theorem toFreeF_one : toFreeF (1 : Fin 2) = gC2 * gC3 := by simp [toFreeF]

theorem toFree_rel (r : FreeGroup (Fin 2)) (hr : r ∈ presentedRels) :
    FreeGroup.lift toFreeF r = 1 := by
  rw [presentedRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with h | h
  · rw [h]
    show (FreeGroup.lift toFreeF) (FreeGroup.of (0 : Fin 2) ^ (2 : ℕ)) = 1
    rw [map_pow, FreeGroup.lift_apply_of, toFreeF_zero]
    exact gC2_sq
  · rw [h]
    show (FreeGroup.lift toFreeF)
      ((FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2)) ^ (3 : ℕ)) = 1
    rw [map_pow, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, toFreeF_zero, toFreeF_one]
    rw [← mul_assoc, gC2_mul_self, one_mul, gC3_cube]

/-- The isomorphism `Γ → ℤ/2 ∗ ℤ/3` on generators. -/
noncomputable def toFree : Gamma →* FP := PresentedGroup.toGroup toFree_rel

theorem toFree_genS : toFree genS = gC2 := by
  rw [toFree, PresentedGroup.toGroup.of]
  simp [toFreeF]

theorem toFree_genT : toFree genT = gC2 * gC3 := by
  rw [toFree, PresentedGroup.toGroup.of]
  simp [toFreeF]

noncomputable def ofFreeC2 : C2 →* Gamma := zmodHom 2 genS genS_sq
noncomputable def ofFreeC3 : C3 →* Gamma := zmodHom 3 (genS * genT) genS_mul_genT_cube

noncomputable def ofFreeOf : (b : Bool) → Cyc b →* Gamma
  | false => ofFreeC2
  | true => ofFreeC3

/-- The isomorphism `ℤ/2 ∗ ℤ/3 → Γ` on generators. -/
noncomputable def ofFree : FP →* Gamma := Monoid.CoprodI.lift ofFreeOf

theorem ofFree_gC2 : ofFree gC2 = genS := by
  rw [gC2, ofFree, Monoid.CoprodI.lift_of]
  show genS ^ (Multiplicative.ofAdd 1 : C2).toAdd.val = genS
  rw [show (Multiplicative.ofAdd 1 : C2).toAdd.val = 1 from rfl, pow_one]

theorem ofFree_gC3 : ofFree gC3 = genS * genT := by
  rw [gC3, ofFree, Monoid.CoprodI.lift_of]
  show (genS * genT) ^ (Multiplicative.ofAdd 1 : C3).toAdd.val = genS * genT
  rw [show (Multiplicative.ofAdd 1 : C3).toAdd.val = 1 from rfl, pow_one]

theorem ofFree_comp_toFree : ofFree.comp toFree = MonoidHom.id Gamma := by
  apply PresentedGroup.ext
  intro x
  fin_cases x
  · show ofFree (toFree (PresentedGroup.of (0 : Fin 2))) = PresentedGroup.of (0 : Fin 2)
    rw [show PresentedGroup.of (0 : Fin 2) = genS from rfl, toFree_genS, ofFree_gC2]
  · show ofFree (toFree (PresentedGroup.of (1 : Fin 2))) = PresentedGroup.of (1 : Fin 2)
    rw [show PresentedGroup.of (1 : Fin 2) = genT from rfl, toFree_genT, map_mul, ofFree_gC2,
      ofFree_gC3, ← mul_assoc, genS_mul_self, one_mul]

theorem toFree_ofFreeC2 (x : C2) : toFree (ofFreeC2 x) = gC2 ^ x.toAdd.val := by
  have : ofFreeC2 x = genS ^ x.toAdd.val := rfl
  rw [this, map_pow, toFree_genS]

theorem toFree_ofFreeC3 (x : C3) : toFree (ofFreeC3 x) = gC3 ^ x.toAdd.val := by
  have h : ofFreeC3 x = (genS * genT) ^ x.toAdd.val := rfl
  rw [h, map_pow, map_mul, toFree_genS, toFree_genT, ← mul_assoc, gC2_mul_self, one_mul]

theorem of_as_pow_C2 (x : C2) :
    Monoid.CoprodI.of (i := false) x = gC2 ^ x.toAdd.val := by
  have hx : x = (Multiplicative.ofAdd 1 : C2) ^ x.toAdd.val := by revert x; decide
  calc Monoid.CoprodI.of (i := false) x
      = Monoid.CoprodI.of (i := false) ((Multiplicative.ofAdd 1 : C2) ^ x.toAdd.val) :=
        congrArg _ hx
    _ = (Monoid.CoprodI.of (i := false) (Multiplicative.ofAdd 1 : C2)) ^ x.toAdd.val :=
        map_pow _ _ _
    _ = gC2 ^ x.toAdd.val := rfl

theorem of_as_pow_C3 (x : C3) :
    Monoid.CoprodI.of (i := true) x = gC3 ^ x.toAdd.val := by
  have hx : x = (Multiplicative.ofAdd 1 : C3) ^ x.toAdd.val := by revert x; decide
  calc Monoid.CoprodI.of (i := true) x
      = Monoid.CoprodI.of (i := true) ((Multiplicative.ofAdd 1 : C3) ^ x.toAdd.val) :=
        congrArg _ hx
    _ = (Monoid.CoprodI.of (i := true) (Multiplicative.ofAdd 1 : C3)) ^ x.toAdd.val :=
        map_pow _ _ _
    _ = gC3 ^ x.toAdd.val := rfl

theorem toFree_comp_ofFree : toFree.comp ofFree = MonoidHom.id FP := by
  apply Monoid.CoprodI.ext_hom
  intro b
  ext x
  cases b
  · show toFree (ofFree (Monoid.CoprodI.of (i := false) x)) = Monoid.CoprodI.of (i := false) x
    rw [show ofFree (Monoid.CoprodI.of (i := false) x) = ofFreeC2 x from rfl, toFree_ofFreeC2,
      of_as_pow_C2 x]
  · show toFree (ofFree (Monoid.CoprodI.of (i := true) x)) = Monoid.CoprodI.of (i := true) x
    rw [show ofFree (Monoid.CoprodI.of (i := true) x) = ofFreeC3 x from rfl, toFree_ofFreeC3,
      of_as_pow_C3 x]

/-- `Γ ≅ ℤ/2 ∗ ℤ/3`. -/
noncomputable def gammaEquivFP : Gamma ≃* FP :=
  MonoidHom.toMulEquiv toFree ofFree ofFree_comp_toFree toFree_comp_ofFree

end PresGroup

/-- **The classical presentation of `PSL(2, ℤ)`**: the abstract group
`Γ = ⟨S, T | S ^ 2 = (S * T) ^ 3 = 1⟩` (a free product `ℤ/2 * ℤ/3`) is isomorphic to
`PSL(2, ℤ) = SL(2, ℤ) / {±1}`.  This is the step that transfers the results proved for the group
algebra `ℂ[Γ]` (the six-dimensional quotient `ℂ[Γ]/I`, the representation `σ`, the functional
`φ`) to the group algebra of `PSL(2, ℤ)` used in the paper. -/
theorem presentedGroup_equiv_PSL :
    Nonempty (Gamma ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℤ) :=
  ⟨PresGroup.gammaEquivFP.trans PresGroup.PsiEquiv⟩

end Work.Modular
