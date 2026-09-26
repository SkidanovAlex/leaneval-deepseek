/-
# Polynomial growth of the powers of `σ(T)`

The matrix `σ(T) = Work.Modular.sigmaT` has spectrum `{1 (multiplicity 5), -1 (multiplicity 1)}`,
so its powers grow at most quadratically.  We make this explicit: there are integer matrices
`P₀, P₁, P₂, Q` with

  `4 · σ(T)^n = P₀ + n P₁ + (n choose 2) P₂ + (-1)^n Q`,

which gives the bound `‖σ(T)^n‖ ≤ C (1+n)^2`.  The analogous formula holds for `σ(T)⁻¹`, so the
same bound applies to negative powers.

The identities needed are the finite verifications `P_j (σ(T) - 1) = P_{j+1}`, `P₂ (σ(T) - 1) = 0`,
`Q (σ(T) + 1) = 0` and `P₀ + Q = 4`.
-/
import Mathlib
import Submission.Work.Residues.IdealImRowDiffAll

set_option maxHeartbeats 800000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-- `σ(T)` as an integer matrix. -/
def Tmat : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0; -1, 2, 0, 0, 0, 0; 2, 0, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0;
     0, 0, 0, -1, 2, 0; 0, 0, -1, 2, 0, 0]

/-- `σ(T)⁻¹` as an integer matrix. -/
def Timat : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, -1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 4, -2, -1; 0, 0, 0, 2, -1, 0;
     0, 0, 0, 1, 0, 0; 4, -2, -1, 0, 0, 0]

def P0 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![4, 0, 0, 0, 0, 0; 0, 4, 0, 0, 0, 0; 3, -1, 2, 3, -1, -2; 0, 0, 0, 4, 0, 0;
     0, 0, 0, 0, 4, 0; 3, -1, -2, 3, -1, 2]

def P1 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![(-4), 4, 0, 0, 0, 0; -4, 4, 0, 0, 0, 0; 2, 2, 0, -6, 2, 0; 0, 0, 0, -4, 4, 0;
     0, 0, 0, -4, 4, 0; -6, 2, 0, 2, 2, 0]

def P1' : Matrix (Fin 6) (Fin 6) ℤ :=
  !![4, -4, 0, 0, 0, 0; 4, -4, 0, 0, 0, 0; -6, 2, 0, 10, -6, 0; 0, 0, 0, 4, -4, 0;
     0, 0, 0, 4, -4, 0; 10, -6, 0, -6, 2, 0]

def P2 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; -4, 4, 0, 4, -4, 0; 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0; 4, -4, 0, -4, 4, 0]

def Q : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; -3, 1, 2, -3, 1, 2; 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0; -3, 1, 2, -3, 1, 2]

-- The finite verifications.

lemma P0_add_Q : P0 + Q = 4 • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

lemma P0_rel : P0 * (Tmat - 1) = P1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

lemma P1_rel : P1 * (Tmat - 1) = P2 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

lemma P2_rel : P2 * (Tmat - 1) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

lemma Q_rel : Q * (Tmat + 1) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

lemma P0_rel' : P0 * (Timat - 1) = P1' := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

lemma P1_rel' : P1' * (Timat - 1) = P2 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

lemma P2_rel' : P2 * (Timat - 1) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

lemma Q_rel' : Q * (Timat + 1) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

lemma Tmat_mul_Timat : Tmat * Timat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

end Work.Asymptotics

namespace Work.Asymptotics

/-- Matrices over `ℤ` regarded as matrices over `ℂ`. -/
def toC (M : Matrix (Fin 6) (Fin 6) ℤ) : Matrix (Fin 6) (Fin 6) ℂ := M.map (Int.castRingHom ℂ)

lemma toC_mul (A B : Matrix (Fin 6) (Fin 6) ℤ) : toC (A * B) = toC A * toC B := Matrix.map_mul

lemma toC_zero : toC (0 : Matrix (Fin 6) (Fin 6) ℤ) = 0 := by
  ext i j; simp [toC]

/-- **The power formula for `σ(T)`, over `ℤ`.** -/
theorem Tmat_pow_formula (n : ℕ) :
    (4 : ℤ) • (Tmat ^ n)
      = P0 + (n : ℤ) • P1 + ((n.choose 2 : ℕ) : ℤ) • P2 + ((-1 : ℤ) ^ n) • Q := by
  induction n with
  | zero =>
    simp only [pow_zero, one_smul, Nat.cast_zero, zero_smul, add_zero, Nat.choose_zero_right,
      pow_zero]
    have h2 : ((Nat.choose 0 2 : ℕ) : ℤ) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (by norm_num : 0 < 2)]; rfl
    rw [h2, zero_smul, add_zero]
    exact P0_add_Q.symm
  | succ n ih =>
    rw [pow_succ, ← smul_mul_assoc, ih]
    have h0 : P0 * Tmat = P0 + P1 := by
      have h := P0_rel; rw [mul_sub, mul_one] at h; rw [sub_eq_iff_eq_add] at h
      rw [add_comm]; exact h
    have h1 : P1 * Tmat = P1 + P2 := by
      have h := P1_rel; rw [mul_sub, mul_one] at h; rw [sub_eq_iff_eq_add] at h
      rw [add_comm]; exact h
    have h2 : P2 * Tmat = P2 := by
      have h := P2_rel; rw [mul_sub, mul_one, sub_eq_zero] at h; exact h
    have hq : Q * Tmat = -Q := by
      have h := Q_rel; rw [mul_add, mul_one, add_eq_zero_iff_eq_neg] at h; exact h
    rw [add_mul, add_mul, add_mul, h0, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]
    rw [h1, smul_add, h2, hq]
    rw [show ((-1 : ℤ) ^ n) • (-Q) = ((-1 : ℤ) ^ (n + 1)) • Q from by
      rw [pow_succ]; module]
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add, add_smul]
    module

/-- **The power formula for `σ(T)⁻¹`, over `ℤ`.** -/
theorem Timat_pow_formula (n : ℕ) :
    (4 : ℤ) • (Timat ^ n)
      = P0 + (n : ℤ) • P1' + ((n.choose 2 : ℕ) : ℤ) • P2 + ((-1 : ℤ) ^ n) • Q := by
  induction n with
  | zero =>
    simp only [pow_zero, one_smul, Nat.cast_zero, zero_smul, add_zero, Nat.choose_zero_right,
      pow_zero]
    have h2 : ((Nat.choose 0 2 : ℕ) : ℤ) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (by norm_num : 0 < 2)]; rfl
    rw [h2, zero_smul, add_zero]
    exact P0_add_Q.symm
  | succ n ih =>
    rw [pow_succ, ← smul_mul_assoc, ih]
    have h0 : P0 * Timat = P0 + P1' := by
      have h := P0_rel'; rw [mul_sub, mul_one] at h; rw [sub_eq_iff_eq_add] at h
      rw [add_comm]; exact h
    have h1 : P1' * Timat = P1' + P2 := by
      have h := P1_rel'; rw [mul_sub, mul_one] at h; rw [sub_eq_iff_eq_add] at h
      rw [add_comm]; exact h
    have h2 : P2 * Timat = P2 := by
      have h := P2_rel'; rw [mul_sub, mul_one, sub_eq_zero] at h; exact h
    have hq : Q * Timat = -Q := by
      have h := Q_rel'; rw [mul_add, mul_one, add_eq_zero_iff_eq_neg] at h; exact h
    rw [add_mul, add_mul, add_mul, h0, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]
    rw [h1, smul_add, h2, hq]
    rw [show ((-1 : ℤ) ^ n) • (-Q) = ((-1 : ℤ) ^ (n + 1)) • Q from by
      rw [pow_succ]; module]
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add, add_smul]
    module

/-- `σ(T)` is `Tmat` with coefficients in `ℂ`. -/
lemma toC_Tmat : toC Tmat = Work.Modular.sigmaT := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toC, Tmat, Work.Modular.sigmaT]

/-- `σ(T)⁻¹` is `Timat` with coefficients in `ℂ`. -/
lemma toC_Timat : toC Timat = Work.Modular.sigmaTinv := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toC, Timat, Work.Modular.sigmaTinv]



namespace Work.Asymptotics

