import Submission.Work.TMC7Core.Defs

/-!
# TMC7Core: the transfer cocycle of the almost Mathieu operator

Basic API for `frob`, `tmC`, `iterC` used by the Bourgain--Jitomirskaya component.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core

/-! ## The Frobenius norm -/

theorem frob_nonneg (A : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ frob A := Real.sqrt_nonneg _

theorem frob_sq (A : Matrix (Fin 2) (Fin 2) ℂ) :
    frob A ^ 2 = ‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2 := by
  rw [frob, Real.sq_sqrt (by positivity)]

theorem frob_entry (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : ‖A i j‖ ≤ frob A := by
  have hf := frob_nonneg A
  have hsum : frob A ^ 2 = ∑ i : Fin 2, ∑ j : Fin 2, ‖A i j‖ ^ 2 := by
    rw [frob_sq, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    ring
  have hle : ‖A i j‖ ^ 2 ≤ frob A ^ 2 := by
    rw [hsum]
    calc ‖A i j‖ ^ 2 ≤ ∑ j' : Fin 2, ‖A i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2) (fun j' _ => sq_nonneg _)
            (Finset.mem_univ j)
      _ ≤ ∑ i' : Fin 2, ∑ j' : Fin 2, ‖A i' j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j' : Fin 2, ‖A i' j'‖ ^ 2)
            (fun i' _ => Finset.sum_nonneg (fun j' _ => sq_nonneg _)) (Finset.mem_univ i)
  calc ‖A i j‖ = Real.sqrt (‖A i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (frob A ^ 2) := Real.sqrt_le_sqrt hle
    _ = frob A := Real.sqrt_sq hf

theorem frob_one : frob (1 : Matrix (Fin 2) (Fin 2) ℂ) = Real.sqrt 2 := by
  rw [frob]
  norm_num [Matrix.one_apply, Fin.forall_fin_two]

/-! ## Periodicity of the transfer matrices -/

theorem cos_two_pi_add_one (y : ℝ) :
    Real.cos (2 * Real.pi * (y + 1)) = Real.cos (2 * Real.pi * y) := by
  have h : 2 * Real.pi * (y + 1) = 2 * Real.pi * y + 2 * Real.pi := by ring
  rw [h, Real.cos_add_two_pi]

theorem tmC_add_one (lam : ℝ) (E : ℂ) (x : ℝ) : tmC lam E (x + 1) = tmC lam E x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tmC, cos_two_pi_add_one]

/-! ## Determinants -/

theorem det_tmC (lam : ℝ) (E : ℂ) (x : ℝ) : (tmC lam E x).det = 1 := by
  simp [tmC, Matrix.det_fin_two]

theorem det_iterC (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) : (iterC α lam E n x).det = 1 := by
  induction n with
  | zero => simp [iterC]
  | succ n ih => simp [iterC, Matrix.det_mul, det_tmC, ih]

/-! ## The cocycle identity -/

theorem iterC_zero (α lam : ℝ) (E : ℂ) (x : ℝ) : iterC α lam E 0 x = 1 := rfl

theorem iterC_succ (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    iterC α lam E (n + 1) x = tmC lam E (x + (n : ℝ) * α) * iterC α lam E n x := rfl

theorem iterC_add (α lam : ℝ) (E : ℂ) (m n : ℕ) (x : ℝ) :
    iterC α lam E (m + n) x = iterC α lam E m (x + (n : ℝ) * α) * iterC α lam E n x := by
  induction m with
  | zero => simp [iterC_zero]
  | succ m ih =>
    have hy : x + (((m + n : ℕ)) : ℝ) * α = x + (n : ℝ) * α + (m : ℝ) * α := by
      push_cast; ring
    rw [Nat.succ_add, iterC_succ, ih, iterC_succ, hy, mul_assoc]

theorem iterC_periodic (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    iterC α lam E n (x + 1) = iterC α lam E n x := by
  induction n with
  | zero => simp [iterC_zero]
  | succ n ih =>
    rw [iterC_succ, iterC_succ, ih]
    have hy : (x + 1) + (n : ℝ) * α = x + (n : ℝ) * α + 1 := by ring
    rw [hy, tmC_add_one]

/-! ## Continuity -/

theorem continuous_tmC (lam : ℝ) (E : ℂ) : Continuous (fun x : ℝ => tmC lam E x) := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [tmC] <;> fun_prop

theorem continuous_iterC (α lam : ℝ) (E : ℂ) (n : ℕ) :
    Continuous (fun x : ℝ => iterC α lam E n x) := by
  induction n with
  | zero => simpa [iterC_zero] using continuous_const
  | succ n ih =>
    have h : (fun x : ℝ => iterC α lam E (n + 1) x)
        = fun x : ℝ => tmC lam E (x + (n : ℝ) * α) * iterC α lam E n x := rfl
    rw [h]
    exact ((continuous_tmC lam E).comp (by fun_prop)).mul ih

theorem continuous_iterC_energy (α lam : ℝ) (n : ℕ) (x : ℝ) :
    Continuous (fun E : ℂ => iterC α lam E n x) := by
  induction n with
  | zero => simpa [iterC_zero] using continuous_const
  | succ n ih =>
    have h : (fun E : ℂ => iterC α lam E (n + 1) x)
        = fun E : ℂ => tmC lam E (x + (n : ℝ) * α) * iterC α lam E n x := rfl
    rw [h]
    refine ((continuous_matrix ?_).mul ih)
    intro i j
    fin_cases i <;> fin_cases j <;> simp [tmC] <;> fun_prop

/-! ## Ordered products of matrices

`matProd A n = A (n-1) * ⋯ * A 1 * A 0`, the same convention as `iterC`. -/

def matProd (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | n + 1 => A n * matProd A n

theorem matProd_zero (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) : matProd A 0 = 1 := rfl

theorem matProd_succ (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    matProd A (n + 1) = A n * matProd A n := rfl

theorem matProd_add (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (m n : ℕ) :
    matProd A (m + n) = matProd (fun j => A (m + j)) n * matProd A m := by
  induction n with
  | zero => rw [Nat.add_zero, matProd_zero, one_mul]
  | succ n ih =>
    rw [Nat.add_succ, matProd_succ, ih, matProd_succ, mul_assoc]

theorem iterC_eq_matProd (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    iterC α lam E n x = matProd (fun j => tmC lam E (x + (j : ℝ) * α)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterC_succ, ih, matProd_succ]

theorem det_matProd (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hA : ∀ j, (A j).det = 1) (n : ℕ) :
    (matProd A n).det = 1 := by
  induction n with
  | zero => simp [matProd_zero]
  | succ n ih => rw [matProd_succ, Matrix.det_mul, hA n, ih, one_mul]

/-! ## The squared Frobenius norm of an iterate -/

/-- `frobSq α lam E n x = ‖A_n(x)‖_F²`.  For real energy this is a real trigonometric
polynomial of degree `≤ 2n`. -/
def frobSq (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) : ℝ := frob (iterC α lam E n x) ^ 2

theorem frobSq_nonneg (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) : 0 ≤ frobSq α lam E n x :=
  sq_nonneg _

theorem frobSq_eq (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    frobSq α lam E n x = ‖iterC α lam E n x 0 0‖ ^ 2 + ‖iterC α lam E n x 0 1‖ ^ 2
      + ‖iterC α lam E n x 1 0‖ ^ 2 + ‖iterC α lam E n x 1 1‖ ^ 2 := by
  rw [frobSq, frob_sq]

/-! ## Finite-scale Lyapunov averages -/

/-- The `N`-th finite-scale Lyapunov average `L_N = (1/N)∫₀¹ ln‖A_N(x)‖_F dx` (junk value `0`
at `N = 0`; only `N ≥ 1` is used).  `lyap` is the infimum of `lyapAvg · (N+1)`. -/
def lyapAvg (α lam : ℝ) (E : ℂ) (N : ℕ) : ℝ :=
  (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E N x))) / (N : ℝ)

/-- The pointwise finite-scale exponent `u_N(x) = (1/N) ln‖A_N(x)‖_F` (junk value `0` at
`N = 0`). -/
def uAvg (α lam : ℝ) (E : ℂ) (N : ℕ) (x : ℝ) : ℝ :=
  Real.log (frob (iterC α lam E N x)) / (N : ℝ)

theorem lyap_eq_iInf_lyapAvg (α lam : ℝ) (E : ℂ) :
    lyap α lam E = ⨅ N : ℕ, lyapAvg α lam E (N + 1) := by
  simp only [lyap, lyapAvg, Nat.cast_add, Nat.cast_one]

theorem lyapAvg_eq_integral_uAvg (α lam : ℝ) (E : ℂ) (N : ℕ) :
    lyapAvg α lam E N = ∫ x in (0 : ℝ)..1, uAvg α lam E N x := by
  simp only [lyapAvg, uAvg, intervalIntegral.integral_div]

end Work.TMC7Core
