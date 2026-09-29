import Mathlib

/-!
# Auxiliary objects for `disc_zero_abs`

The energy-zero transfer matrix `S(x) = !![x, -1; 1, 0]` of the almost Mathieu cocycle,
the diagonal involution `sz = diag(1,-1)` and `K2 = !![0,-1;1,0]`, together with
`mprod`, the ordered product of `2 × 2` matrices.  These reduce the value at `0` of the
discriminant of a rational approximant to a finite product of transfer matrices.
-/

open Matrix

noncomputable section

namespace Work.TMC14Core

/-- The energy-zero transfer matrix `S(x) = !![x, -1; 1, 0]`. -/
def S2 (x : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![x, -1; 1, 0]

/-- `sz = diag(1,-1)`. -/
def sz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `K2 = !![0,-1;1,0]`. -/
def K2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

/-- The ordered product `f 0 * f 1 * ... * f (n-1)` of `2 × 2` matrices. -/
def mprod (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | n + 1 => mprod f n * f n

@[simp] theorem mprod_zero (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ) : mprod f 0 = 1 := rfl

@[simp] theorem mprod_succ (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    mprod f (n + 1) = mprod f n * f n := rfl

theorem mprod_add (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (m n : ℕ) :
    mprod f (m + n) = mprod f m * mprod (fun k => f (m + k)) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 by omega, mprod_succ, ih, mprod_succ, mul_assoc]

theorem sz_mul_sz : sz * sz = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sz, Matrix.mul_apply, Fin.sum_univ_two]

theorem sz_mul_S2 (x : ℂ) : sz * S2 x * sz = -S2 (-x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S2, sz, Matrix.mul_apply, Fin.sum_univ_two]

theorem S2_neg (x : ℂ) : S2 (-x) = -(sz * S2 x * sz) := by
  rw [sz_mul_S2]; simp

theorem S2_det (x : ℂ) : (S2 x).det = 1 := by
  simp [S2, Matrix.det_fin_two]

theorem mprod_det_eq_one (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hf : ∀ k, (f k).det = 1) (n : ℕ) :
    (mprod f n).det = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [mprod_succ, Matrix.det_mul, ih, hf, one_mul]

theorem mprod_smul (c : ℕ → ℂ) (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    mprod (fun k => c k • f k) n = (Finset.prod (Finset.range n) c) • mprod f n := by
  induction n with
  | zero => rw [mprod_zero, mprod_zero]; simp
  | succ n ih =>
    rw [mprod_succ, mprod_succ, ih, Finset.prod_range_succ, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]

theorem mprod_conj (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X * X = 1)
    (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    mprod (fun k => X * f k * X) n = X * mprod f n * X := by
  induction n with
  | zero => rw [mprod_zero, mprod_zero, mul_one, hX]
  | succ n ih =>
    rw [mprod_succ, mprod_succ, ih]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc X X (f n * X), hX, Matrix.one_mul]

theorem K2_mul_sz : K2 * sz = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [K2, sz, Matrix.mul_apply, Fin.sum_univ_two]

theorem S2_mul_K2_mul_sz (x : ℂ) : (S2 x * K2 * sz).trace = 0 := by
  rw [Matrix.mul_assoc, K2_mul_sz]
  simp [S2, Matrix.trace_fin_two]

theorem trace_conj_sz (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    (A * sz * A * sz).trace = ((A * sz).trace)^2 + 2 := by
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s, A = !![p, q; r, s] :=
    ⟨A 0 0, A 0 1, A 1 0, A 1 1, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  have hps : p * s - q * r = 1 := by
    simpa [Matrix.det_fin_two] using hA
  have h1 : (!![p, q; r, s] * sz * !![p, q; r, s] * sz).trace = p*p - q*r - r*q + s*s := by
    simp [sz, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have h2 : ((!![p, q; r, s] * sz).trace)^2 + 2 = (p - s)^2 + 2 := by
    simp [sz, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [h1, h2]
  linear_combination 2 * hps

/-- The product of `2N` transfer matrices whose arguments come in opposite pairs
`(d k, d (N+k) = -d k)` has trace `(-1)^N ((tr (A sz))^2 + 2)`, `A` being the first half. -/
theorem mprod_half_trace (N : ℕ) (d : ℕ → ℂ) (hd : ∀ k, d (N + k) = -(d k)) :
    (mprod (fun k => S2 (d k)) (2 * N)).trace
      = (-1 : ℂ)^N * (((mprod (fun k => S2 (d k)) N * sz).trace)^2 + 2) := by
  have h2 : 2 * N = N + N := by ring
  have hfun : (fun k => S2 (d (N + k))) = (fun k => (-1 : ℂ) • (sz * S2 (d k) * sz)) := by
    funext k
    rw [hd k]
    show S2 (-(d k)) = (-1 : ℂ) • (sz * S2 (d k) * sz)
    rw [S2_neg]
    show -(sz * S2 (d k) * sz) = (-1 : ℂ) • (sz * S2 (d k) * sz)
    rw [neg_one_smul]
  have hB : mprod (fun k => S2 (d (N + k))) N
      = ((-1 : ℂ)^N) • (sz * mprod (fun k => S2 (d k)) N * sz) := by
    rw [hfun, mprod_smul, mprod_conj _ sz_mul_sz, Finset.prod_const, Finset.card_range]
  have hsplit : mprod (fun k => S2 (d k)) (2 * N)
      = mprod (fun k => S2 (d k)) N * mprod (fun k => S2 (d (N + k))) N := by
    rw [h2, mprod_add]
  have hdet : (mprod (fun k => S2 (d k)) N).det = 1 :=
    mprod_det_eq_one _ (fun k => S2_det _) N
  have hassoc : mprod (fun k => S2 (d k)) N * (sz * mprod (fun k => S2 (d k)) N * sz)
      = mprod (fun k => S2 (d k)) N * sz * mprod (fun k => S2 (d k)) N * sz := by
    simp only [Matrix.mul_assoc]
  rw [hsplit, hB, Matrix.mul_smul, Matrix.trace_smul, hassoc, trace_conj_sz _ hdet]
  rw [smul_eq_mul]
end Work.TMC14Core
