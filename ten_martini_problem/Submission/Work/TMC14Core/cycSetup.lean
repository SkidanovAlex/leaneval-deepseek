/-
# TMC14Core: the cyclic (Bloch) matrix, the transfer product, and the shooting matrix

Definitions used to prove `Work.TMC14Core.blochDet`
`det (z - blochMat p q lam θ k) = trAq p q lam z θ - 2 cos (2 π k)`.

The proof goes through a *general* statement about arbitrary diagonals `d : ℕ → ℂ`
and twist `t : ℂ`:

* `cycMat q d t`       : the `q × q` "cyclic" (tridiagonal with two corners) matrix with
                         diagonal `d`, off-diagonal `-1` and corners `-t` (bottom-left) and
                         `-t⁻¹` (top-right).
* `transProd d q`      : the product `tm2 (d (q-1)) ⋯ tm2 (d 0)` of the `2 × 2` transfer
                         matrices `tm2 a = !![a, -1; 1, 0]`.
* `smMat q d t`        : the `(q+2) × (q+2)` "shooting" matrix whose rows are the two
                         boundary conditions and the `q` recurrence residuals.

The two key facts (proved in the sibling files `cycSmDet` and `cycSmTrace`) are

* `det (smMat q d t) = det (cycMat q d t)`                       (Schur complement),
* `det (smMat q d t) = (transProd d q).trace - (t + t⁻¹)`        (change of variables).

Combining them gives `det (cycMat q d t) = (transProd d q).trace - (t + t⁻¹)`, and
specialising `d i = z - 2λ cos 2π(θ + i p/q)`, `t = e^{2πik}` yields the target.
-/
import Mathlib
import Submission.Work.TMC14Core.Rat

open LeanEval.Analysis.TenMartini
noncomputable section

namespace Work.TMC14Core

/-- The `2 × 2` transfer matrix `!![a, -1; 1, 0]` (unimodular). -/
def tm2 (a : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, -1; 1, 0]

/-- `transProd d n = tm2 (d (n-1)) * ⋯ * tm2 (d 0)`. -/
def transProd (d : ℕ → ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | (n+1) => tm2 (d n) * transProd d n

@[simp] theorem transProd_zero (d : ℕ → ℂ) : transProd d 0 = 1 := rfl

theorem transProd_succ (d : ℕ → ℂ) (n : ℕ) :
    transProd d (n+1) = tm2 (d n) * transProd d n := rfl

/-- The `q × q` cyclic matrix: diagonal `d`, off-diagonal `-1`, bottom-left corner `-t`,
top-right corner `-t⁻¹`.  (For `q = 1` the two corner conditions coincide, so the single
entry is `d 0 - t - t⁻¹`.) -/
def cycMat (q : ℕ) (d : ℕ → ℂ) (t : ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  Matrix.of fun i j =>
      (if i = j then d i.val else 0)
    + (if i.val + 1 = j.val then (-1:ℂ) else 0)
    + (if j.val + 1 = i.val then (-1:ℂ) else 0)
    + (if i.val = q - 1 ∧ j.val = 0 then -t else 0)
    + (if i.val = 0 ∧ j.val = q - 1 then -t⁻¹ else 0)

/-- The shooting matrix of the periodic problem.  Columns are indexed by
`u_{-1}, u_0, …, u_{q-1}, u_q` (column `k` is `u_{k-1}`); rows are
`Bd1 = u_{-1} - t⁻¹ u_{q-1}`, `Bd2 = u_q - t u_0`, then the recurrence residuals
`Rec_i = u_{i-1} - d_i u_i + u_{i+1}`. -/
def smMat (q : ℕ) (d : ℕ → ℂ) (t : ℂ) : Matrix (Fin (q+2)) (Fin (q+2)) ℂ :=
  Matrix.of fun i j =>
      (if i.val = 0 ∧ j.val = 0 then (1:ℂ) else 0)
    + (if i.val = 0 ∧ j.val = q then -t⁻¹ else 0)
    + (if i.val = 1 ∧ j.val = 1 then -t else 0)
    + (if i.val = 1 ∧ j.val = q+1 then (1:ℂ) else 0)
    + (if 2 ≤ i.val ∧ j.val + 2 = i.val then (1:ℂ) else 0)
    + (if 2 ≤ i.val ∧ j.val + 1 = i.val then -(d (i.val - 2)) else 0)
    + (if 2 ≤ i.val ∧ j.val = i.val then (1:ℂ) else 0)

/-- `β = e^{2πik}`, the corner phase. -/
def wBeta (k : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (k : ℂ))

/-- The diagonal `d i = z - 2λ cos 2π(θ + i p/q)`. -/
def dOf (p : ℤ) (q : ℕ) (lam θ : ℝ) (z : ℂ) : ℕ → ℂ :=
  fun i => z - (((2 * lam * Real.cos (2 * Real.pi * (θ + (i : ℝ) * (p : ℝ) / (q : ℝ)))) : ℝ) : ℂ)

/-- The Bloch matrix is the cyclic matrix with diagonal `d i = z - 2λ cos 2π(θ + i p/q)`
and twist `t = e^{2πik}`. -/
theorem cycMat_bloch (p : ℤ) (q : ℕ) (lam θ k : ℝ) (z : ℂ) :
    z • (1 : Matrix (Fin q) (Fin q) ℂ) - blochMat p q lam θ k
      = cycMat q (dOf p q lam θ z) (wBeta k) := by
  ext i j
  simp only [cycMat, Matrix.of_apply, dOf, wBeta, blochMat, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, Complex.exp_neg, smul_ite, smul_zero, smul_one]
  split_ifs <;> ring

/-- `iterC α lam z n θ` is the transfer product with diagonal `z - 2λ cos 2π(θ + i α)`. -/
theorem iterC_eq_transProd (α lam θ : ℝ) (z : ℂ) (n : ℕ) :
    iterC α lam z n θ
      = transProd (fun i => z - (((2*lam*Real.cos (2*Real.pi*(θ + (i:ℝ)*α))) : ℝ) : ℂ)) n := by
  induction n with
  | zero => simp [iterC, transProd]
  | succ k ih =>
    rw [iterC_succ, ih, transProd]
    rfl

/-- `t + t⁻¹ = 2 cos (2 π k)` for `t = e^{2πik}`. -/
theorem wBeta_add_inv (k : ℝ) :
    wBeta k + (wBeta k)⁻¹ = ((2 * Real.cos (2 * Real.pi * k) : ℝ) : ℂ) := by
  simp only [wBeta]
  have h1 : 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)
      = ((2 * Real.pi * k : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hinv : (Complex.exp (2 * ↑Real.pi * Complex.I * ↑k))⁻¹
      = Complex.exp (-(((2 * Real.pi * k : ℝ) : ℂ) * Complex.I)) := by
    rw [← h1]; exact (Complex.exp_neg _).symm
  rw [hinv, h1]
  have key : ∀ x : ℝ, Complex.exp ((x:ℂ)*Complex.I) + Complex.exp (-((x:ℂ)*Complex.I))
      = ((2 * Real.cos x : ℝ) : ℂ) := by
    intro x
    rw [Complex.exp_ofReal_mul_I x]
    have h2 : Complex.exp (-((x:ℂ)*Complex.I)) = Complex.exp (((-x : ℝ):ℂ)*Complex.I) := by
      congr 1; push_cast; ring
    rw [h2, Complex.exp_ofReal_mul_I (-x)]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    push_cast; ring
  exact key (2 * Real.pi * k)

end Work.TMC14Core
